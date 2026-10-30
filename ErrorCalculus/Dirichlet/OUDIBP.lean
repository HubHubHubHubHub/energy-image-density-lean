import ErrorCalculus.Dirichlet.DivergenceOU
import Foundations.HermiteD.Basis
import Mathlib.Algebra.MvPolynomial.PDeriv

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace

namespace ErrorCalculus
variable {d : ℕ}

/-- The explicit density and the Gaussian product are the same measure. -/
theorem ouDensityD_eq_gaussianPi (d : ℕ) :
    densityMeasureD (ouDensityD d) = Foundations.gaussianPi d := ouDensityD_measure d

/-- Canonical isometry associated with equality of measures. -/
def lpEquivOfMeasureEq {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    (h : μ = ν) : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν := by
  subst ν
  exact LinearIsometryEquiv.refl ℝ _

theorem lpEquivOfMeasureEq_toLp {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    (h : μ = ν) {f : Ω → ℝ} (hf : MemLp f 2 μ) (hf' : MemLp f 2 ν) :
    lpEquivOfMeasureEq h (hf.toLp f) = hf'.toLp f := by
  subst ν
  rfl

/-- Change of measure retaining the original closed form's type. -/
def ouGaussianEquivD (d : ℕ) :
    Lp ℝ 2 (densityMeasureD (ouDensityD d)) ≃ₗᵢ[ℝ] Lp ℝ 2 (Foundations.gaussianPi d) :=
  lpEquivOfMeasureEq (ouDensityD_eq_gaussianPi d)

theorem contDiff_mvPolynomialD (p : MvPolynomial (Fin d) ℝ) :
    ContDiff ℝ 1 (fun x => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : Fin d → ℝ => c))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul, MvPolynomial.eval_X] using hp.mul (contDiff_apply ℝ ℝ i)

theorem partial_mvPolynomialD (p : MvPolynomial (Fin d) ℝ) (i : Fin d) (x : Fin d → ℝ) :
    fderiv ℝ (fun y => MvPolynomial.eval y p) x (Pi.single i 1) =
      MvPolynomial.eval x (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    simp only [map_add]
    rw [fderiv_fun_add ((contDiff_mvPolynomialD p).differentiable (by norm_num) x)
      ((contDiff_mvPolynomialD q).differentiable (by norm_num) x)]
    simp only [add_apply, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X, map_add]
    rw [fderiv_fun_mul ((contDiff_mvPolynomialD p).differentiable (by norm_num) x)
      (differentiableAt_apply j x)]
    rw [(hasFDerivAt_apply j x).fderiv]
    simp [hp, Pi.single_apply, eq_comm, mul_comm, add_comm]

theorem ouD_memLp_mvPolynomial (p : MvPolynomial (Fin d) ℝ) :
    MemLp (fun x => MvPolynomial.eval x p) 2 (densityMeasureD (ouDensityD d)) := by
  rw [ouDensityD_eq_gaussianPi]
  exact Foundations.memLp_mvPolynomial_gaussianProduct p

def ouDMvPolynomialLp (p : MvPolynomial (Fin d) ℝ) :
    Lp ℝ 2 (densityMeasureD (ouDensityD d)) := (ouD_memLp_mvPolynomial p).toLp _

theorem coe_ouDMvPolynomialLp (p : MvPolynomial (Fin d) ℝ) :
    ouDMvPolynomialLp p =ᵐ[densityMeasureD (ouDensityD d)] fun x => MvPolynomial.eval x p :=
  (ouD_memLp_mvPolynomial p).coeFn_toLp

@[simp] theorem ouGaussianEquivD_polynomial (p : MvPolynomial (Fin d) ℝ) :
    ouGaussianEquivD d (ouDMvPolynomialLp p) = Foundations.mvPolynomialLp p :=
  lpEquivOfMeasureEq_toLp _ _ _

/-- Gaussian integration by parts with an arbitrary multivariate polynomial. -/
theorem integral_partial_mul_ouD_mvPolynomial_of_memLp (i : Fin d) {f : (Fin d → ℝ) → ℝ}
    (hf : Differentiable ℝ f)
    (hm : MemLp f 2 (densityMeasureD (ouDensityD d)))
    (hpartial : MemLp (fun x => fderiv ℝ f x (Pi.single i 1)) 2
      (densityMeasureD (ouDensityD d))) (p : MvPolynomial (Fin d) ℝ) :
    (∫ x, fderiv ℝ f x (Pi.single i 1) * MvPolynomial.eval x p
      ∂densityMeasureD (ouDensityD d)) =
    ∫ x, f x * MvPolynomial.eval x (MvPolynomial.X i * p - MvPolynomial.pderiv i p)
      ∂densityMeasureD (ouDensityD d) := by
  let g := fun x => MvPolynomial.eval x p
  let q := MvPolynomial.X i * p - MvPolynomial.pderiv i p
  have hg : Differentiable ℝ g := (contDiff_mvPolynomialD p).differentiable (by norm_num)
  have hd (x : Fin d → ℝ) :
      fderiv ℝ (g * ouDensityD d) x (Pi.single i 1) =
        -(ouDensityD d x * MvPolynomial.eval x q) := by
    rw [fderiv_mul (hg x)
      ((SmoothDensityD.contDiff (ρ := ouDensityD d)).differentiable (by norm_num) x)]
    simp only [add_apply, smul_apply,
      smul_eq_mul, partial_ouDensityD, g, partial_mvPolynomialD, q, map_sub, map_mul,
      MvPolynomial.eval_X]
    ring
  have h1 := integrable_ou_weightD (hm.integrable_mul (ouD_memLp_mvPolynomial q))
  have h2 := integrable_ou_weightD (hpartial.integrable_mul (ouD_memLp_mvPolynomial p))
  have h3 := integrable_ou_weightD (hm.integrable_mul (ouD_memLp_mvPolynomial p))
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := g * ouDensityD d) (g := f) (v := Pi.single i 1)
    (by convert h1.neg using 1; funext x; rw [hd]; simp only [Pi.neg_apply, Pi.mul_apply]; ring)
    (by convert h2 using 1; funext x; simp only [Pi.mul_apply, g]; ring)
    (by convert h3 using 1; funext x; simp only [Pi.mul_apply, g]; ring)
    (fun x _ => (hg x).mul
      ((SmoothDensityD.contDiff (ρ := ouDensityD d)).differentiable (by norm_num) x))
    (fun x _ => hf x)
  rw [integral_densityD, integral_densityD]
  convert hi using 1
  · congr 1; funext x; simp only [Pi.mul_apply, g]; ring
  · rw [← integral_neg]
    congr 1; funext x; rw [hd]; ring

/-- Gaussian integration by parts with an arbitrary multivariate polynomial. -/
theorem integral_partial_mul_ouD_mvPolynomial (i : Fin d) {f : (Fin d → ℝ) → ℝ}
    (hf : IsC1BoundedD f) (p : MvPolynomial (Fin d) ℝ) :
    (∫ x, fderiv ℝ f x (Pi.single i 1) * MvPolynomial.eval x p
      ∂densityMeasureD (ouDensityD d)) =
    ∫ x, f x * MvPolynomial.eval x (MvPolynomial.X i * p - MvPolynomial.pderiv i p)
      ∂densityMeasureD (ouDensityD d) :=
  integral_partial_mul_ouD_mvPolynomial_of_memLp i hf.differentiable
    (hf.memLp _ 2) (hf.partial_memLp i _ 2) p

/-- The polynomial adjoint identity extends to the entire closed domain. -/
theorem inner_gradientD_mvPolynomial (i : Fin d) (v : (ouStructureD d).dom)
    (p : MvPolynomial (Fin d) ℝ) :
    ⟪gradientD (ouDensityD d) i v, ouDMvPolynomialLp p⟫_ℝ =
      ⟪(v : Lp ℝ 2 (densityMeasureD (ouDensityD d))),
        ouDMvPolynomialLp (MvPolynomial.X i * p - MvPolynomial.pderiv i p)⟫_ℝ := by
  have he (u : protoDomD (ouDensityD d)) :
      ⟪gradD (ouDensityD d) i u, ouDMvPolynomialLp p⟫_ℝ =
      ⟪(u : Lp ℝ 2 (densityMeasureD (ouDensityD d))),
        ouDMvPolynomialLp (MvPolynomial.X i * p - MvPolynomial.pderiv i p)⟫_ℝ := by
    simp only [L2.inner_def]
    calc
      _ = ∫ x, fderiv ℝ (repD (ouDensityD d) u) x (Pi.single i 1) * MvPolynomial.eval x p
          ∂densityMeasureD (ouDensityD d) := by
        apply integral_congr_ae
        filter_upwards [coeFn_gradD (ouDensityD d) i u, coe_ouDMvPolynomialLp p] with x hu hp
        rw [hu, hp, real_inner_comm]; rfl
      _ = _ := integral_partial_mul_ouD_mvPolynomial i (rep_isC1BoundedD _ u) p
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [coeFn_repD (ouDensityD d) u,
          coe_ouDMvPolynomialLp (MvPolynomial.X i * p - MvPolynomial.pderiv i p)] with x hu hp
        rw [hu, hp, real_inner_comm]; rfl
  obtain ⟨s, hs, hG⟩ := gradientD_spec (ouDensityD d) i v
  exact tendsto_nhds_unique (hG.inner (𝕜 := ℝ) tendsto_const_nhds)
    ((hs.2.inner (𝕜 := ℝ) tendsto_const_nhds).congr (fun n => (he (s n)).symm))

end ErrorCalculus
