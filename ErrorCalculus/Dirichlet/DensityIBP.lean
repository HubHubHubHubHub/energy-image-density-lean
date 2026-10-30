import ErrorCalculus.Dirichlet.DensityGamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus
variable {ρ g φ : ℝ → ℝ}

/-- X.2, slightly stronger: neither g nor g' needs to be bounded here. -/
theorem integral_deriv_mul_test (hg : ContDiff ℝ 1 g) (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (hρ : ContDiff ℝ 1 ρ) :
    (∫ x, deriv g x * φ x * ρ x) = -(∫ x, g x * deriv (φ * ρ) x) := by
  have hψ := hφ.mul hρ
  have hcψ : HasCompactSupport (φ * ρ) := hc.mul_right
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (v := φ * ρ) (u' := deriv g) (v' := deriv (φ * ρ))
    (fun x _ => (hg.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hψ.differentiable (by norm_num) x).hasDerivAt)
    ((hg.continuous.mul (hψ.continuous_deriv (by norm_num))).integrable_of_hasCompactSupport hcψ.deriv.mul_left)
    (((hg.continuous_deriv (by norm_num)).mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left)
    ((hg.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left)
  have he : (fun x => deriv g x * φ x * ρ x) = fun x => deriv g x * (φ * ρ) x := by
    funext x; simp only [Pi.mul_apply]; ring
  rw [he, hi, neg_neg]

variable (ρ) [SmoothDensity ρ]

/-- The adjoint test expression, initially defined as a quotient. -/
def testChi (φ : ℝ → ℝ) (x : ℝ) : ℝ := deriv (φ * ρ) x / ρ x

theorem testChi_eq (hφ : ContDiff ℝ 1 φ) (x : ℝ) :
    testChi ρ φ x = deriv φ x + φ x * deriv ρ x / ρ x := by
  unfold testChi
  rw [deriv_mul (hφ.differentiable (by norm_num) x)
    ((SmoothDensity.contDiff (ρ := ρ)).differentiable (by norm_num) x)]
  field_simp [(SmoothDensity.pos (ρ := ρ) x).ne']

theorem continuous_testChi (hφ : ContDiff ℝ 1 φ) : Continuous (testChi ρ φ) :=
  ((hφ.mul SmoothDensity.contDiff).continuous_deriv (by norm_num)).div
    (SmoothDensity.contDiff (ρ := ρ)).continuous (fun x => (SmoothDensity.pos x).ne')

omit [SmoothDensity ρ] in
theorem hasCompactSupport_testChi (hc : HasCompactSupport φ) : HasCompactSupport (testChi ρ φ) :=
  by
    change HasCompactSupport (fun x => deriv (φ * ρ) x / ρ x)
    simpa only [div_eq_mul_inv, Pi.mul_def] using
      ((hc.mul_right (f' := ρ)).deriv.mul_right (f' := fun x => (ρ x)⁻¹))

/-- Conversion to the weighted Lebesgue integral, without integrability side conditions. -/
theorem integral_density (f : ℝ → ℝ) :
    (∫ x, f x ∂densityMeasure ρ) = ∫ x, ρ x * f x := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul
    (SmoothDensity.contDiff (ρ := ρ)).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (SmoothDensity.pos _).le, smul_eq_mul]

variable [IsProbabilityMeasure (densityMeasure ρ)]

/-- The compactly supported adjoint expression belongs to L². -/
def testChiLp (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Lp ℝ 2 (densityMeasure ρ) :=
  ((continuous_testChi ρ hφ).memLp_of_hasCompactSupport (hasCompactSupport_testChi ρ hc)).toLp _

/--
Integration by parts identifies the gradient pairing with a compactly supported C¹ test as the
negative pairing with its weighted derivative `testChiLp`.
-/
theorem inner_grad_test (u : protoDom ρ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    inner ℝ (grad ρ u) (protoOfFunction ρ φ (isC1Bounded_of_hasCompactSupport hφ hc) : Lp ℝ 2 (densityMeasure ρ)) =
      - inner ℝ (u : Lp ℝ 2 (densityMeasure ρ)) (testChiLp ρ φ hφ hc) := by
  have hl : inner ℝ (grad ρ u)
      (protoOfFunction ρ φ (isC1Bounded_of_hasCompactSupport hφ hc) : Lp ℝ 2 (densityMeasure ρ)) =
      ∫ x, deriv (rep ρ u) x * φ x ∂densityMeasure ρ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_grad ρ u,
      MemLp.coeFn_toLp ((isC1Bounded_of_hasCompactSupport hφ hc).memLp (densityMeasure ρ) 2)] with x hu hx
    dsimp only [protoOfFunction]
    rw [hu, hx, real_inner_comm]
    rfl
  have hr : inner ℝ (u : Lp ℝ 2 (densityMeasure ρ)) (testChiLp ρ φ hφ hc) =
      ∫ x, rep ρ u x * testChi ρ φ x ∂densityMeasure ρ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_rep ρ u, MemLp.coeFn_toLp
      ((continuous_testChi ρ hφ).memLp_of_hasCompactSupport (μ := densityMeasure ρ) (p := 2)
        (hasCompactSupport_testChi ρ hc))] with x hu hx
    dsimp only [testChiLp]
    rw [hu, hx, real_inner_comm]
    rfl
  rw [hl, hr, integral_density, integral_density]
  convert integral_deriv_mul_test (rep_isC1Bounded ρ u).1 hφ hc (SmoothDensity.contDiff (ρ := ρ)) using 1
  · congr 1; funext x; ring
  · congr 1; congr 1; funext x
    dsimp [testChi]
    field_simp [(SmoothDensity.pos (ρ := ρ) x).ne']

end ErrorCalculus
