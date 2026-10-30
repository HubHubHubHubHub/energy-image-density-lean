import ErrorCalculus.Dirichlet.DensityDGamma
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus
variable {d : ℕ}
variable {ρ g φ : (Fin d → ℝ) → ℝ}

/-- integration by parts in one coordinate, without boundedness of g. -/
theorem integral_fderiv_mul_test (i : Fin d) (hg : ContDiff ℝ 1 g) (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (hρ : ContDiff ℝ 1 ρ) :
    (∫ x, fderiv ℝ g x (Pi.single i 1) * φ x * ρ x) =
      -(∫ x, g x * fderiv ℝ (φ * ρ) x (Pi.single i 1)) := by
  have hψ := hφ.mul hρ
  have hcψ : HasCompactSupport (φ * ρ) := hc.mul_right
  have hdψ := (hψ.continuous_fderiv (by norm_num)).clm_apply
    (continuous_const (y := Pi.single i (1:ℝ)))
  have hdg := (hg.continuous_fderiv (by norm_num)).clm_apply
    (continuous_const (y := Pi.single i (1:ℝ)))
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := φ * ρ) (g := g) (v := Pi.single i 1)
    ((hdψ.mul hg.continuous).integrable_of_hasCompactSupport
      ((hcψ.fderiv_apply ℝ (Pi.single i 1)).mul_right))
    ((hψ.continuous.mul hdg).integrable_of_hasCompactSupport hcψ.mul_right)
    ((hψ.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcψ.mul_right)
    (fun x _ => hψ.differentiable (by norm_num) x)
    (fun x _ => hg.differentiable (by norm_num) x)
  convert hi using 1 <;> congr 1
  · funext x; simp only [Pi.mul_apply]; ring
  · congr 1; funext x; ring

variable (ρ) [SmoothDensityD ρ]

/-- The adjoint test expression, initially defined as a quotient. -/
def testChiD (i : Fin d) (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ := fderiv ℝ (φ * ρ) x (Pi.single i 1) / ρ x

theorem testChi_eqD (i : Fin d) (hφ : ContDiff ℝ 1 φ) (x : Fin d → ℝ) :
    testChiD ρ i φ x = fderiv ℝ φ x (Pi.single i 1) + φ x * fderiv ℝ ρ x (Pi.single i 1) / ρ x := by
  unfold testChiD
  rw [fderiv_mul (hφ.differentiable (by norm_num) x)
    ((SmoothDensityD.contDiff (ρ := ρ)).differentiable (by norm_num) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  field_simp [(SmoothDensityD.pos (ρ := ρ) x).ne']
  ring

theorem continuous_testChiD (i : Fin d) (hφ : ContDiff ℝ 1 φ) : Continuous (testChiD ρ i φ) :=
  (((hφ.mul SmoothDensityD.contDiff).continuous_fderiv (by norm_num)).clm_apply continuous_const).div
    (SmoothDensityD.contDiff (ρ := ρ)).continuous (fun x => (SmoothDensityD.pos x).ne')

omit [SmoothDensityD ρ] in
theorem hasCompactSupport_testChiD (i : Fin d) (hc : HasCompactSupport φ) : HasCompactSupport (testChiD ρ i φ) :=
  by
    change HasCompactSupport (fun x => fderiv ℝ (φ * ρ) x (Pi.single i 1) / ρ x)
    simpa only [div_eq_mul_inv, Pi.mul_def] using
      (((hc.mul_right (f' := ρ)).fderiv_apply ℝ (Pi.single i 1)).mul_right (f' := fun x => (ρ x)⁻¹))

/-- Conversion to the weighted Lebesgue integral, without integrability side conditions. -/
theorem integral_densityD (f : (Fin d → ℝ) → ℝ) :
    (∫ x, f x ∂densityMeasureD ρ) = ∫ x, ρ x * f x := by
  rw [densityMeasureD, integral_withDensity_eq_integral_toReal_smul
    (SmoothDensityD.contDiff (ρ := ρ)).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (SmoothDensityD.pos _).le, smul_eq_mul]

variable [IsProbabilityMeasure (densityMeasureD ρ)]

/-- The compactly supported adjoint expression belongs to L². -/
def testChiLpD (i : Fin d) (φ : (Fin d → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Lp ℝ 2 (densityMeasureD ρ) :=
  ((continuous_testChiD ρ i hφ).memLp_of_hasCompactSupport (hasCompactSupport_testChiD ρ i hc)).toLp _

/--
For each coordinate, integration by parts identifies the gradient pairing with a compactly supported
C¹ test as the negative pairing with its weighted derivative `testChiLpD`.
-/
theorem inner_gradD_test (i : Fin d) (u : protoDomD ρ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    inner ℝ (gradD ρ i u) (protoOfFunctionD ρ φ (isC1Bounded_of_hasCompactSupportD hφ hc) : Lp ℝ 2 (densityMeasureD ρ)) =
      - inner ℝ (u : Lp ℝ 2 (densityMeasureD ρ)) (testChiLpD ρ i φ hφ hc) := by
  have hl : inner ℝ (gradD ρ i u)
      (protoOfFunctionD ρ φ (isC1Bounded_of_hasCompactSupportD hφ hc) : Lp ℝ 2 (densityMeasureD ρ)) =
      ∫ x, fderiv ℝ (repD ρ u) x (Pi.single i 1) * φ x ∂densityMeasureD ρ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_gradD ρ i u,
      MemLp.coeFn_toLp ((isC1Bounded_of_hasCompactSupportD hφ hc).memLp (densityMeasureD ρ) 2)] with x hu hx
    dsimp only [protoOfFunctionD]
    rw [hu, hx, real_inner_comm]
    rfl
  have hr : inner ℝ (u : Lp ℝ 2 (densityMeasureD ρ)) (testChiLpD ρ i φ hφ hc) =
      ∫ x, repD ρ u x * testChiD ρ i φ x ∂densityMeasureD ρ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_repD ρ u, MemLp.coeFn_toLp
      ((continuous_testChiD ρ i hφ).memLp_of_hasCompactSupport (μ := densityMeasureD ρ) (p := 2)
        (hasCompactSupport_testChiD ρ i hc))] with x hu hx
    dsimp only [testChiLpD]
    rw [hu, hx, real_inner_comm]
    rfl
  rw [hl, hr, integral_densityD, integral_densityD]
  convert integral_fderiv_mul_test i (rep_isC1BoundedD ρ u).1 hφ hc (SmoothDensityD.contDiff (ρ := ρ)) using 1
  · congr 1; funext x; ring
  · congr 1; congr 1; funext x
    dsimp [testChiD]
    field_simp [(SmoothDensityD.pos (ρ := ρ) x).ne']

end ErrorCalculus
