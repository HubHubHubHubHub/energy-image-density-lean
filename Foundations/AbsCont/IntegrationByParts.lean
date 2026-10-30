import Foundations.AbsCont.TotalVariation

noncomputable section
open MeasureTheory Filter Set Function ContinuousLinearMap
open scoped Topology ENNReal ContDiff Convolution
namespace Foundations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [HasContDiffBump E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem continuous_acKernel_deriv (n : ℕ) (v : E) :
    Continuous (fun x => fderiv ℝ (acKernel (E := E) n) x v) :=
  ((contDiff_acKernel n).continuous_fderiv (by simp)).clm_apply continuous_const

theorem hasCompactSupport_acKernel_deriv (n : ℕ) (v : E) :
    HasCompactSupport (fun x => fderiv ℝ (acKernel (E := E) n) x v) :=
  ((hasCompactSupport_acKernel n).fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L v) (by simp)

theorem integrable_acKernel_deriv (n : ℕ) (v : E) :
    Integrable (fun x => fderiv ℝ (acKernel (E := E) n) x v) :=
  (continuous_acKernel_deriv n v).integrable_of_hasCompactSupport
    (hasCompactSupport_acKernel_deriv n v)

theorem acKernel_deriv_neg (n : ℕ) (x v : E) :
    fderiv ℝ (acKernel (E := E) n) (-x) v = -fderiv ℝ (acKernel n) x v := by
  have h := ((contDiff_acKernel (E := E) n).differentiable (by simp) (-x)).hasFDerivAt.comp x
    (hasFDerivAt_id x).neg
  have he : (fun z : E => acKernel n (-z)) = acKernel n := funext (acKernel_neg n)
  rw [Function.comp_def, he] at h
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) h.fderiv
  have hh' : fderiv ℝ (acKernel n) x v = -fderiv ℝ (acKernel n) (-x) v := by simpa using hh
  linarith

variable (ν : Measure E) [IsFiniteMeasure ν]

theorem integrable_acKernel_deriv_sub (n : ℕ) (v : E) :
    Integrable (fun z : E × E => fderiv ℝ (acKernel n) (z.1-z.2) v) (volume.prod ν) := by
  simpa using (integrable_const (1:ℝ) (μ := ν)).convolution_integrand (lsmul ℝ ℝ)
    (integrable_acKernel_deriv n v)

theorem integrable_deriv_measureMollify (n : ℕ) (v : E) :
    Integrable (fun x => fderiv ℝ (measureMollify ν n) x v) := by
  simp_rw [fderiv_measureMollify_apply]
  exact (integrable_acKernel_deriv_sub ν n v).integral_prod_left

/-- Unit-ball formulation of the distributional derivative bound. -/
def HasIBPBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (ν : Measure E) (v : E) (C : ℝ) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, ‖φ x‖ ≤ 1) →
    |∫ x, fderiv ℝ φ x v ∂ν| ≤ C

/-- Duality transfers the distributional bound to every smooth density. -/
theorem integral_norm_deriv_measureMollify_le (v : E) {C : ℝ}
    (hb : HasIBPBound ν v C) (n : ℕ) :
    ∫ x, ‖fderiv ℝ (measureMollify ν n) x v‖ ≤ C := by
  apply integral_norm_le_of_test_bound
    (((contDiff_measureMollify ν n).continuous_fderiv (by simp)).clm_apply continuous_const)
    (integrable_deriv_measureMollify ν n v)
  intro ψ hψ hψk hψb
  let φ := ψ ⋆[lsmul ℝ ℝ] acKernel (E := E) n
  have hφ : ContDiff ℝ ∞ φ := (hasCompactSupport_acKernel n).contDiff_convolution_right
    (lsmul ℝ ℝ) hψ.locallyIntegrable (contDiff_acKernel n)
  have hφk : HasCompactSupport φ := hψk.convolution (lsmul ℝ ℝ) (hasCompactSupport_acKernel n)
  have hφb (x : E) : ‖φ x‖ ≤ 1 := by
    have H := dist_convolution_le (μ := (volume : Measure E)) (x₀ := x) (z₀ := (0:ℝ))
      (R := (acMollifier E n).rOut) zero_le_one
      (by simpa [acKernel] using (acMollifier E n).support_normed_eq (μ := volume) |>.subset)
      (acKernel_nonneg n) (integral_acKernel n) hψ.aestronglyMeasurable
      (fun z _ => by simpa using hψb z)
    have he : (acKernel n ⋆[lsmul ℝ ℝ] ψ) x = φ x := by
      rw [convolution_lsmul_swap]
      change (∫ z, acKernel n (x-z) • ψ z) = ∫ z, ψ z • acKernel n (x-z)
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by simp only [smul_eq_mul, mul_comm]
    simpa only [he, dist_zero_right] using H
  have hφd (y : E) : fderiv ℝ φ y v = ∫ x, ψ x * fderiv ℝ (acKernel n) (y-x) v := by
    rw [((hasCompactSupport_acKernel n).hasFDerivAt_convolution_right (lsmul ℝ ℝ)
      hψ.locallyIntegrable ((contDiff_acKernel n).of_le (by simp)) y).fderiv]
    rw [convolution_precompR_apply (lsmul ℝ ℝ) hψ.locallyIntegrable
      ((hasCompactSupport_acKernel n).fderiv ℝ)
      ((contDiff_acKernel n).continuous_fderiv (by simp))]
    rfl
  have hj : Integrable (fun z : E × E => ψ z.1 * fderiv ℝ (acKernel n) (z.1-z.2) v)
      (volume.prod ν) :=
    (integrable_acKernel_deriv_sub ν n v).bdd_mul (hψ.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun z => hψb _)
  have he : (∫ x, ψ x * fderiv ℝ (measureMollify ν n) x v) =
      -(∫ y, fderiv ℝ φ y v ∂ν) := by
    simp_rw [fderiv_measureMollify_apply, ← integral_const_mul]
    rw [integral_integral_swap hj, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [hφd, ← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        have H := acKernel_deriv_neg n (x-y) v
        rw [neg_sub] at H
        rw [H]
        ring
  rw [he, abs_neg]
  exact hb φ hφ hφk hφb

/-- The L¹ seminorm version of the distributional derivative estimate. -/
theorem eLpNorm_one_deriv_measureMollify_le (v : E) {C : ℝ}
    (hb : HasIBPBound ν v C) (n : ℕ) :
    eLpNorm (fun x => fderiv ℝ (measureMollify ν n) x v) 1 ≤ ENNReal.ofReal C := by
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm
    (integrable_deriv_measureMollify ν n v)]
  exact ENNReal.ofReal_le_ofReal (integral_norm_deriv_measureMollify_le ν v hb n)

end Foundations
