import Foundations.AbsCont.IntegrationByParts
import Foundations.AbsCont.WeakLimit
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
namespace Foundations

/-- The one-dimensional endpoint follows from the FTC on a half-line. -/
theorem enorm_le_eLpNorm_deriv_of_integrable {g : ℝ → ℝ} (hc : ContDiff ℝ 1 g)
    (hi : Integrable g) (hd : Integrable (deriv g)) (x : ℝ) :
    ‖g x‖ₑ ≤ eLpNorm (deriv g) 1 := by
  have hD : ∀ y ∈ Iic x, HasDerivAt g (deriv g y) y :=
    fun y _ => (hc.differentiable one_ne_zero y).hasDerivAt
  have hzero := tendsto_zero_of_hasDerivAt_of_integrableOn_Iic hD hd.integrableOn hi.integrableOn
  have he : (∫ y in Iic x, deriv g y) = g x := by
    simpa using integral_Iic_of_hasDerivAt_of_tendsto' hD hd.integrableOn hzero
  rw [← he, eLpNorm_one_eq_lintegral_enorm]
  exact (enorm_integral_le_lintegral_enorm (μ := volume.restrict (Iic x)) (deriv g)).trans
    (lintegral_mono' Measure.restrict_le_self le_rfl)

theorem absolutelyContinuous_of_integral_deriv_le_real (ν : Measure ℝ) [IsFiniteMeasure ν]
    {C : ℝ} (hb : HasIBPBound ν 1 C) : ν ≪ volume := by
  apply absolutelyContinuous_of_eLpNorm_measureMollify_le ν (p := 1) (q := (⊤ : ℝ≥0∞)) (M := ENNReal.ofReal C)
    le_rfl ENNReal.one_ne_top ENNReal.ofReal_ne_top
  intro n
  have hd : Integrable (deriv (measureMollify ν n)) := by
    simpa only [fderiv_apply_one_eq_deriv] using integrable_deriv_measureMollify ν n (1:ℝ)
  have hb' : eLpNorm (deriv (measureMollify ν n)) 1 ≤ ENNReal.ofReal C := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hd]
    apply ENNReal.ofReal_le_ofReal
    simpa only [fderiv_apply_one_eq_deriv] using integral_norm_deriv_measureMollify_le ν 1 hb n
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  exact Eventually.of_forall fun x =>
    (enorm_le_eLpNorm_deriv_of_integrable ((contDiff_measureMollify ν n).of_le (by simp))
      (integrable_measureMollify ν n) hd x).trans hb'

end Foundations
