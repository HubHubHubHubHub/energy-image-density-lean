import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory Filter Set Function Metric ContinuousLinearMap
open scoped Topology ENNReal ContDiff Convolution
namespace Foundations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [HasContDiffBump E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- Compact normalized approximate identity in any finite-dimensional bump space. -/
def acMollifier (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    ContDiffBump (0 : E) :=
  ⟨(1 / (n+1 : ℝ))/2, 1 / (n+1 : ℝ), by positivity, by exact half_lt_self (by positivity)⟩

def acKernel (n : ℕ) : E → ℝ := (acMollifier E n).normed volume

theorem contDiff_acKernel (n : ℕ) : ContDiff ℝ ∞ (acKernel (E := E) n) :=
  (acMollifier E n).contDiff_normed

theorem hasCompactSupport_acKernel (n : ℕ) : HasCompactSupport (acKernel (E := E) n) :=
  (acMollifier E n).hasCompactSupport_normed

theorem integrable_acKernel (n : ℕ) : Integrable (acKernel (E := E) n) :=
  (acMollifier E n).integrable_normed

theorem integral_acKernel (n : ℕ) : ∫ x : E, acKernel n x = 1 :=
  (acMollifier E n).integral_normed

theorem acKernel_nonneg (n : ℕ) (x : E) : 0 ≤ acKernel n x :=
  (acMollifier E n).nonneg_normed x

theorem acKernel_neg (n : ℕ) (x : E) : acKernel n (-x) = acKernel n x :=
  (acMollifier E n).normed_neg x

/-- Convolution of a finite measure with a smooth normalized compact kernel. -/
def measureMollify (ν : Measure E) (n : ℕ) (x : E) : ℝ :=
  ∫ y, acKernel n (x-y) ∂ν

variable (ν : Measure E) [IsFiniteMeasure ν]

theorem measureMollify_eq_convolution (n : ℕ) :
    measureMollify ν n = (fun _ : E => (1:ℝ)) ⋆[lsmul ℝ ℝ, ν] acKernel n := by
  ext x
  simp [measureMollify, convolution_def]

theorem contDiff_measureMollify (n : ℕ) : ContDiff ℝ ∞ (measureMollify ν n) := by
  rw [measureMollify_eq_convolution]
  exact (hasCompactSupport_acKernel n).contDiff_convolution_right (lsmul ℝ ℝ)
    (integrable_const 1).locallyIntegrable (contDiff_acKernel n)

theorem measureMollify_nonneg (n : ℕ) (x : E) : 0 ≤ measureMollify ν n x :=
  integral_nonneg fun y => acKernel_nonneg n (x-y)

/-- Joint integrability, used for all measure/kernel Fubini interchanges. -/
theorem integrable_acKernel_sub (n : ℕ) :
    Integrable (fun z : E × E => acKernel n (z.1-z.2)) (volume.prod ν) := by
  simpa using (integrable_const (1:ℝ) (μ := ν)).convolution_integrand (lsmul ℝ ℝ)
    (integrable_acKernel (E := E) n)

theorem integrable_measureMollify (n : ℕ) : Integrable (measureMollify ν n) :=
  (integrable_acKernel_sub ν n).integral_prod_left

theorem integral_measureMollify (n : ℕ) :
    (∫ x, measureMollify ν n x) = ν.real univ := by
  unfold measureMollify
  rw [integral_integral_swap (integrable_acKernel_sub ν n)]
  simp only [integral_sub_right_eq_self, integral_acKernel, integral_const, smul_eq_mul, mul_one]

/--
Differentiating under a finite measure is justified by a global bound on the kernel derivative.
-/
theorem hasFDerivAt_measureMollify (n : ℕ) (x : E) :
    HasFDerivAt (measureMollify ν n) (∫ y, fderiv ℝ (acKernel (E := E) n) (x-y) ∂ν) x := by
  have hc : ContDiff ℝ 1 (acKernel (E := E) n) := (contDiff_acKernel n).of_le (by simp)
  have hd := (hc.continuous_fderiv one_ne_zero)
  obtain ⟨C,hC⟩ := ((hasCompactSupport_acKernel (E := E) n).fderiv ℝ).exists_bound_of_continuous hd
  have hk : Integrable (fun y => acKernel n (x-y)) ν := by
    obtain ⟨K,hK⟩ := (hasCompactSupport_acKernel (E := E) n).exists_bound_of_continuous hc.continuous
    exact Integrable.of_bound (hc.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      K (Eventually.of_forall fun y => hK _)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := fun _ => C)
    (F' := fun x y => fderiv ℝ (acKernel (E := E) n) (x-y)) (Filter.univ_mem)
  · exact Eventually.of_forall fun z => (hc.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact hk
  · exact (hd.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun y z _ => hC _
  · exact integrable_const C
  · exact Eventually.of_forall fun y z _ =>
      (hc.differentiable one_ne_zero (z-y)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const y) |>.congr_fderiv (by simp)

/-- The directional derivative as a scalar kernel integral. -/
theorem fderiv_measureMollify_apply (n : ℕ) (x v : E) :
    fderiv ℝ (measureMollify ν n) x v = ∫ y, fderiv ℝ (acKernel (E := E) n) (x-y) v ∂ν := by
  rw [(hasFDerivAt_measureMollify ν n x).fderiv]
  apply ContinuousLinearMap.integral_apply
  have hc : ContDiff ℝ 1 (acKernel (E := E) n) := (contDiff_acKernel n).of_le (by simp)
  obtain ⟨C,hC⟩ := ((hasCompactSupport_acKernel (E := E) n).fderiv ℝ).exists_bound_of_continuous (hc.continuous_fderiv one_ne_zero)
  exact Integrable.of_bound ((hc.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    C (Eventually.of_forall fun y => hC _)

end Foundations
