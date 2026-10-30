import Foundations.LogSobolev.Representative
import ErrorCalculus.Dirichlet.ExtensionLp
import Mathlib.Analysis.Convex.Integral

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {μ : Measure Ω} {ν : Measure Ω'}

/-- Real entropy; inequalities below also assert integrability of its integrand. -/
def entropy (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  (∫ x, f x * Real.log (f x) ∂μ) -
    (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ)

@[simp] theorem entropy_eq_foundations (μ : Measure ℝ) (f : ℝ → ℝ) :
    entropy μ f = Foundations.entropy μ f := rfl

theorem entropy_congr_ae {f g : Ω → ℝ} (h : f =ᵐ[μ] g) :
    entropy μ f = entropy μ g := by
  unfold entropy
  have he := integral_congr_ae (h.fun_comp (fun z => z * Real.log z))
  simp only [Function.comp_def] at he
  rw [integral_congr_ae h, he]

/-- Change of variables for a measurable representative, without injectivity. -/
theorem entropy_comp_measurePreserving {T : Ω → Ω'}
    (hT : MeasurePreserving T μ ν) {f : Ω' → ℝ} (hf : AEStronglyMeasurable f ν) :
    entropy μ (f ∘ T) = entropy ν f := by
  have hm : AEStronglyMeasurable f (Measure.map T μ) := by rwa [hT.map_eq]
  have he := Real.continuous_mul_log.comp_aestronglyMeasurable hm
  have hi := integral_map hT.aemeasurable hm
  have hi' := integral_map hT.aemeasurable he
  rw [hT.map_eq] at hi hi'
  simp only [entropy, Function.comp_def]
  rw [← hi, ← hi']

/-- Homogeneity of real entropy. The formula even holds for signed scalars with Real.log. -/
theorem entropy_smul (c : ℝ) {f : Ω → ℝ} (hf : Integrable f μ)
    (he : Integrable (fun x => f x * Real.log (f x)) μ) :
    entropy μ (fun x => c * f x) = c * entropy μ f := by
  have hmul (a b : ℝ) : (a*b) * Real.log (a*b) =
      b * (a * Real.log a) + a * (b * Real.log b) := by
    have hh := Real.negMulLog_mul a b
    dsimp [Real.negMulLog] at hh
    linarith
  have hfn : (fun x => (c*f x) * Real.log (c*f x)) =
      (fun x => c * (f x * Real.log (f x)) + (c * Real.log c) * f x) := by
    funext x
    rw [hmul]
    ring
  unfold entropy
  rw [hfn, integral_add (he.const_mul c) (hf.const_mul (c * Real.log c)),
    integral_const_mul, integral_const_mul, integral_const_mul, hmul]
  ring

/-- Jensen's inequality for nonnegative functions on a probability space. -/
theorem entropy_nonneg [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (he : Integrable (fun x => f x * Real.log (f x)) μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ f x) : 0 ≤ entropy μ f := by
  exact sub_nonneg.mpr (Real.convexOn_mul_log.map_integral_le
    Real.continuous_mul_log.continuousOn isClosed_Ici hpos hf he)

end ErrorCalculus
