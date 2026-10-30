import Foundations.Mehler.Markov
import Foundations.Hermite.Rodrigues
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations

/-- Bounded C¹ functions with bounded first derivative. -/
structure IsC1Bounded (f : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 f
  bounded : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
  deriv_bounded : ∃ C : ℝ, ∀ x, ‖deriv f x‖ ≤ C

/-- Bounded C² functions with bounded first and second derivatives. -/
def IsC2Bounded (f : ℝ → ℝ) : Prop := IsC1Bounded f ∧ IsC1Bounded (deriv f)

theorem memLp_gaussian_of_bounded {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (p : ENNReal) : MemLp f p standardGaussian := by
  obtain ⟨C,hC⟩ := hb
  exact MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)

theorem IsC1Bounded.memLp {f : ℝ → ℝ} (hf : IsC1Bounded f) (p : ENNReal) :
    MemLp f p standardGaussian := memLp_gaussian_of_bounded hf.contDiff.continuous hf.bounded p

theorem IsC1Bounded.memLp_deriv {f : ℝ → ℝ} (hf : IsC1Bounded f) (p : ENNReal) :
    MemLp (deriv f) p standardGaussian :=
  memLp_gaussian_of_bounded hf.contDiff.continuous_deriv_one hf.deriv_bounded p

theorem IsC1Bounded.hasDerivAt {f : ℝ → ℝ} (hf : IsC1Bounded f) (x : ℝ) :
    HasDerivAt f (deriv f x) x := (hf.contDiff.differentiable (by norm_num) x).hasDerivAt

@[fun_prop] theorem continuous_mehlerCoeffA : Continuous mehlerCoeffA := by
  unfold mehlerCoeffA; fun_prop
@[fun_prop] theorem continuous_mehlerCoeffB : Continuous mehlerCoeffB := by
  unfold mehlerCoeffB; fun_prop

theorem mehlerCoeffA_pos (t : ℝ) : 0 < mehlerCoeffA t := Real.exp_pos _
theorem mehlerCoeffA_le_one {t : ℝ} (ht : 0 ≤ t) : mehlerCoeffA t ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
theorem mehlerCoeffB_nonneg (t : ℝ) : 0 ≤ mehlerCoeffB t := Real.sqrt_nonneg _
theorem mehlerCoeffB_pos {t : ℝ} (ht : 0 < t) : 0 < mehlerCoeffB t := by
  apply Real.sqrt_pos.mpr
  have h : Real.exp (-2*t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

theorem mehlerCoeffA_sq (t : ℝ) : (mehlerCoeffA t)^2 = Real.exp (-2*t) := by
  rw [mehlerCoeffA,← Real.exp_nat_mul]
  congr 1
  ring

theorem integrable_gaussian_affine {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (a b : ℝ) :
    Integrable (fun y => f (a+b*y)) standardGaussian := by
  exact (memLp_gaussian_of_bounded (by fun_prop)
    (by obtain ⟨C,hC⟩ := hb; exact ⟨C,fun y => hC _⟩) 1).integrable le_rfl

theorem norm_mehlerKernel_le {f : ℝ → ℝ} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (t x : ℝ) :
    ‖mehlerKernel t f x‖ ≤ C := by
  exact (norm_integral_le_of_norm_le_const (ae_of_all _ (fun y => hC _))).trans_eq (by simp)

theorem le_mehlerKernel {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) {c : ℝ} (hc : ∀ x, c ≤ f x) (t x : ℝ) :
    c ≤ mehlerKernel t f x := by
  simpa [mehlerKernel] using integral_mono (integrable_const c)
    (integrable_gaussian_affine hf hb (mehlerCoeffA t*x) (mehlerCoeffB t)) (fun y => hc _)

theorem mehlerKernel_le {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) {c : ℝ} (hc : ∀ x, f x ≤ c) (t x : ℝ) :
    mehlerKernel t f x ≤ c := by
  simpa [mehlerKernel] using integral_mono
    (integrable_gaussian_affine hf hb (mehlerCoeffA t*x) (mehlerCoeffB t))
    (integrable_const c) (fun y => hc _)

theorem continuous_mehlerKernel {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Continuous (fun p : ℝ × ℝ => mehlerKernel p.1 f p.2) := by
  obtain ⟨C,hC⟩ := hb
  apply continuous_of_dominated (bound := fun _ => C)
  · intro p; exact (hf.comp (by fun_prop)).aestronglyMeasurable
  · intro p; exact ae_of_all _ (fun y => hC _)
  · exact integrable_const C
  · exact ae_of_all _ (fun y => hf.comp (by fun_prop))

theorem integral_mehlerKernel {f : ℝ → ℝ} (hf : MemLp f 2 standardGaussian)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, mehlerKernel t f x ∂standardGaussian) = ∫ x, f x ∂standardGaussian := by
  rw [← integral_congr_ae (coe_mehler_toLp ht hf),integral_mehler ht,
    integral_congr_ae hf.coeFn_toLp]

end Foundations
