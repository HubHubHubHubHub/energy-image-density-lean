import Foundations.Hermite.Orthogonality
import Mathlib.Probability.Independence.Basic

noncomputable section
open Filter Topology Set MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal InnerProductSpace
namespace Foundations

def mehlerCoeffA (t : ℝ) : ℝ := Real.exp (-t)
def mehlerCoeffB (t : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-2*t))

theorem mehlerCoeff_sq {t : ℝ} (ht : 0 ≤ t) :
    mehlerCoeffA t ^ 2 + mehlerCoeffB t ^ 2 = 1 := by
  have he : Real.exp (-2*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [mehlerCoeffB, Real.sq_sqrt (by linarith)]
  have ha : mehlerCoeffA t ^ 2 = Real.exp (-2*t) := by
    rw [mehlerCoeffA, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [ha]
  ring

@[simp] theorem mehlerCoeffA_zero : mehlerCoeffA 0 = 1 := by simp [mehlerCoeffA]
@[simp] theorem mehlerCoeffB_zero : mehlerCoeffB 0 = 0 := by simp [mehlerCoeffB]

theorem map_gaussian_linear_combination {a b : ℝ} (hab : a^2+b^2=1) :
    (standardGaussian.prod standardGaussian).map (fun z : ℝ×ℝ => a*z.1+b*z.2) =
      standardGaussian := by
  have hX : (standardGaussian.prod standardGaussian).map (fun z : ℝ×ℝ => a*z.1) =
      gaussianReal 0 (NNReal.mk (a^2) (sq_nonneg a)) := by
    rw [show (fun z : ℝ×ℝ => a*z.1) = (fun x : ℝ => a*x) ∘ Prod.fst from rfl,
      ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod]
    simp [standardGaussian, gaussianReal_map_const_mul, NNReal.mk]
  have hY : (standardGaussian.prod standardGaussian).map (fun z : ℝ×ℝ => b*z.2) =
      gaussianReal 0 (NNReal.mk (b^2) (sq_nonneg b)) := by
    rw [show (fun z : ℝ×ℝ => b*z.2) = (fun x : ℝ => b*x) ∘ Prod.snd from rfl,
      ← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod]
    simp [standardGaussian, gaussianReal_map_const_mul, NNReal.mk]
  have h := gaussianReal_add_gaussianReal_of_indepFun
    (indepFun_prod (μ := standardGaussian) (ν := standardGaussian)
      (X := fun x : ℝ => a*x) (Y := fun y : ℝ => b*y) (by fun_prop) (by fun_prop)) hX hY
  have hv : ((NNReal.mk (a^2) (sq_nonneg a)) : ℝ≥0) + (NNReal.mk (b^2) (sq_nonneg b)) = 1 := by
    apply NNReal.eq
    exact hab
  change (standardGaussian.prod standardGaussian).map (fun z : ℝ×ℝ => a*z.1+b*z.2) =
    gaussianReal (0+0) ((NNReal.mk (a^2) (sq_nonneg a)) + (NNReal.mk (b^2) (sq_nonneg b))) at h
  rw [hv, zero_add] at h
  exact h

theorem map_mehler_gaussian {t : ℝ} (ht : 0 ≤ t) :
    (standardGaussian.prod standardGaussian).map
      (fun z : ℝ×ℝ => mehlerCoeffA t*z.1+mehlerCoeffB t*z.2) = standardGaussian :=
  map_gaussian_linear_combination (mehlerCoeff_sq ht)

/-- The Gaussian mixing map, with reversed coordinate order to match the section isometry. -/
def mehlerMix (t : ℝ) (z : ℝ×ℝ) : ℝ := mehlerCoeffA t*z.2+mehlerCoeffB t*z.1

theorem measurePreserving_mehlerMix {t : ℝ} (ht : 0 ≤ t) :
    MeasurePreserving (mehlerMix t) (standardGaussian.prod standardGaussian) standardGaussian := by
  refine ⟨by unfold mehlerMix; fun_prop, ?_⟩
  change (standardGaussian.prod standardGaussian).map
    (fun z : ℝ×ℝ => mehlerCoeffA t*z.2+mehlerCoeffB t*z.1) = standardGaussian
  simpa only [add_comm] using
    (map_gaussian_linear_combination (a := mehlerCoeffB t) (b := mehlerCoeffA t)
      (by linarith [mehlerCoeff_sq ht]))

def mehlerKernel (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, f (mehlerCoeffA t*x+mehlerCoeffB t*y) ∂standardGaussian

@[simp] theorem mehlerKernel_zero (f : ℝ → ℝ) (x : ℝ) : mehlerKernel 0 f x = f x := by
  simp [mehlerKernel]

end Foundations
