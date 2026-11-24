import GeometricMeasure.VectorMeasure.GoodRadii
import GeometricMeasure.Current.LocalizedDilation.Basic
import GeometricMeasure.VectorMeasure.SingularDifferentiation.Basic

/-!
# Nonzero divergence-free tangents

This file contains the definitions and results of the development of
`GeometricMeasure.Current.Tangent` that the main statements of the library (the head theorems listed
in the README of the repository) use. `GeometricMeasure.Current.Tangent` imports it and continues
the development.

## Main definitions

* `tentCutoff`: Tent cutoff: `1` on `B̄(0,1/2)`, `0` outside `ball 0 1` (support `B̄(0,3/4)`).

## Main statements

* `indicator_closedBall_half_le_cutoff`: If `χ ≥ 0` equals `1` on `closedBall 0 (1 / 2)` and `r >
  0`, the indicator of `closedBall x₀ (r / 2)` is at most `χ (dilationEquiv x₀ r _ y)` at every `y`.
* `inv_two_pow_le_measureReal_ratio`: If `ν` is finite and `0 < ν (closedBall x₀ r) ≤ 2 ^ d * ν
  (closedBall x₀ (r / 2))`, then `(2 ^ d)⁻¹ ≤ ν.real (closedBall x₀ (r / 2)) / ν.real (closedBall x₀
  r)`.
* `tentCutoff_le_one`: The tent cutoff `tentCutoff` is bounded above by `1` everywhere.
-/
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d m : ℕ}

theorem indicator_closedBall_half_le_cutoff
    (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) (hχ0 : ∀ y, 0 ≤ χ y)
    (hχB : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2), χ y = 1)
    (x₀ : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) (y : EuclideanSpace ℝ (Fin d)) :
    (closedBall x₀ (r / 2)).indicator 1 y ≤ χ (dilationEquiv x₀ r hr.ne' y) := by
  by_cases hy : y ∈ closedBall x₀ (r / 2)
  · rw [indicator_of_mem hy, Pi.one_apply]
    have hmem : dilationEquiv x₀ r hr.ne' y ∈
        closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2) := by
      rw [← mem_preimage, preimage_closedBall_dilation, abs_of_pos hr]
      convert hy using 2
      ring
    rw [hχB _ hmem]
  · rw [indicator_of_notMem hy]
    exact hχ0 _

theorem inv_two_pow_le_measureReal_ratio
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hpos : 0 < ν (closedBall x₀ r))
    (h : ν (closedBall x₀ r) ≤ 2 ^ d * ν (closedBall x₀ (r / 2))) :
    ((2 : ℝ) ^ d)⁻¹ ≤ ν.real (closedBall x₀ (r / 2)) / ν.real (closedBall x₀ r) := by
  have hp : 0 < ν.real (closedBall x₀ r) := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hR : ν.real (closedBall x₀ r) ≤ 2 ^ d * ν.real (closedBall x₀ (r / 2)) := by
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) h
    simpa [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow] using h'
  rw [le_div_iff₀ hp, inv_mul_le_iff₀ (by positivity)]
  exact hR

/-- Tent cutoff: `1` on `B̄(0,1/2)`, `0` outside `ball 0 1` (support `B̄(0,3/4)`). -/
def tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => max 0 (min 1 (3 - 4 * ‖y‖)))
    (continuous_const.max (continuous_const.min
      (continuous_const.sub (continuous_const.mul continuous_norm)))) 1
    (fun y => by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [le_max_left (0 : ℝ) (min 1 (3 - 4 * ‖y‖))]
      · exact max_le (by norm_num) (min_le_left _ _))

theorem tentCutoff_apply (y : EuclideanSpace ℝ (Fin d)) :
    (tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) y =
      max 0 (min 1 (3 - 4 * ‖y‖)) := rfl

theorem tentCutoff_nonneg (y : EuclideanSpace ℝ (Fin d)) :
    0 ≤ (tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) y := by
  rw [tentCutoff_apply]; exact le_max_left _ _

theorem tentCutoff_le_one (y : EuclideanSpace ℝ (Fin d)) :
    (tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) y ≤ 1 := by
  rw [tentCutoff_apply]; exact max_le (by norm_num) (min_le_left _ _)

theorem tentCutoff_eq_one {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) :
    (tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) y = 1 := by
  rw [mem_closedBall, dist_zero_right] at hy
  rw [tentCutoff_apply, min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem tentCutoff_eq_zero {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∉ ball (0 : EuclideanSpace ℝ (Fin d)) 1) :
    (tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) y = 0 := by
  rw [mem_ball, dist_zero_right, not_lt] at hy
  rw [tentCutoff_apply, min_eq_right (by linarith), max_eq_left (by linarith)]

end GeometricMeasure
