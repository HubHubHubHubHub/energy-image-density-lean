import Foundations.Haar.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Elementary real tent estimates used for the Schauder functions. -/

open Set

namespace Foundations

/-- The tent of unit slopes over an interval, extended by zero outside. -/
noncomputable def tent (a b t : ℝ) : ℝ := max 0 (min (t-a) (b-t))

/-- A tent is nonnegative at every real point. -/
theorem tent_nonneg (a b t : ℝ) : 0 ≤ tent a b t := le_max_left _ _

/-- The two ramps with a midpoint give exactly the tent. -/
theorem tent_eq_ramps {a m b : ℝ} (hab : a ≤ b) (hm : 2*m = a+b) (t : ℝ) :
    tent a b t = max 0 (min t m-a) - max 0 (min t b-m) := by
  simp only [tent, min_def, max_def]
  split_ifs <;> linarith

/-- The height bound is half the interval length. -/
theorem tent_le {a b : ℝ} (hab : a ≤ b) (t : ℝ) : tent a b t ≤ (b-a)/2 := by
  apply max_le
  · linarith
  · have h1 := min_le_left (t-a) (b-t)
    have h2 := min_le_right (t-a) (b-t)
    linarith

/-- The midpoint attains the height bound. -/
theorem tent_midpoint {a b : ℝ} (hab : a ≤ b) : tent a b ((a+b)/2) = (b-a)/2 := by
  unfold tent
  rw [show (a+b)/2-a = (b-a)/2 by ring, show b-(a+b)/2 = (b-a)/2 by ring, min_self]
  exact max_eq_right (by linarith)

/-- The nonzero support is the open interval. -/
theorem tent_ne_zero_iff (a b t : ℝ) : tent a b t ≠ 0 ↔ t ∈ Ioo a b := by
  simp only [tent, ne_eq, max_eq_left_iff, not_le, lt_min_iff, sub_pos, mem_Ioo]

/-- Tents are globally 1-Lipschitz, independently of the interval. -/
theorem lipschitzWith_tent (a b : ℝ) : LipschitzWith 1 (tent a b) := by
  have h1 : LipschitzWith 1 (fun t : ℝ => t-a) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq]
  have h2 : LipschitzWith 1 (fun t : ℝ => b-t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    rw [show b-x-(b-y) = -(x-y) by ring, abs_neg]
  change LipschitzWith 1 (fun t : ℝ => max 0 (min (t-a) (b-t)))
  simpa only [max_self] using (h1.min h2).const_max 0

end Foundations
