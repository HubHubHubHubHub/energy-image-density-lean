import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Basic

## Main results
Dyadic cells and normalized Haar functions on the real line.
-/

open Set MeasureTheory
open scoped BigOperators
open scoped Classical

namespace Foundations

/-- half-open dyadic cell; natural indices outside the unit interval are allowed. -/
def dyadicCell (j k : ℕ) : Set ℝ :=
  Ico ((k : ℝ) / (2:ℝ)^j) (((k:ℝ)+1) / (2:ℝ)^j)

/-- The unnormalized cell indicator. -/
noncomputable def dyadicIndicator (j k : ℕ) (x : ℝ) : ℝ :=
  (dyadicCell j k).indicator (fun _ => 1) x

/-- Haar's normalized difference of the two half-cell indicators. -/
noncomputable def haar (j k : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt ((2:ℝ)^j) * (dyadicIndicator (j+1) (2*k) x - dyadicIndicator (j+1) (2*k+1) x)

/-- membership in a cell in scaled coordinates. -/
theorem mem_dyadicCell (j k : ℕ) (x : ℝ) :
    x ∈ dyadicCell j k ↔ (k:ℝ) ≤ (2:ℝ)^j*x ∧ (2:ℝ)^j*x < (k:ℝ)+1 := by
  have hp : 0 < (2:ℝ)^j := by positivity
  simp only [dyadicCell, mem_Ico, div_le_iff₀ hp, lt_div_iff₀ hp, mul_comm x]

/-- indicators have an explicit 0/1 representative. -/
theorem dyadicIndicator_apply (j k : ℕ) (x : ℝ) :
    dyadicIndicator j k x = if x ∈ dyadicCell j k then 1 else 0 := rfl

/-- measurability of cell indicators. -/
theorem measurable_dyadicIndicator (j k : ℕ) : Measurable (dyadicIndicator j k) :=
  measurable_const.indicator measurableSet_Ico

/-- measurability of Haar functions. -/
theorem measurable_haar (j k : ℕ) : Measurable (haar j k) :=
  measurable_const.mul ((measurable_dyadicIndicator _ _).sub (measurable_dyadicIndicator _ _))

/-- Each cell indicator is nonnegative. -/
theorem dyadicIndicator_nonneg (j k : ℕ) (x : ℝ) : 0 ≤ dyadicIndicator j k x := by
  rw [dyadicIndicator_apply]; split_ifs <;> norm_num

/-- different cells at the same level cannot contain the same point. -/
theorem dyadicCell_unique {j k l : ℕ} {x : ℝ}
    (hk : x ∈ dyadicCell j k) (hl : x ∈ dyadicCell j l) : k = l := by
  rw [mem_dyadicCell] at hk hl
  have hkl : (k:ℝ) < (l:ℝ)+1 := hk.1.trans_lt hl.2
  have hlk : (l:ℝ) < (k:ℝ)+1 := hl.1.trans_lt hk.2
  have : k < l+1 := by exact_mod_cast hkl
  have : l < k+1 := by exact_mod_cast hlk
  omega

/-- a parent indicator is the sum of its half-cell indicators, at every real point. -/
theorem dyadicIndicator_refine (j k : ℕ) (x : ℝ) :
    dyadicIndicator j k x = dyadicIndicator (j+1) (2*k) x +
      dyadicIndicator (j+1) (2*k+1) x := by
  simp only [dyadicIndicator_apply, mem_dyadicCell, pow_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_ofNat]
  split_ifs <;> simp_all <;> grind

/-- Haar vanishes off its parent cell. -/
theorem haar_eq_zero_of_not_mem {j k : ℕ} {x : ℝ} (hx : x ∉ dyadicCell j k) :
    haar j k x = 0 := by
  have h := dyadicIndicator_refine j k x
  rw [dyadicIndicator_apply j k x, if_neg hx] at h
  have hL := dyadicIndicator_nonneg (j+1) (2*k) x
  have hR := dyadicIndicator_nonneg (j+1) (2*k+1) x
  have hl : dyadicIndicator (j+1) (2*k) x = 0 := by linarith
  have hr : dyadicIndicator (j+1) (2*k+1) x = 0 := by linarith
  simp [haar, hl, hr]

/-- The square of a Haar function is its parent indicator times 2^j. -/
theorem haar_sq (j k : ℕ) (x : ℝ) : (haar j k x)^2 = (2:ℝ)^j * dyadicIndicator j k x := by
  have hs := Real.sq_sqrt (show 0 ≤ (2:ℝ)^j by positivity)
  rw [haar, mul_pow, hs, dyadicIndicator_refine j k x]
  by_cases hl : x ∈ dyadicCell (j+1) (2*k)
  · have hr : x ∉ dyadicCell (j+1) (2*k+1) := by
      intro hr
      have := dyadicCell_unique hl hr
      omega
    simp [dyadicIndicator_apply, hl, hr]
  · by_cases hr : x ∈ dyadicCell (j+1) (2*k+1) <;>
      simp [dyadicIndicator_apply, hl, hr]

/-- The finite even/odd reindexing used at each refinement step. -/
theorem sum_range_two_mul (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (2*n), f k = ∑ k ∈ Finset.range n, (f (2*k) + f (2*k+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- The indicators at every level sum to the indicator of [0,1). -/
theorem sum_dyadicIndicator (j : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (2^j), dyadicIndicator j k x = dyadicIndicator 0 0 x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Nat.mul_comm, sum_range_two_mul]
    simpa only [← dyadicIndicator_refine] using ih

/-- The zeroth cell indicator is exactly the indicator of the unit interval. -/
theorem dyadicIndicator_zero (x : ℝ) :
    dyadicIndicator 0 0 x = if x ∈ Ico (0:ℝ) 1 then 1 else 0 := by
  simp [dyadicIndicator_apply, dyadicCell]

/-- nonnegative real coordinates identify a cell by the natural floor. -/
theorem mem_dyadicCell_iff_floor (j k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ∈ dyadicCell j k ↔ ⌊(2:ℝ)^j*x⌋₊ = k := by
  rw [mem_dyadicCell, Nat.floor_eq_iff (mul_nonneg (by positivity) hx)]

/-- The natural floor lies in the finite level for x in [0,1). -/
theorem floor_dyadic_lt (j : ℕ) {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    ⌊(2:ℝ)^j*x⌋₊ < 2^j := by
  rw [Nat.floor_lt (mul_nonneg (by positivity) hx.1)]
  push_cast
  simpa using mul_lt_mul_of_pos_left hx.2 (show 0 < (2:ℝ)^j by positivity)

/-- floor indices refine into the even or odd child index. -/
theorem floor_dyadic_succ {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    ⌊(2:ℝ)^(j+1)*x⌋₊ = 2*⌊(2:ℝ)^j*x⌋₊ ∨
      ⌊(2:ℝ)^(j+1)*x⌋₊ = 2*⌊(2:ℝ)^j*x⌋₊ + 1 := by
  have hxj : 0 ≤ (2:ℝ)^j*x := mul_nonneg (by positivity) hx
  have hlo := Nat.floor_le hxj
  have hup := Nat.lt_floor_add_one ((2:ℝ)^j*x)
  have hL : 2*⌊(2:ℝ)^j*x⌋₊ ≤ ⌊(2:ℝ)^(j+1)*x⌋₊ := by
    apply Nat.le_floor
    push_cast
    rw [pow_succ]
    nlinarith
  have hU : ⌊(2:ℝ)^(j+1)*x⌋₊ < 2*⌊(2:ℝ)^j*x⌋₊+2 := by
    apply (Nat.floor_lt (mul_nonneg (by positivity) hx)).mpr
    push_cast
    rw [pow_succ]
    nlinarith
  omega

end Foundations
