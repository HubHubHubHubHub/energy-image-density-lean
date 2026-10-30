import Foundations.Haar.Basic

/-!
# Kernel

## Main results
The reproducing dyadic kernel.
-/

open Set
open scoped BigOperators Classical

namespace Foundations

/-- The dyadic kernel, extended by zero off the unit square. -/
noncomputable def dyadicKernel (J : ℕ) (x y : ℝ) : ℝ :=
  (2:ℝ)^J * ∑ k ∈ Finset.range (2^J), dyadicIndicator J k x * dyadicIndicator J k y

/-- The finite-cell definition agrees with the floor formula on [0,1)². -/
theorem dyadicKernel_eq_floor (J : ℕ) {x y : ℝ} (hx : x ∈ Ico (0:ℝ) 1)
    (hy : y ∈ Ico (0:ℝ) 1) :
    dyadicKernel J x y = if ⌊(2:ℝ)^J*x⌋₊ = ⌊(2:ℝ)^J*y⌋₊ then (2:ℝ)^J else 0 := by
  have hxk : x ∈ dyadicCell J ⌊(2:ℝ)^J*x⌋₊ := (mem_dyadicCell_iff_floor J _ hx.1).mpr rfl
  unfold dyadicKernel
  rw [Finset.sum_eq_single ⌊(2:ℝ)^J*x⌋₊]
  · simp only [dyadicIndicator_apply, if_pos hxk, one_mul, mem_dyadicCell_iff_floor J _ hy.1]
    by_cases he : ⌊(2:ℝ)^J*x⌋₊ = ⌊(2:ℝ)^J*y⌋₊
    · simp only [if_pos he, if_pos he.symm, mul_one]
    · simp only [if_neg he, if_neg (Ne.symm he), mul_zero]
  · intro k hk hne
    have hnot : x ∉ dyadicCell J k := fun h => hne (dyadicCell_unique h hxk)
    simp [dyadicIndicator_apply, hnot]
  · intro hn
    exact (hn (Finset.mem_range.mpr (floor_dyadic_lt J hx))).elim

/-- The parent kernel and one Haar product give the two child kernels. -/
theorem haar_mul_refine (j k : ℕ) (x y : ℝ) :
    (2:ℝ)^j * (dyadicIndicator j k x * dyadicIndicator j k y) + haar j k x * haar j k y =
      (2:ℝ)^(j+1) * (dyadicIndicator (j+1) (2*k) x * dyadicIndicator (j+1) (2*k) y +
        dyadicIndicator (j+1) (2*k+1) x * dyadicIndicator (j+1) (2*k+1) y) := by
  have hs := Real.sq_sqrt (show 0 ≤ (2:ℝ)^j by positivity)
  rw [dyadicIndicator_refine j k x, dyadicIndicator_refine j k y]
  unfold haar
  rw [show Real.sqrt ((2:ℝ)^j) * (dyadicIndicator (j+1) (2*k) x - dyadicIndicator (j+1) (2*k+1) x) *
      (Real.sqrt ((2:ℝ)^j) * (dyadicIndicator (j+1) (2*k) y - dyadicIndicator (j+1) (2*k+1) y)) =
      (Real.sqrt ((2:ℝ)^j))^2 * ((dyadicIndicator (j+1) (2*k) x - dyadicIndicator (j+1) (2*k+1) x) *
      (dyadicIndicator (j+1) (2*k) y - dyadicIndicator (j+1) (2*k+1) y)) by ring, hs, pow_succ]
  ring

/-- The one-level kernel increment. -/
theorem haar_mul_haar_eq_sum_kernel_sub (J : ℕ) (x y : ℝ) :
    ∑ k ∈ Finset.range (2^J), haar J k x * haar J k y =
      dyadicKernel (J+1) x y - dyadicKernel J x y := by
  have h := Finset.sum_congr (s₁ := Finset.range (2^J)) rfl (fun k _ => haar_mul_refine J k x y)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  unfold dyadicKernel
  rw [pow_succ (2:ℕ), Nat.mul_comm, sum_range_two_mul, Finset.sum_add_distrib]
  linarith

/-- The reproducing identity including the constant indicator, on all of ℝ². -/
theorem indicator_add_sum_haar_mul_eq_dyadicKernel (J : ℕ) (x y : ℝ) :
    dyadicIndicator 0 0 x * dyadicIndicator 0 0 y +
      ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range (2^j), haar j k x * haar j k y =
      dyadicKernel J x y := by
  induction J with
  | zero => simp [dyadicKernel]
  | succ J ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih, haar_mul_haar_eq_sum_kernel_sub]
    ring

/-- The requested reproducing identity on the half-open unit square. -/
theorem one_add_sum_haar_mul_eq_dyadicKernel (J : ℕ) {x y : ℝ}
    (hx : x ∈ Ico (0:ℝ) 1) (hy : y ∈ Ico (0:ℝ) 1) :
    1 + ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range (2^j), haar j k x * haar j k y =
      dyadicKernel J x y := by
  simpa only [dyadicIndicator_zero, if_pos hx, if_pos hy, one_mul] using
    indicator_add_sum_haar_mul_eq_dyadicKernel J x y

end Foundations
