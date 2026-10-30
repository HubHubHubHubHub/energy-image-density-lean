import Foundations.Haar.Schauder

/-!
# Integrated Kernel

## Main results
Finite integration of the reproducing kernel.
-/

open Set MeasureTheory
open scoped BigOperators Classical

namespace Foundations

/-- Pointwise finite-sum form of Mathlib's interval integrability lemma. -/
theorem intervalIntegrable_sum_apply {ι : Type*} (F : Finset ι) (f : ι → ℝ → ℝ)
    {s t : ℝ} (hf : ∀ i ∈ F, IntervalIntegrable (f i) volume s t) :
    IntervalIntegrable (fun x => ∑ i ∈ F, f i x) volume s t := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))


/-- Finite Haar expansions are integrable on every interval. -/
theorem intervalIntegrable_haar_expansion (J : ℕ) (c : ℝ) (a : ℕ → ℕ → ℝ) (s t : ℝ) :
    IntervalIntegrable (fun x => c * dyadicIndicator 0 0 x +
      ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range (2^j), a j k * haar j k x) volume s t := by
  apply ((integrable_dyadicIndicator 0 0).intervalIntegrable.const_mul c).add
  apply intervalIntegrable_sum_apply
  intro j _
  apply intervalIntegrable_sum_apply
  intro k _
  exact (integrable_haar j k).intervalIntegrable.const_mul (a j k)

/-- Term-by-term integration of a finite Haar expansion. -/
theorem integral_haar_expansion (J : ℕ) (c : ℝ) (a : ℕ → ℕ → ℝ) (t : ℝ) :
    (∫ x in (0:ℝ)..t, c * dyadicIndicator 0 0 x +
      ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range (2^j), a j k * haar j k x) =
    c * cellPrimitive 0 0 t +
      ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range (2^j), a j k * schauder j k t := by
  have hi (j : ℕ) : IntervalIntegrable
      (fun x => ∑ k ∈ Finset.range (2^j), a j k * haar j k x) volume 0 t := by
    exact intervalIntegrable_sum_apply _ _ (fun k _ =>
      (integrable_haar j k).intervalIntegrable.const_mul (a j k))
  rw [intervalIntegral.integral_add ((integrable_dyadicIndicator 0 0).intervalIntegrable.const_mul c)
    (intervalIntegrable_sum_apply _ _ (fun j _ => hi j))]
  rw [intervalIntegral.integral_finsetSum (fun j _ => hi j)]
  simp_rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (integrable_haar _ k).intervalIntegrable.const_mul (a _ k))]
  simp only [intervalIntegral.integral_const_mul, cellPrimitive, schauder]

/-- The partial covariance includes the constant Schauder function. -/
noncomputable def schauderSum (J : ℕ) (s t : ℝ) : ℝ :=
  s*t + ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range (2^j), schauder j k s * schauder j k t

/-- finite integration of the pointwise kernel identity (no limiting Fubini step). -/
theorem schauderSum_eq_integral_kernel (J : ℕ) {s t : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    schauderSum J s t = ∫ x in (0:ℝ)..s, ∫ y in (0:ℝ)..t, dyadicKernel J x y := by
  have hi (x : ℝ) : (∫ y in (0:ℝ)..t, dyadicKernel J x y) =
      cellPrimitive 0 0 t * dyadicIndicator 0 0 x +
        ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range (2^j), schauder j k t * haar j k x := by
    simp_rw [← indicator_add_sum_haar_mul_eq_dyadicKernel]
    rw [integral_haar_expansion]
    simp only [mul_comm]
  simp_rw [hi]
  rw [integral_haar_expansion, cellPrimitive_zero_unit hs, cellPrimitive_zero_unit ht]
  simp only [schauderSum, mul_comm]

/-- The double kernel integral is the sum of products of clipped cell lengths. -/
theorem integral_kernel_eq_cell_sum (J : ℕ) (s t : ℝ) :
    (∫ x in (0:ℝ)..s, ∫ y in (0:ℝ)..t, dyadicKernel J x y) =
    (2:ℝ)^J * ∑ k ∈ Finset.range (2^J), cellPrimitive J k s * cellPrimitive J k t := by
  have hi (x : ℝ) : (∫ y in (0:ℝ)..t, dyadicKernel J x y) =
      (2:ℝ)^J * ∑ k ∈ Finset.range (2^J), dyadicIndicator J k x * cellPrimitive J k t := by
    unfold dyadicKernel
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun k _ =>
      (integrable_dyadicIndicator J k).intervalIntegrable.const_mul (dyadicIndicator J k x))]
    simp only [intervalIntegral.integral_const_mul, cellPrimitive]
  simp_rw [hi]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun k _ =>
    (integrable_dyadicIndicator J k).intervalIntegrable.mul_const (cellPrimitive J k t))]
  simp only [intervalIntegral.integral_mul_const, cellPrimitive]

/-- The computable finite-cell expression for partial covariance. -/
theorem schauderSum_eq_cell_sum (J : ℕ) {s t : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    schauderSum J s t =
      (2:ℝ)^J * ∑ k ∈ Finset.range (2^J), cellPrimitive J k s * cellPrimitive J k t := by
  rw [schauderSum_eq_integral_kernel J hs ht, integral_kernel_eq_cell_sum]

end Foundations
