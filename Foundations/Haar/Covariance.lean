import Foundations.Haar.IntegratedKernel
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Covariance

## Main results
Covariance identity, with a sharp uniform error bound.
-/

open Set MeasureTheory Filter
open scoped BigOperators Classical Topology

namespace Foundations

/-- Only the cell containing s can contribute an error; its maximum is a quarter-cell square. -/
theorem cellPrimitive_remainder_le (J k : ℕ) {s t : ℝ} (hst : s ≤ t) :
    cellPrimitive J k s * (1/(2:ℝ)^J - cellPrimitive J k t) ≤
      (1/(2:ℝ)^J)^2 / 4 * dyadicIndicator J k s := by
  by_cases hm : s ∈ dyadicCell J k
  · rw [dyadicIndicator_apply, if_pos hm, mul_one]
    have hst' := cellPrimitive_mono J k hst
    have hp := mul_nonneg (cellPrimitive_nonneg J k s) (sub_nonneg.mpr hst')
    nlinarith [sq_nonneg (cellPrimitive J k s - (1/(2:ℝ)^J)/2)]
  · rw [dyadicIndicator_apply, if_neg hm, mul_zero]
    by_cases hsa : s ≤ (k:ℝ)/(2:ℝ)^J
    · rw [cellPrimitive_eq_zero hsa, zero_mul]
    · have hbs : ((k:ℝ)+1)/(2:ℝ)^J ≤ s := by
        by_contra h
        exact hm ⟨(lt_of_not_ge hsa).le, lt_of_not_ge h⟩
      rw [cellPrimitive_eq_width (hbs.trans hst), sub_self, mul_zero]

/-- The covariance deficit for ordered times is a sum of nonnegative cell remainders. -/
theorem sub_schauderSum_eq_remainder (J : ℕ) {s t : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    s - schauderSum J s t = (2:ℝ)^J * ∑ k ∈ Finset.range (2^J),
      cellPrimitive J k s * (1/(2:ℝ)^J - cellPrimitive J k t) := by
  have hn : (2:ℝ)^J * (1/(2:ℝ)^J) = 1 := by field_simp
  have htotal : (2:ℝ)^J * (∑ k ∈ Finset.range (2^J), cellPrimitive J k s * (1/(2:ℝ)^J)) = s := by
    rw [← Finset.sum_mul, sum_cellPrimitive J hs]
    calc (2:ℝ)^J * (s * (1/(2:ℝ)^J)) = s * ((2:ℝ)^J * (1/(2:ℝ)^J)) := by ring
         _ = s := by rw [hn, mul_one]
  rw [schauderSum_eq_cell_sum J hs ht]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, mul_sub, htotal]

/-- The deficit is between zero and one quarter of the dyadic cell width. -/
theorem sub_schauderSum_bounds (J : ℕ) {s t : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) (hst : s ≤ t) :
    0 ≤ s - schauderSum J s t ∧ s - schauderSum J s t ≤ 1/(4*(2:ℝ)^J) := by
  rw [sub_schauderSum_eq_remainder J hs ht]
  constructor
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (cellPrimitive_nonneg J k s)
      (sub_nonneg.mpr (cellPrimitive_le J k t)))
  · have hsum := Finset.sum_le_sum (s := Finset.range (2^J)) (fun k _ => cellPrimitive_remainder_le J k hst)
    rw [← Finset.mul_sum, sum_dyadicIndicator] at hsum
    have hI : dyadicIndicator 0 0 s ≤ 1 := by
      rw [dyadicIndicator_zero]; split_ifs <;> norm_num
    have hbound := mul_le_mul_of_nonneg_left hI (show 0 ≤ (1/(2:ℝ)^J)^2 / 4 by positivity)
    have h := mul_le_mul_of_nonneg_left (hsum.trans hbound) (show 0 ≤ (2:ℝ)^J by positivity)
    calc
      _ ≤ (2:ℝ)^J * ((1/(2:ℝ)^J)^2 / 4 * 1) := h
      _ = 1/(4*(2:ℝ)^J) := by field_simp

/-- Partial covariance is symmetric. -/
theorem schauderSum_comm (J : ℕ) (s t : ℝ) : schauderSum J s t = schauderSum J t s := by
  simp only [schauderSum, mul_comm]

/--
For s, t ∈ [0, 1], the error between the finite Haar–Schauder covariance and min(s, t) is at most
1/(4·2^J).
-/
theorem abs_schauderSum_sub_min_le_sharp (J : ℕ) {s t : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    |schauderSum J s t - min s t| ≤ 1/(4*(2:ℝ)^J) := by
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst, abs_sub_comm, abs_of_nonneg (sub_schauderSum_bounds J hs ht hst).1]
    exact (sub_schauderSum_bounds J hs ht hst).2
  · rw [schauderSum_comm, min_eq_right hts, abs_sub_comm,
      abs_of_nonneg (sub_schauderSum_bounds J ht hs hts).1]
    exact (sub_schauderSum_bounds J ht hs hts).2

/-- The requested uniform bound 2^(1-J). -/
theorem abs_schauderSum_sub_min_le (J : ℕ) {s t : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    |schauderSum J s t - min s t| ≤ 2/(2:ℝ)^J := by
  apply (abs_schauderSum_sub_min_le_sharp J hs ht).trans
  have hp : 0 < (2:ℝ)^J := by positivity
  apply (div_le_div_iff₀ (by positivity) hp).mpr
  nlinarith

/-- partial covariance converges to min(s,t) at every pair of unit-interval times. -/
theorem tendsto_schauderSum {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    Tendsto (fun J : ℕ => schauderSum J s t) atTop (𝓝 (min s t)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hg : Tendsto (fun J : ℕ => 2/(2:ℝ)^J) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1:ℝ)/2) (by norm_num) (by norm_num)
    simpa only [div_pow, one_pow, mul_one_div, mul_zero] using hp.const_mul (2:ℝ)
  apply squeeze_zero (fun _ => dist_nonneg) _ hg
  intro J
  simpa only [Real.dist_eq] using abs_schauderSum_sub_min_le J hs ht

/-- The nonnegative sums by level have the desired sum, excluding the constant term. -/
theorem hasSum_schauder_mul {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    HasSum (fun j : ℕ => ∑ k ∈ Finset.range (2^j), schauder j k s * schauder j k t)
      (min s t - s*t) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j => Finset.sum_nonneg (fun k _ =>
    mul_nonneg (schauder_nonneg j k s) (schauder_nonneg j k t))) _).mpr
  simpa only [schauderSum, add_sub_cancel_left] using
    (tendsto_schauderSum hs ht).sub (tendsto_const_nhds (x := s*t))

/-- The covariance identity in infinite-sum notation. -/
theorem schauder_covariance {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    s*t + ∑' j : ℕ, ∑ k ∈ Finset.range (2^j), schauder j k s * schauder j k t = min s t := by
  rw [(hasSum_schauder_mul hs ht).tsum_eq]
  ring

/-- The quarter-cell constant is attained already at J=0 and s=t=1/2. -/
theorem covariance_error_half :
    |schauderSum 0 (1/2) (1/2) - min (1/2:ℝ) (1/2)| = 1/4 := by
  norm_num [schauderSum]

/-- No coefficient below 1/4 works uniformly over all J and all unit-interval times. -/
theorem covariance_error_constant_optimal {C : ℝ}
    (hC : ∀ (J : ℕ) (s t : ℝ), s ∈ Icc (0:ℝ) 1 → t ∈ Icc (0:ℝ) 1 →
      |schauderSum J s t - min s t| ≤ C/(2:ℝ)^J) : 1/4 ≤ C := by
  have h := hC 0 (1/2) (1/2) (by norm_num) (by norm_num)
  simpa only [covariance_error_half, pow_zero, div_one] using h

end Foundations
