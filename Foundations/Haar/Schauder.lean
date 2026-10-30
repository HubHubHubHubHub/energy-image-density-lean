import Foundations.Haar.Kernel
import Foundations.Haar.Tent
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Schauder

## Main results
Haar primitives and the Schauder tent functions.
-/

open Set MeasureTheory
open scoped BigOperators Classical

namespace Foundations

/-- The primitive of a cell indicator starting at zero. -/
noncomputable def cellPrimitive (j k : ℕ) (t : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..t, dyadicIndicator j k x

/-- The Schauder function is the actual interval integral of Haar. -/
noncomputable def schauder (j k : ℕ) (t : ℝ) : ℝ := ∫ x in (0:ℝ)..t, haar j k x

/-- bounded cells make their indicators integrable. -/
theorem integrable_dyadicIndicator (j k : ℕ) : Integrable (dyadicIndicator j k) :=
  (integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_const measure_Ico_lt_top.ne)

/-- Each Haar function is integrable on the real line. -/
theorem integrable_haar (j k : ℕ) : Integrable (haar j k) :=
  ((integrable_dyadicIndicator _ _).sub (integrable_dyadicIndicator _ _)).const_mul _

/-- The primitive is the length of a clipped cell, including negative times. -/
theorem cellPrimitive_eq (j k : ℕ) (t : ℝ) :
    cellPrimitive j k t = max 0 (min t (((k:ℝ)+1)/(2:ℝ)^j) - (k:ℝ)/(2:ℝ)^j) := by
  have ha : 0 ≤ (k:ℝ)/(2:ℝ)^j := by positivity
  by_cases ht : 0 ≤ t
  · rw [cellPrimitive, intervalIntegral.integral_of_le ht, ← integral_Ico_eq_integral_Ioc]
    simp only [dyadicIndicator, dyadicCell, integral_indicator_const _ measurableSet_Ico,
      measureReal_restrict_apply measurableSet_Ico, Ico_inter_Ico,
      max_eq_left ha, Real.volume_real_Ico, smul_eq_mul, mul_one]
    rw [min_comm, max_comm]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have hzero : cellPrimitive j k t = 0 := by
      unfold cellPrimitive
      apply intervalIntegral.integral_zero_ae
      have hae : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
      filter_upwards [hae] with x hx0
      intro hx
      rw [uIoc_of_ge ht'] at hx
      have hnot : x ∉ dyadicCell j k := by
        intro h
        have hxneg : x < 0 := lt_of_le_of_ne hx.2 hx0
        exact (not_le_of_gt hxneg) (ha.trans h.1)
      rw [dyadicIndicator_apply, if_neg hnot]
    rw [hzero, max_eq_left (by have := min_le_left t (((k:ℝ)+1)/(2:ℝ)^j); linarith)]

/-- The Schauder primitive is the difference of the half-cell primitives. -/
theorem schauder_eq_primitives (j k : ℕ) (t : ℝ) :
    schauder j k t = Real.sqrt ((2:ℝ)^j) *
      (cellPrimitive (j+1) (2*k) t - cellPrimitive (j+1) (2*k+1) t) := by
  simp only [schauder, haar, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub (integrable_dyadicIndicator _ _).intervalIntegrable
      (integrable_dyadicIndicator _ _).intervalIntegrable]
  rfl

/-- cell primitives are nonnegative. -/
theorem cellPrimitive_nonneg (j k : ℕ) (t : ℝ) : 0 ≤ cellPrimitive j k t := by
  rw [cellPrimitive_eq]; exact le_max_left _ _

/-- a clipped cell has length at most the cell width. -/
theorem cellPrimitive_le (j k : ℕ) (t : ℝ) : cellPrimitive j k t ≤ 1/(2:ℝ)^j := by
  rw [cellPrimitive_eq]
  apply max_le (by positivity)
  have h := min_le_right t (((k:ℝ)+1)/(2:ℝ)^j)
  have he : ((k:ℝ)+1)/(2:ℝ)^j - (k:ℝ)/(2:ℝ)^j = 1/(2:ℝ)^j := by ring
  linarith

/-- clipping is monotone in its time endpoint. -/
theorem cellPrimitive_mono (j k : ℕ) : Monotone (cellPrimitive j k) := by
  intro s t hst
  simp only [cellPrimitive_eq]
  exact max_le_max le_rfl (sub_le_sub_right (min_le_min hst le_rfl) _)

/-- a cell before the endpoint contributes its full length. -/
theorem cellPrimitive_eq_width {j k : ℕ} {t : ℝ}
    (ht : ((k:ℝ)+1)/(2:ℝ)^j ≤ t) : cellPrimitive j k t = 1/(2:ℝ)^j := by
  rw [cellPrimitive_eq, min_eq_right ht,
    show ((k:ℝ)+1)/(2:ℝ)^j - (k:ℝ)/(2:ℝ)^j = 1/(2:ℝ)^j by ring]
  exact max_eq_right (by positivity)

/-- a cell after the endpoint contributes zero. -/
theorem cellPrimitive_eq_zero {j k : ℕ} {t : ℝ}
    (ht : t ≤ (k:ℝ)/(2:ℝ)^j) : cellPrimitive j k t = 0 := by
  rw [cellPrimitive_eq]
  exact max_eq_left (by have := min_le_left t (((k:ℝ)+1)/(2:ℝ)^j); linarith)

/-- The explicit Schauder tent formula, valid at every real time. -/
theorem schauder_eq (j k : ℕ) (t : ℝ) :
    schauder j k t = Real.sqrt ((2:ℝ)^j) *
      tent ((k:ℝ)/(2:ℝ)^j) (((k:ℝ)+1)/(2:ℝ)^j) t := by
  rw [schauder_eq_primitives]
  simp only [cellPrimitive_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
  have hn : (2:ℝ)^j ≠ 0 := by positivity
  have hL : (2*(k:ℝ))/((2:ℝ)^j*2) = (k:ℝ)/(2:ℝ)^j := by field_simp
  have hR : (2*(k:ℝ)+1+1)/((2:ℝ)^j*2) = ((k:ℝ)+1)/(2:ℝ)^j := by field_simp; ring
  have hM : 2*((2*(k:ℝ)+1)/((2:ℝ)^j*2)) = (k:ℝ)/(2:ℝ)^j + ((k:ℝ)+1)/(2:ℝ)^j := by
    field_simp; ring
  rw [hL, hR, ← tent_eq_ramps (div_le_div_of_nonneg_right (by linarith) (by positivity)) hM]

/-- The Schauder functions are continuous. -/
theorem continuous_schauder (j k : ℕ) : Continuous (schauder j k) := by
  have he : schauder j k = fun t => Real.sqrt ((2:ℝ)^j) *
      tent ((k:ℝ)/(2:ℝ)^j) (((k:ℝ)+1)/(2:ℝ)^j) t := funext (schauder_eq j k)
  rw [he]
  exact continuous_const.mul (lipschitzWith_tent _ _).continuous

/-- Schauder functions are nonnegative. -/
theorem schauder_nonneg (j k : ℕ) (t : ℝ) : 0 ≤ schauder j k t := by
  rw [schauder_eq]; exact mul_nonneg (Real.sqrt_nonneg _) (tent_nonneg _ _ _)

/-- The normalization gives the exact claimed peak height. -/
theorem schauder_height (j k : ℕ) :
    Real.sqrt ((2:ℝ)^j) * ((((k:ℝ)+1)/(2:ℝ)^j - (k:ℝ)/(2:ℝ)^j)/2) =
      1/(2*Real.sqrt ((2:ℝ)^j)) := by
  have hs := Real.sq_sqrt (show 0 ≤ (2:ℝ)^j by positivity)
  have hn : (2:ℝ)^j ≠ 0 := by positivity
  have hr : Real.sqrt ((2:ℝ)^j) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The uniform bound 2^(-j/2-1), stated without real powers. -/
theorem schauder_le (j k : ℕ) (t : ℝ) :
    schauder j k t ≤ 1/(2*Real.sqrt ((2:ℝ)^j)) := by
  rw [schauder_eq, ← schauder_height j k]
  exact mul_le_mul_of_nonneg_left (tent_le
    (div_le_div_of_nonneg_right (by linarith) (by positivity)) t) (Real.sqrt_nonneg _)

/-- The peak is attained at the midpoint. -/
theorem schauder_midpoint (j k : ℕ) :
    schauder j k (((k:ℝ)+1/2)/(2:ℝ)^j) = 1/(2*Real.sqrt ((2:ℝ)^j)) := by
  rw [schauder_eq, show ((k:ℝ)+1/2)/(2:ℝ)^j =
    ((k:ℝ)/(2:ℝ)^j + ((k:ℝ)+1)/(2:ℝ)^j)/2 by ring,
    tent_midpoint (div_le_div_of_nonneg_right (by linarith) (by positivity)), schauder_height]

/-- The nonzero support lies in the parent cell (indeed in its interior). -/
theorem schauder_support {j k : ℕ} {t : ℝ} (ht : schauder j k t ≠ 0) : t ∈ dyadicCell j k := by
  rw [schauder_eq] at ht
  have htent := (tent_ne_zero_iff _ _ _).mp (mul_ne_zero_iff.mp ht).2
  exact ⟨htent.1.le, htent.2⟩

/-- At most one Schauder function at a level is nonzero. -/
theorem schauder_level_unique {j k l : ℕ} {t : ℝ}
    (hk : schauder j k t ≠ 0) (hl : schauder j l t ≠ 0) : k = l :=
  dyadicCell_unique (schauder_support hk) (schauder_support hl)

/-- The sharp slope bound, globally in time. -/
theorem schauder_lipschitz (j k : ℕ) (s t : ℝ) :
    |schauder j k t - schauder j k s| ≤ Real.sqrt ((2:ℝ)^j) * |t-s| := by
  rw [schauder_eq, schauder_eq, ← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using (lipschitzWith_tent
    ((k:ℝ)/(2:ℝ)^j) (((k:ℝ)+1)/(2:ℝ)^j)).norm_sub_le t s

/-- a coefficient bound controls a whole level, uniformly in time. -/
theorem sum_schauder_level_le_of_bound (j : ℕ) (a : ℕ → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ k ∈ Finset.range (2^j), |a k| ≤ A) (t : ℝ) :
    |∑ k ∈ Finset.range (2^j), a k * schauder j k t| ≤ A / (2*Real.sqrt ((2:ℝ)^j)) := by
  by_cases hex : ∃ k ∈ Finset.range (2^j), schauder j k t ≠ 0
  · obtain ⟨k, hk, hkt⟩ := hex
    have he : ∑ l ∈ Finset.range (2^j), a l * schauder j l t = a k * schauder j k t := by
      apply Finset.sum_eq_single k
      · intro l hl hlk
        have hz : schauder j l t = 0 := by
          by_contra hlt
          exact hlk (schauder_level_unique hlt hkt)
        simp [hz]
      · exact fun h => False.elim (h hk)
    rw [he, abs_mul, abs_of_nonneg (schauder_nonneg _ _ _), div_eq_mul_one_div]
    exact mul_le_mul (ha k hk) (schauder_le j k t) (schauder_nonneg _ _ _) hA
  · have hz : ∀ k ∈ Finset.range (2^j), schauder j k t = 0 := by simpa using hex
    have he : ∑ k ∈ Finset.range (2^j), a k * schauder j k t = 0 :=
      Finset.sum_eq_zero (fun k hk => by rw [hz k hk, mul_zero])
    rw [he, abs_zero]
    positivity

/-- The finite maximum of coefficients controls the level, for every real t. -/
theorem sum_schauder_level_le (j : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    |∑ k ∈ Finset.range (2^j), a k * schauder j k t| ≤
      (Finset.range (2^j)).sup' (⟨0, Finset.mem_range.mpr (by positivity)⟩) (fun k => |a k|) /
        (2*Real.sqrt ((2:ℝ)^j)) := by
  apply sum_schauder_level_le_of_bound
  · exact (abs_nonneg (a 0)).trans (Finset.le_sup' (fun k => |a k|)
      (Finset.mem_range.mpr (by positivity)))
  · intro k hk
    exact Finset.le_sup' (fun k => |a k|) hk

/-- all unit-interval Haar functions have mean zero. -/
theorem integral_haar_eq_zero (j k : ℕ) (hk : k < 2^j) :
    (∫ x in (0:ℝ)..1, haar j k x) = 0 := by
  change schauder j k 1 = 0
  by_contra h
  have hcell := (schauder_support h).2
  have hbound : ((k:ℝ)+1)/(2:ℝ)^j ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast (show k+1 ≤ 2^j by omega)
  linarith

/-- The square integral of each normalized Haar function equals one. -/
theorem integral_haar_sq (j k : ℕ) (hk : k < 2^j) :
    (∫ x in (0:ℝ)..1, (haar j k x)^2) = 1 := by
  simp_rw [haar_sq]
  rw [intervalIntegral.integral_const_mul]
  change (2:ℝ)^j * cellPrimitive j k 1 = 1
  rw [cellPrimitive_eq_width (by
    rw [div_le_one (by positivity)]
    exact_mod_cast (show k+1 ≤ 2^j by omega))]
  field_simp

/-- The constant function has primitive t on the closed unit interval. -/
theorem cellPrimitive_zero_unit {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    cellPrimitive 0 0 t = t := by
  simp [cellPrimitive_eq, min_eq_left ht.2, max_eq_right ht.1]

/-- clipped cell lengths add to t on the closed unit interval. -/
theorem sum_cellPrimitive (j : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ∑ k ∈ Finset.range (2^j), cellPrimitive j k t = t := by
  simp only [cellPrimitive]
  rw [← intervalIntegral.integral_finsetSum (fun k _ =>
    (integrable_dyadicIndicator j k).intervalIntegrable)]
  simp_rw [sum_dyadicIndicator]
  exact cellPrimitive_zero_unit ht

end Foundations
