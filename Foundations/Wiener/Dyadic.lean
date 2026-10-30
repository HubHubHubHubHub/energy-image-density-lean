import Foundations.Haar.Schauder

open Set

namespace Foundations

/-- Refinement of dyadic grid points. -/
theorem dyadic_grid_refine {j l : ℕ} (h : j ≤ l) (n : ℕ) :
    (n : ℝ) / 2^j = ((n * 2^(l-j) : ℕ) : ℝ) / 2^l := by
  have hp : (2 : ℝ)^l = 2^j * 2^(l-j) := by rw [← pow_add, Nat.add_sub_of_le h]
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hp]
  field_simp

/-- Tents vanish at integer grid points of their own level. -/
theorem tent_grid_zero {d : ℝ} (hd : 0 < d) (n r : ℕ) :
    tent ((n : ℝ)/d) (((n : ℝ)+1)/d) ((r : ℝ)/d) = 0 := by
  rw [tent, max_eq_left_iff]
  by_cases h : r ≤ n
  · exact (min_le_left _ _).trans (sub_nonpos.mpr ((div_le_div_iff_of_pos_right hd).mpr
      (by exact_mod_cast h)))
  · exact (min_le_right _ _).trans (sub_nonpos.mpr ((div_le_div_iff_of_pos_right hd).mpr
      (by exact_mod_cast (show n+1 ≤ r by omega))))

/-- Every finer Schauder tent vanishes on a coarser dyadic grid. -/
theorem schauder_dyadic_zero {j l : ℕ} (h : j ≤ l) (n r : ℕ) :
    schauder l n ((r : ℝ)/2^j) = 0 := by
  rw [schauder_eq, dyadic_grid_refine h r,
    tent_grid_zero (pow_pos (by norm_num : (0:ℝ)<2) l), mul_zero]

/-- A tent is a second difference of positive-part ramps. -/
theorem tent_eq_positiveRamps {a m b : ℝ} (hab : a ≤ b) (hm : 2*m=a+b) (t : ℝ) :
    tent a b t = max 0 (t-a) - 2*max 0 (t-m) + max 0 (t-b) := by
  unfold tent
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- A ramp with a grid breakpoint is affine on each grid cell. -/
theorem ramp_dyadic_secondDifference (j k r : ℕ) :
    2 * max 0 ((((k:ℝ)+1/2)/2^j) - (r:ℝ)/2^j) -
      max 0 ((k:ℝ)/2^j - (r:ℝ)/2^j) -
      max 0 ((((k:ℝ)+1)/2^j) - (r:ℝ)/2^j) = 0 := by
  have hd : (0:ℝ) < 2^j := by positivity
  by_cases h : r ≤ k
  · have hk : (r:ℝ) ≤ k := by exact_mod_cast h
    have ha : 0 ≤ (k:ℝ)/2^j - (r:ℝ)/2^j := sub_nonneg.mpr ((div_le_div_iff_of_pos_right hd).mpr hk)
    have hm : 0 ≤ ((k:ℝ)+1/2)/2^j - (r:ℝ)/2^j :=
      sub_nonneg.mpr ((div_le_div_iff_of_pos_right hd).mpr (by linarith))
    have hb : 0 ≤ ((k:ℝ)+1)/2^j - (r:ℝ)/2^j :=
      sub_nonneg.mpr ((div_le_div_iff_of_pos_right hd).mpr (by linarith))
    rw [max_eq_right ha, max_eq_right hm, max_eq_right hb]
    ring
  · have hk : (k:ℝ)+1 ≤ r := by exact_mod_cast (show k+1 ≤ r by omega)
    have ha : (k:ℝ)/2^j - (r:ℝ)/2^j ≤ 0 :=
      sub_nonpos.mpr ((div_le_div_iff_of_pos_right hd).mpr (by linarith))
    have hm : ((k:ℝ)+1/2)/2^j - (r:ℝ)/2^j ≤ 0 :=
      sub_nonpos.mpr ((div_le_div_iff_of_pos_right hd).mpr (by linarith))
    have hb : ((k:ℝ)+1)/2^j - (r:ℝ)/2^j ≤ 0 :=
      sub_nonpos.mpr ((div_le_div_iff_of_pos_right hd).mpr hk)
    rw [max_eq_left ha, max_eq_left hm, max_eq_left hb]
    ring

/-- Coarser tents are affine on a dyadic cell at a finer level. -/
theorem schauder_coarse_secondDifference {l j : ℕ} (h : l < j) (n k : ℕ) :
    2 * schauder l n (((k:ℝ)+1/2)/2^j) - schauder l n ((k:ℝ)/2^j) -
      schauder l n (((k:ℝ)+1)/2^j) = 0 := by
  have hd : (0:ℝ) < 2^l := by positivity
  have hab : (n:ℝ)/2^l ≤ ((n:ℝ)+1)/2^l := (div_le_div_iff_of_pos_right hd).mpr (by linarith)
  have hmid : 2 * (((2*n+1:ℕ):ℝ)/2^(l+1)) = (n:ℝ)/2^l + ((n:ℝ)+1)/2^l := by
    push_cast
    rw [pow_succ]
    ring
  simp_rw [schauder_eq, tent_eq_positiveRamps hab hmid]
  have ha := ramp_dyadic_secondDifference j k (n * 2^(j-l))
  have hm := ramp_dyadic_secondDifference j k ((2*n+1) * 2^(j-(l+1)))
  have hb := ramp_dyadic_secondDifference j k ((n+1) * 2^(j-l))
  rw [← dyadic_grid_refine (Nat.le_of_lt h) n] at ha
  rw [← dyadic_grid_refine h (2*n+1)] at hm
  rw [← dyadic_grid_refine (Nat.le_of_lt h) (n+1), Nat.cast_add, Nat.cast_one] at hb
  linear_combination Real.sqrt (2^l) * (ha - 2*hm + hb)

/-- The midpoint belongs to the next dyadic grid. -/
theorem dyadic_midpoint_grid (j k : ℕ) :
    ((k:ℝ)+1/2)/2^j = ((2*k+1:ℕ):ℝ)/2^(j+1) := by
  push_cast
  rw [pow_succ]
  ring

/-- The dyadic second-difference functionals are dual to the Schauder tents. -/
theorem schauder_secondDifference (j k l n : ℕ) :
    Real.sqrt ((2:ℝ)^j) *
      (2*schauder l n (((k:ℝ)+1/2)/2^j) - schauder l n ((k:ℝ)/2^j) -
        schauder l n (((k:ℝ)+1)/2^j)) = if l=j ∧ n=k then 1 else 0 := by
  classical
  rcases lt_trichotomy l j with h | h | h
  · rw [schauder_coarse_secondDifference h, mul_zero, if_neg (by omega)]
  · subst l
    have ha := schauder_dyadic_zero (le_refl j) n k
    have hb := schauder_dyadic_zero (le_refl j) n (k+1)
    simp only [Nat.cast_add, Nat.cast_one] at hb
    rw [ha, hb, sub_zero, sub_zero]
    by_cases hn : n=k
    · subst n
      rw [schauder_midpoint, if_pos ⟨rfl,rfl⟩]
      have hs : Real.sqrt ((2:ℝ)^j) ≠ 0 := by positivity
      field_simp
    · have hz : schauder j n (((k:ℝ)+1/2)/2^j) = 0 := by
        by_contra hne
        exact hn (schauder_level_unique hne (by rw [schauder_midpoint]; positivity))
      rw [hz, mul_zero, mul_zero, if_neg (by simp [hn])]
  · have ha := schauder_dyadic_zero (Nat.le_of_lt h) n k
    have hb := schauder_dyadic_zero (Nat.le_of_lt h) n (k+1)
    have hm := schauder_dyadic_zero h n (2*k+1)
    simp only [Nat.cast_add, Nat.cast_one] at hb
    rw [← dyadic_midpoint_grid] at hm
    rw [ha, hb, hm, mul_zero, sub_self, sub_self, mul_zero, if_neg (by omega)]

end Foundations
