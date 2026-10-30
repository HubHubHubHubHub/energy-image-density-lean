import Foundations.GaussianSeries.Tail
import Foundations.GaussianSeries.Schauder
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Normed

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Foundations

variable {Ω : Type*}

/-- Maximum of the absolute values of the coefficients at a fixed level. -/
noncomputable def schauderLevelMax (ξ : SchauderIndex → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  Finset.univ.sup' ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩
    (fun k : Fin (2^j) => |ξ (some ⟨j, k⟩) ω|)

theorem abs_le_schauderLevelMax (ξ : SchauderIndex → Ω → ℝ) (j : ℕ)
    (k : Fin (2^j)) (ω : Ω) : |ξ (some ⟨j, k⟩) ω| ≤ schauderLevelMax ξ j ω :=
  Finset.le_sup' (fun k : Fin (2^j) => |ξ (some ⟨j, k⟩) ω|) (Finset.mem_univ k)

theorem schauderLevelMax_nonneg (ξ : SchauderIndex → Ω → ℝ) (j : ℕ) (ω : Ω) :
    0 ≤ schauderLevelMax ξ j ω :=
  (abs_nonneg _).trans (abs_le_schauderLevelMax ξ j ⟨0, by positivity⟩ ω)

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Union bound; independence is not required. -/
theorem measure_schauderLevelMax_ge_le {ξ : SchauderIndex → Ω → ℝ}
    (hLaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P) (j : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    P {ω | x ≤ schauderLevelMax ξ j ω} ≤
      ENNReal.ofReal ((2:ℝ)^(j+1) * Real.exp (-x^2 / 2)) := by
  have hs : {ω | x ≤ schauderLevelMax ξ j ω} =
      ⋃ k : Fin (2^j), {ω | x ≤ |ξ (some ⟨j, k⟩) ω|} := by
    ext ω
    simp [schauderLevelMax, Finset.le_sup'_iff]
  rw [hs]
  calc
    _ ≤ ∑ k : Fin (2^j), P {ω | x ≤ |ξ (some ⟨j, k⟩) ω|} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin (2^j), ENNReal.ofReal (2 * Real.exp (-x^2 / 2)) :=
      Finset.sum_le_sum (fun k _ => gaussianReal_tail_le (hLaw _) hx)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      ring

/-- Summable bound for the level maximum at threshold `2 * (j + 1)`. -/
noncomputable def levelMaxBound (j : ℕ) : ℝ := (2:ℝ)^(j+1) * Real.exp (-2 * (j+1:ℝ)^2)

theorem levelMaxBound_nonneg (j : ℕ) : 0 ≤ levelMaxBound j := by
  unfold levelMaxBound
  positivity

/-- Domination by a geometric series with ratio `2 * exp (-2)`. -/
theorem levelMaxBound_le_geometric (j : ℕ) :
    levelMaxBound j ≤ (2 * Real.exp (-2))^(j+1) := by
  unfold levelMaxBound
  rw [mul_pow, ← Real.exp_nat_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  push_cast
  nlinarith [sq_nonneg (j:ℝ)]

theorem levelMax_ratio_lt_one : 2 * Real.exp (-2) < 1 := by
  rw [Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _)]
  have h := Real.add_one_le_exp (2:ℝ)
  linarith

theorem summable_levelMax_bound : Summable levelMaxBound := by
  have h := summable_geometric_of_lt_one
    (show 0 ≤ 2 * Real.exp (-2) by positivity) levelMax_ratio_lt_one
  have hs : Summable (fun j : ℕ => (2 * Real.exp (-2))^(j+1)) := by
    simpa only [pow_succ] using h.mul_right (2 * Real.exp (-2))
  exact Summable.of_nonneg_of_le levelMaxBound_nonneg levelMaxBound_le_geometric hs

/-- Borel--Cantelli: eventually all coefficients of level `j` are below `2(j+1)`. -/
theorem ae_eventually_schauderLevelMax_lt {ξ : SchauderIndex → Ω → ℝ}
    (hLaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P) :
    ∀ᵐ ω ∂P, ∀ᶠ j in atTop, schauderLevelMax ξ j ω < 2 * (j+1:ℝ) := by
  have hb (j : ℕ) : P {ω | 2 * (j+1:ℝ) ≤ schauderLevelMax ξ j ω} ≤
      ENNReal.ofReal (levelMaxBound j) := by
    have he : -(2 * (j+1:ℝ))^2 / 2 = -2 * (j+1:ℝ)^2 := by ring
    simpa only [levelMaxBound, he] using
      measure_schauderLevelMax_ge_le hLaw j (by positivity : 0 ≤ 2 * (j+1:ℝ))
  have hf : (∑' j : ℕ, P {ω | 2 * (j+1:ℝ) ≤ schauderLevelMax ξ j ω}) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum hb)
    rw [← ENNReal.ofReal_tsum_of_nonneg levelMaxBound_nonneg summable_levelMax_bound]
    exact ENNReal.ofReal_lt_top
  simpa only [Set.mem_setOf_eq, not_le] using ae_eventually_notMem hf

end Foundations
