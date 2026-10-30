import Foundations.GaussianSeries.LevelMax
import Mathlib.Analysis.Normed.Group.FunctionSeries

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal

namespace Foundations

variable {Ω : Type*}

/-- The finite sum at one Schauder level, defined for all real times. -/
noncomputable def schauderLevelSum (ξ : SchauderIndex → Ω → ℝ)
    (j : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ k : Fin (2^j), ξ (some ⟨j, k⟩) ω * schauder j k t

/--
The absolute value of a Schauder level sum is bounded by the level amplitude times the maximum
coefficient over `Fin (2^j)`.
-/
theorem abs_schauderLevelSum_le (ξ : SchauderIndex → Ω → ℝ)
    (j : ℕ) (t : ℝ) (ω : Ω) :
    |schauderLevelSum ξ j t ω| ≤ schauderLevelMax ξ j ω / (2 * Real.sqrt ((2:ℝ)^j)) := by
  classical
  let a : ℕ → ℝ := fun k => if h : k < 2^j then ξ (some ⟨j, ⟨k, h⟩⟩) ω else 0
  have he : schauderLevelSum ξ j t ω =
      ∑ k ∈ Finset.range (2^j), a k * schauder j k t := by
    rw [← Fin.sum_univ_eq_sum_range]
    unfold schauderLevelSum
    apply Finset.sum_congr rfl
    intro k hk
    simp [a, k.isLt]
  rw [he]
  apply sum_schauder_level_le_of_bound _ _ (schauderLevelMax_nonneg ξ j ω)
  intro k hk
  simpa [a, Finset.mem_range.mp hk] using
    abs_le_schauderLevelMax ξ j ⟨k, Finset.mem_range.mp hk⟩ ω

/-- The deterministic Weierstrass majorant. -/
noncomputable def schauderBound (j : ℕ) : ℝ := (j+1:ℝ) / Real.sqrt ((2:ℝ)^j)

theorem schauderBound_eq (j : ℕ) :
    schauderBound j = (j+1:ℝ) * (1 / Real.sqrt 2)^j := by
  have hs : Real.sqrt ((2:ℝ)^j) = (Real.sqrt 2)^j := by
    induction j with
    | zero => simp
    | succ j hj => rw [pow_succ, Real.sqrt_mul (by positivity), hj, pow_succ]
  rw [schauderBound, hs]
  simp [div_eq_mul_inv, inv_pow]

theorem summable_schauder_bound : Summable schauderBound := by
  have hr : ‖(1 / Real.sqrt 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one (by positivity)]
    exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hn : Summable (fun j : ℕ => (j:ℝ) * (1 / Real.sqrt 2)^j) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have hg : Summable (fun j : ℕ => (1 / Real.sqrt 2)^j) :=
    summable_geometric_of_norm_lt_one hr
  apply (hn.add hg).congr
  intro j
  rw [schauderBound_eq]
  ring

/-- Lévy--Ciesielski limit; the `tsum` is evaluated level by level. -/
noncomputable def schauderSeriesLimit (ξ : SchauderIndex → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ξ none ω * (t:ℝ) + ∑' j, schauderLevelSum ξ j t ω

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Uniform convergence of the level series on the entire real line, almost surely. -/
theorem ae_tendstoUniformly_schauder_levels {ξ : SchauderIndex → Ω → ℝ}
    (hLaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P) :
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun N t => ∑ j ∈ Finset.range N, schauderLevelSum ξ j t ω)
      (fun t => ∑' j, schauderLevelSum ξ j t ω) atTop := by
  filter_upwards [ae_eventually_schauderLevelMax_lt hLaw] with ω hω
  rw [← tendstoUniformlyOn_univ]
  apply tendstoUniformlyOn_tsum_nat_eventually summable_schauder_bound
  filter_upwards [hω] with j hj
  intro t ht
  rw [Real.norm_eq_abs]
  calc
    _ ≤ schauderLevelMax ξ j ω / (2 * Real.sqrt ((2:ℝ)^j)) :=
      abs_schauderLevelSum_le ξ j t ω
    _ ≤ (2 * (j+1:ℝ)) / (2 * Real.sqrt ((2:ℝ)^j)) :=
      div_le_div_of_nonneg_right hj.le (by positivity)
    _ = schauderBound j := by unfold schauderBound; field_simp

/-- Gaussian marginal laws imply almost-sure uniform convergence of the Haar–Schauder series. -/
theorem ae_tendstoUniformlyOn_schauder_series {ξ : SchauderIndex → Ω → ℝ}
    (hLaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn
      (fun N t => gaussianSeriesPartial ξ schauderCoefficient schauderIndices N t ω)
      (fun t => schauderSeriesLimit ξ t ω) atTop (Icc (0:ℝ≥0) 1) := by
  filter_upwards [ae_tendstoUniformly_schauder_levels hLaw] with ω hω
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp hω) ε hε
  filter_upwards [h] with N hN
  intro t ht
  simpa only [gaussianSeriesPartial_schauder, schauderSeriesLimit,
    schauderLevelSum, dist_add_left] using hN (t:ℝ)

end Foundations
