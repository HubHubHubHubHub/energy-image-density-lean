import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic

/-!
# minimum-norm point in a closed convex set (tool for BH I § 8.1)

## Main results
Projection of 0 onto a nonempty closed convex subset of a real Hilbert space: existence
(adapted from `exists_norm_eq_iInf_of_complete_convex`), the midpoint inequality, uniqueness, and
convergence
of the projections along a decreasing sequence of closed convex sets with bounded projection norms.
The last lemma is used for continuity from below of capacity (BH 1991, ch. I, prop. 8.1.3 c), p.
53).
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace ErrorCalculus.Capacity

/-! ## A. Projection of 0 onto a closed convex subset of a real Hilbert space -/
section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Existence of a minimum-norm point in a nonempty closed convex set (in a complete space). -/
theorem exists_min_norm [CompleteSpace E] {K : Set E} (hne : K.Nonempty) (hK : IsClosed K)
    (hc : Convex ℝ K) : ∃ e ∈ K, ∀ v ∈ K, ‖e‖ ≤ ‖v‖ := by
  obtain ⟨e, he, heq⟩ := exists_norm_eq_iInf_of_complete_convex hne hK.isComplete hc 0
  refine ⟨e, he, fun v hv => ?_⟩
  have hb : BddBelow (Set.range fun w : K => ‖(0 : E) - w‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have h := ciInf_le hb ⟨v, hv⟩
  rw [← heq] at h
  simpa using h

/-- Midpoint inequality: ‖v - e‖² ≤ 2 (‖v‖² - ‖e‖²) when e has minimum norm. -/
theorem norm_sub_sq_le_of_min {K : Set E} (hc : Convex ℝ K) {e v : E} (he : e ∈ K) (hv : v ∈ K)
    (hmin : ∀ w ∈ K, ‖e‖ ≤ ‖w‖) : ‖v - e‖ ^ 2 ≤ 2 * (‖v‖ ^ 2 - ‖e‖ ^ 2) := by
  have hm : (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • e ∈ K :=
    hc hv he (by norm_num) (by norm_num) (by norm_num)
  have h1 := hmin _ hm
  have h2 : (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • e = (1 / 2 : ℝ) • (v + e) := by rw [smul_add]
  have h3 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  rw [h2, norm_smul, h3] at h1
  have hpar := parallelogram_law_with_norm ℝ v e
  have h4 : ‖e‖ ^ 2 ≤ (1 / 2 * ‖v + e‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [norm_nonneg (v + e), norm_nonneg (v - e)]

/-- Uniqueness of the minimum-norm point. -/
theorem eq_of_norm_le_min {K : Set E} (hc : Convex ℝ K) {e v : E} (he : e ∈ K) (hv : v ∈ K)
    (hmin : ∀ w ∈ K, ‖e‖ ≤ ‖w‖) (hle : ‖v‖ ≤ ‖e‖) : v = e := by
  have h := norm_sub_sq_le_of_min hc he hv hmin
  have h2 : ‖v‖ ^ 2 ≤ ‖e‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  have h0 : ‖v - e‖ ^ 2 ≤ 0 := by linarith
  have h5 : ‖v - e‖ = 0 := by nlinarith [norm_nonneg (v - e)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h5)

/--
For a decreasing sequence of closed convex sets, the minimum-norm points converge to a point in the
intersection if their norms are bounded.
-/
theorem exists_tendsto_min_norm [CompleteSpace E] {K : ℕ → Set E} (hc : ∀ n, Convex ℝ (K n))
    (hcl : ∀ n, IsClosed (K n)) (hanti : Antitone K) {e : ℕ → E} (he : ∀ n, e n ∈ K n)
    (hmin : ∀ n, ∀ w ∈ K n, ‖e n‖ ≤ ‖w‖) {M : ℝ} (hM : ∀ n, ‖e n‖ ^ 2 ≤ M) :
    ∃ e' ∈ ⋂ n, K n, Tendsto e atTop (𝓝 e') := by
  set a : ℕ → ℝ := fun n => ‖e n‖ ^ 2 with ha
  have hmono : Monotone a := fun n m hnm =>
    pow_le_pow_left₀ (norm_nonneg _) (hmin n _ (hanti hnm (he m))) 2
  have hbdd : BddAbove (Set.range a) := ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ n, a n with hL
  have hkey : ∀ N n, N ≤ n → ‖e n - e N‖ ^ 2 ≤ 2 * (L - a N) := by
    intro N n hNn
    have h1 := norm_sub_sq_le_of_min (hc N) (he N) (hanti hNn (he n)) (hmin N)
    have h2 : a n ≤ L := le_ciSup hbdd n
    simp only [ha] at h1 h2 ⊢
    linarith
  have hdist : ∀ N n, N ≤ n → dist (e n) (e N) ≤ Real.sqrt (2 * (L - a N)) := by
    intro N n hNn
    rw [dist_eq_norm]
    have h := Real.abs_le_sqrt (hkey N n hNn)
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  have hcauchy : CauchySeq e := by
    refine cauchySeq_of_le_tendsto_0 (fun N => 2 * Real.sqrt (2 * (L - a N))) ?_ ?_
    · intro n m N hn hm
      calc dist (e n) (e m) ≤ dist (e n) (e N) + dist (e m) (e N) := dist_triangle_right _ _ _
        _ ≤ _ := by linarith [hdist N n hn, hdist N m hm]
    · have h : Tendsto (fun N => 2 * Real.sqrt (2 * (L - a N))) atTop
          (𝓝 (2 * Real.sqrt (2 * (L - L)))) :=
        (((hlim.const_sub L).const_mul 2).sqrt).const_mul 2
      simpa using h
  obtain ⟨e', he'⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨e', Set.mem_iInter.2 fun n => (hcl n).mem_of_tendsto he' ?_, he'⟩
  exact eventually_atTop.2 ⟨n, fun m hm => hanti hm (he m)⟩

end Hilbert

end ErrorCalculus.Capacity
