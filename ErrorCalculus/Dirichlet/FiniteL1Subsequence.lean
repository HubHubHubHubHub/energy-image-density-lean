import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic

/-!
# Common almost-everywhere subsequences and localization

## Main results
A finite family of L¹-convergent sequences has a common strictly increasing subsequence converging
almost everywhere. Absolute continuity can be glued from restrictions to an almost-everywhere
eventual cover. For a determinant, the complement of {det > 0} is {det ≤ 0}, including negative
values.
-/

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus

/-- One subsequence works simultaneously for a finite family of L¹ limits. -/
theorem exists_subseq_L1_finite_ae {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [Fintype ι] (a : ℕ → ι → Lp ℝ 1 μ) (b : ι → Lp ℝ 1 μ)
    (h : ∀ i, Tendsto (fun k => a k i) atTop (𝓝 (b i))) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ᵐ x ∂μ, ∀ i,
      Tendsto (fun k => a (s k) i x) atTop (𝓝 (b i x)) := by
  classical
  have H (I : Finset ι) : ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ i ∈ I,
      ∀ᵐ x ∂μ, Tendsto (fun k => a (s k) i x) atTop (𝓝 (b i x)) := by
    induction I using Finset.induction_on with
    | empty => exact ⟨id, strictMono_id, by simp⟩
    | @insert i I hi ih =>
      obtain ⟨s, hs, hsi⟩ := ih
      obtain ⟨t, ht, hti⟩ :=
        (tendstoInMeasure_of_tendsto_Lp ((h i).comp hs.tendsto_atTop)).exists_seq_tendsto_ae
      refine ⟨s ∘ t, hs.comp ht, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hti
      · exact (hsi j hj).mono (fun x hx => hx.comp ht.tendsto_atTop)
  obtain ⟨s, hs, hsi⟩ := H Finset.univ
  exact ⟨s, hs, ae_all_iff.mpr (fun i => hsi i (Finset.mem_univ i))⟩

/-- Gluing restricted measures along an a.e. eventual cover. This uses the whole
complement of each localization set, so negative determinants are allowed. -/
theorem absolutelyContinuous_of_ae_eventually_mem {α : Type*} [MeasurableSpace α]
    {ν η : Measure α} (A : ℕ → Set α) (hm : ∀ k, MeasurableSet (A k))
    (hc : ∀ k, ν.restrict (A k) ≪ η)
    (hA : ∀ᵐ x ∂ν, ∀ᶠ k : ℕ in atTop, x ∈ A k) : ν ≪ η := by
  intro B hB
  have hk (k : ℕ) : ∀ᵐ x ∂ν, x ∈ A k → x ∉ B :=
    (ae_restrict_iff' (hm k)).mp (measure_eq_zero_iff_ae_notMem.mp (hc k hB))
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_all_iff.mpr hk, hA] with x hx hax
  obtain ⟨k, hkm⟩ := hax.exists
  exact hx k hkm

/--
A negative determinant belongs to neither {det > 0} nor {det = 0}; the complement of the first set
is {det ≤ 0}.
-/
theorem negative_det_zero_remainder_counterexample :
    ¬ (Measure.dirac (0 : ℝ)) Set.univ ≤
      (Measure.dirac (0 : ℝ)) (Set.univ ∩ {y : ℝ | 0 < (-1 : ℝ)}) +
      (Measure.dirac (0 : ℝ)) {y : ℝ | (-1 : ℝ) = 0} := by
  norm_num

end ErrorCalculus
