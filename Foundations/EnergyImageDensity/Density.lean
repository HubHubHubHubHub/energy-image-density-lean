import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Density

## Main results
Comparison of densities and countable localization of absolute continuity.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Foundations

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- inclusion of zero sets compares two measurable densities. -/
theorem withDensity_absolutelyContinuous_of_zero_imp {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ x, g x = 0 → f x = 0) : μ.withDensity f ≪ μ.withDensity g := by
  intro s hs
  rw [withDensity_apply_eq_zero hf]
  apply measure_mono_null (show {x | f x ≠ 0} ∩ s ⊆ {x | g x ≠ 0} ∩ s from
    fun x hx => ⟨fun hgx => hx.1 (hfg x hgx), hx.2⟩)
  exact (withDensity_apply_eq_zero hg).mp hs

/-- pointwise domination by a scalar multiple also suffices, including infinite scalars. -/
theorem withDensity_absolutelyContinuous_of_le_mul {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {C : ℝ≥0∞} (hfg : ∀ x, f x ≤ C * g x) : μ.withDensity f ≪ μ.withDensity g := by
  apply withDensity_absolutelyContinuous_of_zero_imp hf hg
  intro x hx
  exact le_zero_iff.mp (by simpa [hx] using hfg x)

/-- a measure dominated by a sum inherits absolute continuity of all pushforwards. -/
theorem map_absolutelyContinuous_of_le_sum {ν : Measure α} {νs : ι → Measure α}
    {μ : Measure β} {u : α → β} (hu : Measurable u) (hν : ν ≤ Measure.sum νs)
    (h : ∀ i, (νs i).map u ≪ μ) : ν.map u ≪ μ := by
  apply (Measure.map_mono hν hu).absolutelyContinuous.trans
  rw [Measure.map_sum hu.aemeasurable]
  exact Measure.absolutelyContinuous_sum_left h

/-- countable localization does not require disjoint pieces. -/
theorem map_absolutelyContinuous_of_restrict_iUnion [Countable ι]
    {ν : Measure α} {μ : Measure β} {u : α → β} (hu : Measurable u)
    (s : ι → Set α) (h : ∀ i, (ν.restrict (s i)).map u ≪ μ) :
    (ν.restrict (⋃ i, s i)).map u ≪ μ :=
  map_absolutelyContinuous_of_le_sum hu Measure.restrict_iUnion_le h

/-- a density is supported on any set outside which it vanishes. -/
theorem withDensity_restrict_eq_self_of_zero_outside {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α}
    (hs : ∀ x, x ∉ s → f x = 0) : (μ.withDensity f).restrict s = μ.withDensity f := by
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_withDensity_iff hf]
  exact Filter.Eventually.of_forall fun x hx => by
    by_contra hxs
    exact hx (hs x hxs)

end Foundations
