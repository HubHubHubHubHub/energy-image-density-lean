import Foundations.GaussianSeries.Existence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

namespace Foundations

/-- The compact time interval, compatible with the local Brownian API. -/
abbrev WienerTime := Set.Icc (0 : ℝ≥0) 1

/-- Real continuous paths with the uniform norm. -/
abbrev PathSpace := C(WienerTime, ℝ)

instance : MeasurableSpace PathSpace := borel PathSpace
instance : BorelSpace PathSpace := ⟨rfl⟩

/-- Schauder basis functions as elements of the path Banach space. -/
noncomputable def schauderPath (i : SchauderIndex) : PathSpace :=
  ⟨fun t => schauderCoefficient i t, (continuous_schauderCoefficient i).comp continuous_subtype_val⟩

/-- Finite rank approximation to the coefficient-to-path map. -/
noncomputable def schauderPartial (N : ℕ) (ξ : SchauderIndex → ℝ) : PathSpace :=
  ∑ i ∈ schauderIndices N, ξ i • schauderPath i

@[simp] theorem schauderPartial_apply (N : ℕ) (ξ : SchauderIndex → ℝ) (t : WienerTime) :
    schauderPartial N ξ t =
      gaussianSeriesPartial (fun i ω => ω i) schauderCoefficient schauderIndices N t ξ := by
  simp [schauderPartial, schauderPath, gaussianSeriesPartial]

theorem continuous_schauderPartial (N : ℕ) : Continuous (schauderPartial N) := by
  unfold schauderPartial
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

/-- Exactly the set where the partial sums are Cauchy in the uniform norm. -/
def schauderGoodSet : Set (SchauderIndex → ℝ) :=
  {ξ | CauchySeq (fun N => schauderPartial N ξ)}

theorem mem_schauderGoodSet_iff (ξ : SchauderIndex → ℝ) :
    ξ ∈ schauderGoodSet ↔ ∃ f : PathSpace, Tendsto (fun N => schauderPartial N ξ) atTop (𝓝 f) :=
  cauchySeq_tendsto_of_complete |> fun h => ⟨h, fun ⟨_, hf⟩ => hf.cauchySeq⟩

theorem measurableSet_schauderGoodSet : MeasurableSet schauderGoodSet := by
  simp_rw [show schauderGoodSet = {ξ | ∃ f : PathSpace,
    Tendsto (fun N => schauderPartial N ξ) atTop (𝓝 f)} from
      Set.ext mem_schauderGoodSet_iff]
  exact measurableSet_exists_tendsto (fun N => (continuous_schauderPartial N).measurable)

/-- The canonical process is extended constantly after time one. -/
noncomputable def canonicalProcess (t : ℝ≥0) (ω : PathSpace) : ℝ :=
  ω ⟨min t 1, zero_le, min_le_right _ _⟩

@[simp] theorem canonicalProcess_apply (t : WienerTime) (ω : PathSpace) :
    canonicalProcess t ω = ω t := by
  simp [canonicalProcess, min_eq_left t.property.2]

theorem continuous_canonicalProcess (t : ℝ≥0) : Continuous (canonicalProcess t) :=
  continuous_eval_const _

theorem continuous_canonicalPath (ω : PathSpace) : Continuous (fun t => canonicalProcess t ω) :=
  ω.continuous.comp ((continuous_id.min continuous_const).subtype_mk _)

end Foundations
