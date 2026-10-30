import Foundations.Sections.Isometry
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.InnerProductSpace.LinearMap

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Foundations
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Membership in a closed domain of L² has a measurable representative as an event. -/
theorem measurableSet_sectionLp_mem_closed {F : α × β → ℝ}
    (hF : MemLp F 2 (μ.prod ν)) {D : Set (Lp ℝ 2 μ)} (hD : IsClosed D) :
    ∃ Y : Set β, MeasurableSet Y ∧ {y | sectionLp μ F y ∈ D} =ᵐ[ν] Y := by
  borelize ↥(Lp ℝ 2 μ)
  let h := aestronglyMeasurable_sectionLp μ hF
  refine ⟨h.mk (sectionLp μ F) ⁻¹' D,
    hD.measurableSet.preimage h.stronglyMeasurable_mk.measurable, ?_⟩
  filter_upwards [h.ae_eq_mk] with y hy
  exact congrArg (fun z => z ∈ D) hy

theorem aemeasurable_lsc_sectionLp {F : α × β → ℝ}
    (hF : MemLp F 2 (μ.prod ν)) {Φ : Lp ℝ 2 μ → ℝ≥0∞} (hΦ : LowerSemicontinuous Φ) :
    AEMeasurable (fun y => Φ (sectionLp μ F y)) ν := by
  borelize ↥(Lp ℝ 2 μ)
  exact hΦ.measurable.comp_aemeasurable (aestronglyMeasurable_sectionLp μ hF).aemeasurable

theorem aestronglyMeasurable_clm_sectionLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) (T : Lp ℝ 2 μ →L[ℝ] G) :
    AEStronglyMeasurable (fun y => T (sectionLp μ F y)) ν :=
  T.continuous.comp_aestronglyMeasurable (aestronglyMeasurable_sectionLp μ hF)

theorem memLp_clm_sectionLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) (T : Lp ℝ 2 μ →L[ℝ] G) :
    MemLp (fun y => T (sectionLp μ F y)) 2 ν :=
  T.comp_memLp' (memLp_sectionLp μ ν hF)

omit [MeasurableSpace β] [IsFiniteMeasure μ] in
/-- Tensor formula, pointwise for the fixed representatives of the factors. -/
theorem sectionLp_tensor (u : Lp ℝ 2 μ) (v : β → ℝ) (y : β) :
    sectionLp μ (fun z => u z.1 * v z.2) y = v y • u := by
  have hf : MemLp (fun x => u x * v y) 2 μ := by
    convert (Lp.memLp u).const_smul (v y) using 1
    ext x
    simp [mul_comm]
  rw [sectionLp_of_memLp μ hf]
  apply Lp.ext
  filter_upwards [hf.coeFn_toLp, Lp.coeFn_smul (v y) u] with x hx hx'
  rw [hx, hx']
  simp [mul_comm]

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem memLp_tensor {u : α → ℝ} {v : β → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 ν) :
    MemLp (fun z => u z.1 * v z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq (hu.1.comp_fst.mul hv.1.comp_snd)).2
  simpa only [Pi.mul_apply, mul_pow] using hu.integrable_sq.mul_prod hv.integrable_sq

/-- Swapping the two variables gives the same construction in the other order. -/
def sectionLp_swap (F : α × β → ℝ) (x : α) : Lp ℝ 2 ν :=
  sectionLp ν (fun z => F z.swap) x

theorem memLp_sectionLp_swap {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    MemLp (sectionLp_swap ν F) 2 μ := by
  apply memLp_sectionLp ν μ
  exact (memLp_two_iff_integrable_sq hF.1.prod_swap).2 hF.integrable_sq.swap

/-- Inner-product Fubini follows from the class isometry. -/
theorem integral_inner_sectionLp (F G : Lp ℝ 2 (μ.prod ν)) :
    ∫ y, inner ℝ (sectionLp μ F y) (sectionLp μ G y) ∂ν = inner ℝ F G := by
  rw [← (sectionLpₗᵢ μ ν).inner_map_map F G, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_sectionLpₗᵢ μ ν F, coeFn_sectionLpₗᵢ μ ν G] with y hf hg
  rw [hf, hg]

end Foundations
