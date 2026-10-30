import GeometricMeasure.VectorMeasure.Domination
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Restriction, change of measurable coordinates, and addition of base measures. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GeometricMeasure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {m : ℕ}

theorem withDensityᵥ_restrict (ν : Measure X) {f : X → EuclideanSpace ℝ (Fin m)}
    (hf : Integrable f ν) {s : Set X} (hs : MeasurableSet s) :
    (ν.withDensityᵥ f).restrict s = (ν.restrict s).withDensityᵥ f := by
  apply VectorMeasure.ext
  intro t ht
  rw [VectorMeasure.restrict_apply _ hs ht, withDensityᵥ_apply hf (ht.inter hs),
    withDensityᵥ_apply hf.restrict ht, Measure.restrict_restrict ht]

theorem polarDensity_restrict (M : VectorMeasure X (EuclideanSpace ℝ (Fin m)))
    {s : Set X} (hs : MeasurableSet s) :
    polarDensity (M.restrict s) =ᵐ[M.variation.restrict s] polarDensity M := by
  have hi : Integrable (polarDensity M) (M.restrict s).variation := by
    rw [VectorMeasure.variation_restrict hs]
    exact (integrable_polarDensity M).restrict
  have hr : (M.restrict s).variation.withDensityᵥ (polarDensity M) = M.restrict s := by
    rw [VectorMeasure.variation_restrict hs, ← withDensityᵥ_restrict _
      (integrable_polarDensity M) hs, withDensityᵥ_polarDensity]
  simpa only [VectorMeasure.variation_restrict hs] using polarDensity_ae_eq _ hi hr

theorem withDensityᵥ_map_equiv (ν : Measure X) {f : X → EuclideanSpace ℝ (Fin m)}
    (hf : Integrable f ν) (e : X ≃ᵐ Y) :
    (ν.withDensityᵥ f).map e = (ν.map e).withDensityᵥ (f ∘ e.symm) := by
  have hi : Integrable (f ∘ e.symm) (ν.map e) :=
    (integrable_map_equiv e _).mpr (by simpa [Function.comp_def] using hf)
  apply VectorMeasure.ext
  intro t ht
  rw [VectorMeasure.map_apply _ e.measurable ht,
    withDensityᵥ_apply hf (e.measurable ht), withDensityᵥ_apply hi ht,
    setIntegral_map_equiv]
  simp only [Function.comp_apply, e.symm_apply_apply]

theorem polarDensity_map_equiv (M : VectorMeasure X (EuclideanSpace ℝ (Fin m)))
    (e : X ≃ᵐ Y) :
    polarDensity (M.map e) =ᵐ[M.variation.map e] (polarDensity M ∘ e.symm) := by
  have hi : Integrable (polarDensity M ∘ e.symm) (M.map e).variation := by
    rw [e.measurableEmbedding.variation_map]
    exact (integrable_map_equiv e _).mpr
      (by simpa [Function.comp_def] using integrable_polarDensity M)
  have hr : (M.map e).variation.withDensityᵥ (polarDensity M ∘ e.symm) = M.map e := by
    rw [e.measurableEmbedding.variation_map,
      ← withDensityᵥ_map_equiv _ (integrable_polarDensity M), withDensityᵥ_polarDensity]
  simpa only [e.measurableEmbedding.variation_map] using polarDensity_ae_eq _ hi hr

theorem variation_map_equiv_apply (M : VectorMeasure X (EuclideanSpace ℝ (Fin m)))
    (e : X ≃ᵐ Y) (s : Set Y) : (M.map e).variation s = M.variation (e ⁻¹' s) := by
  rw [e.measurableEmbedding.variation_map, e.map_apply]

theorem absolutelyContinuous_map_equiv_iff
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) (e : X ≃ᵐ Y) :
    M.map e ≪ᵥ (ν.map e).toENNRealVectorMeasure ↔ M ≪ᵥ ν.toENNRealVectorMeasure := by
  rw [absolutelyContinuous_iff_variation, absolutelyContinuous_iff_variation,
    e.measurableEmbedding.variation_map]
  constructor
  · intro h
    simpa only [e.map_symm_map] using e.symm.measurableEmbedding.absolutelyContinuous_map h
  · exact e.measurableEmbedding.absolutelyContinuous_map

theorem mutuallySingular_map_equiv_iff
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) (e : X ≃ᵐ Y) :
    M.map e ⟂ᵥ (ν.map e).toENNRealVectorMeasure ↔ M ⟂ᵥ ν.toENNRealVectorMeasure := by
  rw [mutuallySingular_iff_variation, mutuallySingular_iff_variation,
    e.measurableEmbedding.variation_map]
  constructor
  · intro h
    simpa only [e.map_symm_map] using e.symm.measurableEmbedding.mutuallySingular_map h
  · exact e.measurableEmbedding.mutuallySingular_map

/-- The spatial change of scale; negative nonzero scales are allowed. -/
def dilationEquiv {d : ℕ} (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) :
    EuclideanSpace ℝ (Fin d) ≃ᵐ EuclideanSpace ℝ (Fin d) :=
  (MeasurableEquiv.addRight (-x₀)).trans (MeasurableEquiv.smul₀ r⁻¹ (inv_ne_zero hr))

@[simp] theorem dilationEquiv_apply {d : ℕ} (x₀ : EuclideanSpace ℝ (Fin d))
    (r : ℝ) (hr : r ≠ 0) (x : EuclideanSpace ℝ (Fin d)) :
    dilationEquiv x₀ r hr x = r⁻¹ • (x - x₀) := rfl

@[simp] theorem dilationEquiv_symm_apply {d : ℕ} (x₀ : EuclideanSpace ℝ (Fin d))
    (r : ℝ) (hr : r ≠ 0) (y : EuclideanSpace ℝ (Fin d)) :
    (dilationEquiv x₀ r hr).symm y = x₀ + r • y := by
  simp [dilationEquiv, add_comm]

theorem polarDensity_map_dilation {d : ℕ}
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) :
    polarDensity (M.map (dilationEquiv x₀ r hr)) =ᵐ[
      M.variation.map (dilationEquiv x₀ r hr)] (fun y => polarDensity M (x₀ + r • y)) := by
  simpa only [Function.comp_def, dilationEquiv_symm_apply] using
    polarDensity_map_equiv M (dilationEquiv x₀ r hr)

theorem withDensityᵥ_add_measure (μ ν : Measure X)
    {f : X → EuclideanSpace ℝ (Fin m)} (hμ : Integrable f μ) (hν : Integrable f ν) :
    (μ + ν).withDensityᵥ f = μ.withDensityᵥ f + ν.withDensityᵥ f := by
  apply VectorMeasure.ext
  intro s hs
  rw [withDensityᵥ_apply (integrable_add_measure.mpr ⟨hμ, hν⟩) hs,
    add_apply, withDensityᵥ_apply hμ hs, withDensityᵥ_apply hν hs,
    Measure.restrict_add, integral_add_measure hμ.restrict hν.restrict]

/-- Null restrictions vanish, even without a measurability assumption on the set. -/
theorem restrict_eq_zero_of_variation_null
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) {s : Set X}
    (hs : M.variation s = 0) : M.restrict s = 0 := by
  apply VectorMeasure.variation_eq_zero.mp
  apply le_antisymm _ bot_le
  exact VectorMeasure.variation_restrict_le.trans_eq (Measure.restrict_zero_set hs)

end GeometricMeasure
