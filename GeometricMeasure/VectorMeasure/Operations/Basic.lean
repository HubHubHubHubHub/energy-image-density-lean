import GeometricMeasure.VectorMeasure.Domination
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Restriction and change of variables for vector measures

This file contains the definitions and results of the development of
`GeometricMeasure.VectorMeasure.Operations` that the main statements of the library (the head
theorems listed in the README of the repository) use, together with the basic API of their
definitions. `GeometricMeasure.VectorMeasure.Operations` imports it and continues the development.

## Main definitions

* `dilationEquiv`: The spatial change of scale; negative nonzero scales are allowed.

## Main statements

* `polarDensity_restrict`: For a measurable set `s`, the polar density of `M.restrict s` agrees
  `M.variation.restrict s`-a.e. with `polarDensity M`.
* `polarDensity_map_equiv`: The polar density of the pushforward `M.map e` along a measurable
  equivalence `e` agrees `M.variation.map e`-a.e. with `polarDensity M ∘ e.symm`.
-/
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

end GeometricMeasure
