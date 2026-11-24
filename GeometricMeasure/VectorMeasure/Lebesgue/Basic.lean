import GeometricMeasure.VectorMeasure.Operations.Basic

/-!
# The Lebesgue decomposition of vector measures

This file contains the definitions and results of the development of
`GeometricMeasure.VectorMeasure.Lebesgue` that the main statements of the library (the head theorems
listed in the README of the repository) use, together with the basic API of their definitions.
`GeometricMeasure.VectorMeasure.Lebesgue` imports it and continues the development.

## Main definitions

* `lebesgueACPart`: The absolutely continuous part of `M` with respect to `ν`: the polar density of
  `M` integrated against the absolutely continuous part of its variation.
* `lebesgueSingularPart`: The singular part of `M` with respect to `ν`: the polar density of `M`
  integrated against the singular part of its variation.
* `lebesgueACDensity`: The function `x ↦ (M.variation.rnDeriv ν x).toReal • polarDensity M x`.

## Main statements

* `integrable_polarDensity_lebesgueSingularMeasure`: The polar density of `M` is integrable with
  respect to `M.variation.singularPart ν`.
* `lebesgueACPart_absolutelyContinuous`: The part `lebesgueACPart M ν` is absolutely continuous with
  respect to `ν`.
* `lebesgueSingularPart_mutuallySingular`: The part `lebesgueSingularPart M ν` is mutually singular
  with `ν`.
* `lebesgueACPart_zero_right`: The absolutely continuous part of `M` with respect to the zero
  measure is zero.
* `lebesgueSingularPart_zero_right`: The singular part of `M` with respect to the zero measure is
  `M` itself.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GeometricMeasure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {m : ℕ}

/-- The absolutely continuous part of `M` with respect to `ν`: the polar density of `M` integrated
against the absolutely continuous part of its variation. -/
def lebesgueACPart (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    VectorMeasure X (EuclideanSpace ℝ (Fin m)) :=
  (ν.withDensity (M.variation.rnDeriv ν)).withDensityᵥ (polarDensity M)

/-- The singular part of `M` with respect to `ν`: the polar density of `M` integrated against the
singular part of its variation. -/
def lebesgueSingularPart (M : VectorMeasure X (EuclideanSpace ℝ (Fin m)))
    (ν : Measure X) : VectorMeasure X (EuclideanSpace ℝ (Fin m)) :=
  (M.variation.singularPart ν).withDensityᵥ (polarDensity M)

/-- The density `x ↦ (M.variation.rnDeriv ν x).toReal • polarDensity M x` of the absolutely
continuous part of `M` with respect to `ν`. -/
def lebesgueACDensity (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    X → EuclideanSpace ℝ (Fin m) :=
  fun x => (M.variation.rnDeriv ν x).toReal • polarDensity M x

theorem integrable_polarDensity_lebesgueACMeasure
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    Integrable (polarDensity M) (ν.withDensity (M.variation.rnDeriv ν)) :=
  (integrable_polarDensity M).mono_measure (M.variation.withDensity_rnDeriv_le ν)

theorem integrable_polarDensity_lebesgueSingularMeasure
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    Integrable (polarDensity M) (M.variation.singularPart ν) :=
  (integrable_polarDensity M).mono_measure (M.variation.singularPart_le ν)

theorem measurable_lebesgueACDensity
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    Measurable (lebesgueACDensity M ν) :=
  (M.variation.measurable_rnDeriv ν).ennreal_toReal.smul (measurable_polarDensity M)

theorem integrable_lebesgueACDensity
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    Integrable (lebesgueACDensity M ν) ν :=
  (integrable_withDensity_iff_integrable_smul' (M.variation.measurable_rnDeriv ν)
    (M.variation.rnDeriv_lt_top ν)).mp (integrable_polarDensity_lebesgueACMeasure M ν)

theorem withDensityᵥ_lebesgueACDensity
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    ν.withDensityᵥ (lebesgueACDensity M ν) = lebesgueACPart M ν :=
  withDensityᵥ_smul_eq_withDensityᵥ_withDensity'
    (M.variation.measurable_rnDeriv ν).aemeasurable (M.variation.rnDeriv_lt_top ν)
    (integrable_lebesgueACDensity M ν)

theorem lebesgueACPart_absolutelyContinuous
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    lebesgueACPart M ν ≪ᵥ ν.toENNRealVectorMeasure := by
  rw [← withDensityᵥ_lebesgueACDensity]
  exact withDensityᵥ_absolutelyContinuous_euclidean ν (integrable_lebesgueACDensity M ν)

theorem variation_lebesgueACPart
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    (lebesgueACPart M ν).variation = ν.withDensity (M.variation.rnDeriv ν) := by
  letI := isFiniteMeasure_of_le M.variation (M.variation.withDensity_rnDeriv_le ν)
  exact variation_withDensityᵥ_eq_of_norm_one _
    (measurable_polarDensity M).aestronglyMeasurable
    ((Measure.absolutelyContinuous_of_le (M.variation.withDensity_rnDeriv_le ν)).ae_le
      (norm_polarDensity_ae M))

theorem variation_lebesgueSingularPart
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    (lebesgueSingularPart M ν).variation = M.variation.singularPart ν := by
  letI := isFiniteMeasure_of_le M.variation (M.variation.singularPart_le ν)
  exact variation_withDensityᵥ_eq_of_norm_one _
    (measurable_polarDensity M).aestronglyMeasurable
    ((Measure.absolutelyContinuous_of_le (M.variation.singularPart_le ν)).ae_le
      (norm_polarDensity_ae M))

theorem lebesgueSingularPart_mutuallySingular
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    lebesgueSingularPart M ν ⟂ᵥ ν.toENNRealVectorMeasure := by
  rw [mutuallySingular_iff_variation, variation_lebesgueSingularPart]
  exact M.variation.mutuallySingular_singularPart ν

@[simp] theorem lebesgueACPart_zero (ν : Measure X) :
    lebesgueACPart (0 : VectorMeasure X (EuclideanSpace ℝ (Fin m))) ν = 0 := by
  apply VectorMeasure.variation_eq_zero.mp
  simp [variation_lebesgueACPart]

@[simp] theorem lebesgueSingularPart_zero (ν : Measure X) :
    lebesgueSingularPart (0 : VectorMeasure X (EuclideanSpace ℝ (Fin m))) ν = 0 := by
  apply VectorMeasure.variation_eq_zero.mp
  simp [variation_lebesgueSingularPart]

@[simp] theorem lebesgueACPart_zero_right
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) : lebesgueACPart M 0 = 0 := by
  apply VectorMeasure.variation_eq_zero.mp
  simp [variation_lebesgueACPart]

@[simp] theorem lebesgueSingularPart_zero_right
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) : lebesgueSingularPart M 0 = M := by
  simp [lebesgueSingularPart, withDensityᵥ_polarDensity]

end GeometricMeasure
