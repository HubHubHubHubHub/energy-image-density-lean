import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-! Coordinates and reconstruction of Euclidean vector measures by scalar RN derivatives.
The source is an arbitrary measurable space; the target always carries the Euclidean norm.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GeometricMeasure

variable {X : Type*} [MeasurableSpace X] {m : ℕ}

/-- A signed coordinate of a Euclidean vector measure. -/
def coord (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (i : Fin m) : SignedMeasure X :=
  M.mapRange (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).toLinearMap.toAddMonoidHom
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).continuous

@[simp] theorem coord_apply (M : VectorMeasure X (EuclideanSpace ℝ (Fin m)))
    (i : Fin m) (s : Set X) : coord M i s = M s i := rfl

@[simp] theorem coord_zero (i : Fin m) :
    coord (0 : VectorMeasure X (EuclideanSpace ℝ (Fin m))) i = 0 := by
  apply VectorMeasure.ext
  intro s hs
  simp

/-- Equality of every signed coordinate determines the vector measure. -/
theorem ext_of_coord_eq {M N : VectorMeasure X (EuclideanSpace ℝ (Fin m))}
    (h : ∀ i, coord M i = coord N i) : M = N := by
  apply VectorMeasure.ext
  intro s hs
  ext i
  exact congrArg (fun v : SignedMeasure X => v s) (h i)

/-- In dimension zero every vector measure vanishes. -/
theorem eq_zero_of_dimension_zero (M : VectorMeasure X (EuclideanSpace ℝ (Fin 0))) :
    M = 0 := by
  apply ext_of_coord_eq
  intro i
  exact Fin.elim0 i

/-- Projection preserves absolute continuity with respect to a positive measure. -/
theorem coord_absolutelyContinuous {M : VectorMeasure X (EuclideanSpace ℝ (Fin m))}
    {μ : Measure X} (h : M ≪ᵥ μ.toENNRealVectorMeasure) (i : Fin m) :
    coord M i ≪ᵥ μ.toENNRealVectorMeasure := by
  intro s hs
  simp only [coord_apply, h hs, PiLp.zero_apply]

/-- Each coordinate is absolutely continuous with respect to the intrinsic variation. -/
theorem coord_absolutelyContinuous_variation
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (i : Fin m) :
    coord M i ≪ᵥ M.variation.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro s hs hzero
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hzero
  have hM : M s = 0 := enorm_eq_zero.mp <|
    le_antisymm (hzero ▸ VectorMeasure.enorm_measure_le_variation M s) (zero_le)
  simp only [coord_apply, hM, PiLp.zero_apply]

/-- The Euclidean vector assembled from the scalar RN derivatives. -/
def rnDensity (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (μ : Measure X) :
    X → EuclideanSpace ℝ (Fin m) :=
  fun x => WithLp.toLp 2 (fun i => (coord M i).rnDeriv μ x)

@[simp] theorem rnDensity_apply (M : VectorMeasure X (EuclideanSpace ℝ (Fin m)))
    (μ : Measure X) (x : X) (i : Fin m) :
    rnDensity M μ x i = (coord M i).rnDeriv μ x := rfl

theorem measurable_rnDensity (M : VectorMeasure X (EuclideanSpace ℝ (Fin m)))
    (μ : Measure X) : Measurable (rnDensity M μ) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable.comp
    (measurable_pi_lambda _ (fun i => (coord M i).measurable_rnDeriv μ))

theorem integrable_rnDensity (M : VectorMeasure X (EuclideanSpace ℝ (Fin m)))
    (μ : Measure X) : Integrable (rnDensity M μ) μ := by
  apply integrable_piLp_iff.mpr
  intro i
  exact (coord M i).integrable_rnDeriv μ

/--
Reconstruction under coordinatewise absolute continuity relative to a sigma-finite measure;
no finiteness of variation is used.
-/
theorem withDensityᵥ_rnDensity (M : VectorMeasure X (EuclideanSpace ℝ (Fin m)))
    (μ : Measure X) [SigmaFinite μ]
    (h : ∀ i, coord M i ≪ᵥ μ.toENNRealVectorMeasure) :
    μ.withDensityᵥ (rnDensity M μ) = M := by
  apply VectorMeasure.ext
  intro s hs
  rw [withDensityᵥ_apply (integrable_rnDensity M μ) hs]
  ext i
  rw [eval_integral_piLp (fun j => ((coord M j).integrable_rnDeriv μ).restrict)]
  change (∫ x in s, (coord M i).rnDeriv μ x ∂μ) = coord M i s
  rw [← withDensityᵥ_apply ((coord M i).integrable_rnDeriv μ) hs,
    (coord M i).withDensityᵥ_rnDeriv_eq μ (h i)]

/-- A sigma-finite common dominating measure yields a measurable integrable density. -/
theorem exists_density_of_coord_absolutelyContinuous
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (μ : Measure X) [SigmaFinite μ]
    (h : ∀ i, coord M i ≪ᵥ μ.toENNRealVectorMeasure) :
    ∃ f : X → EuclideanSpace ℝ (Fin m),
      Measurable f ∧ Integrable f μ ∧ μ.withDensityᵥ f = M :=
  ⟨rnDensity M μ, measurable_rnDensity M μ, integrable_rnDensity M μ,
    withDensityᵥ_rnDensity M μ h⟩

end GeometricMeasure
