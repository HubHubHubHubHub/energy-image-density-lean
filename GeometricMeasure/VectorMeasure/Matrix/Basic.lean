import GeometricMeasure.VectorMeasure.Lebesgue.Basic

/-!
# Matrix-valued measures with the Frobenius norm

This file contains the definitions and results of the development of
`GeometricMeasure.VectorMeasure.Matrix` that the main statements of the library (the head theorems
listed in the README of the repository) use, together with the basic API of their definitions.
`GeometricMeasure.VectorMeasure.Matrix` imports it and continues the development.

## Main definitions

* `MatrixSpace`: Real `d × d` matrices with the Frobenius norm, as a Euclidean space.
* `matrixReindex`: The linear isometry from `MatrixSpace d` onto `EuclideanSpace ℝ (Fin (d * d))`
  given by `finProdFinEquiv`.
* `matrixReindexed`: A matrix-valued vector measure, with values reindexed in `EuclideanSpace ℝ (Fin
  (d * d))`.
* `matrixPolarDensity`: The polar density of a matrix-valued vector measure, computed through
  `matrixReindexed`.
* `matrixRows`: Isometric currying of a Frobenius matrix into its Euclidean rows.
* `rowCLM`: The `i`-th row of a matrix, as a continuous linear map.
* `rowMeasure`: The `i`-th row of a matrix-valued vector measure.
* `rowInsertCLM`: Insert a vector as one row and set all other rows to zero.
* `stackRows`: Finite sums of row insertions give the inverse to taking rows.

## Main statements

* `norm_matrixPolarDensity_ae`: The matrix polar density of `N` has Frobenius norm `1` almost
  everywhere with respect to `N.variation`.
* `variation_rowMeasure_le`: The variation of each row measure `rowMeasure N i` is at most
  `N.variation`.
* `eq_zero_of_matrix_dimension_zero`: Every vector measure with values in `MatrixSpace 0` is zero.
* `rowMeasure_stackRows`: The `i`-th row measure of `stackRows R` is `R i`.
* `polarDensity_rowMeasure`: The polar density of `rowMeasure N i` is, `(rowMeasure N
  i).variation`-almost everywhere, the normalized `i`-th row of `matrixPolarDensity N`.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace GeometricMeasure

variable {X : Type*} [MeasurableSpace X]

section LinearMaps

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem variation_mapRange_linearIsometryEquiv (N : VectorMeasure X E) (L : E ≃ₗᵢ[ℝ] F) :
    (N.mapRange L.toLinearEquiv.toLinearMap.toAddMonoidHom L.continuous).variation =
      N.variation := by
  unfold VectorMeasure.variation
  congr 1
  funext s
  exact L.enorm_map (N s)

theorem withDensityᵥ_mapRange [CompleteSpace E] [CompleteSpace F]
    (ν : Measure X) {f : X → E} (hf : Integrable f ν) (L : E →L[ℝ] F) :
    (ν.withDensityᵥ f).mapRange L.toLinearMap.toAddMonoidHom L.continuous =
      ν.withDensityᵥ (fun x => L (f x)) := by
  apply VectorMeasure.ext
  intro s hs
  rw [VectorMeasure.mapRange_apply, withDensityᵥ_apply hf hs,
    withDensityᵥ_apply (L.integrable_comp hf) hs]
  exact (L.integral_comp_comm hf.restrict).symm

end LinearMaps

/-- Real `d × d` matrices with the Frobenius norm, as a Euclidean space. -/
abbrev MatrixSpace (d : ℕ) := EuclideanSpace ℝ (Fin d × Fin d)

/-- The linear isometry from `MatrixSpace d` onto `EuclideanSpace ℝ (Fin (d * d))` given by
`finProdFinEquiv`. -/
def matrixReindex (d : ℕ) :
    MatrixSpace d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d * d)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finProdFinEquiv

/-- A matrix-valued vector measure, with values reindexed in `EuclideanSpace ℝ (Fin (d * d))`. -/
def matrixReindexed {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    VectorMeasure X (EuclideanSpace ℝ (Fin (d * d))) :=
  N.mapRange (matrixReindex d).toLinearEquiv.toLinearMap.toAddMonoidHom
    (matrixReindex d).continuous

@[simp] theorem matrixReindexed_apply {d : ℕ} (N : VectorMeasure X (MatrixSpace d))
    (s : Set X) : matrixReindexed N s = matrixReindex d (N s) := rfl

theorem variation_matrixReindexed {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    (matrixReindexed N).variation = N.variation :=
  variation_mapRange_linearIsometryEquiv N (matrixReindex d)

instance isFiniteMeasure_variation_matrix {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    IsFiniteMeasure N.variation := by
  rw [← variation_matrixReindexed N]
  infer_instance

/-- The polar density of a matrix-valued vector measure, computed through `matrixReindexed`. -/
def matrixPolarDensity {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) : X → MatrixSpace d :=
  fun x => (matrixReindex d).symm (polarDensity (matrixReindexed N) x)

theorem measurable_matrixPolarDensity {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    Measurable (matrixPolarDensity N) :=
  (matrixReindex d).symm.continuous.measurable.comp (measurable_polarDensity _)

theorem integrable_matrixPolarDensity {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    Integrable (matrixPolarDensity N) N.variation := by
  rw [← variation_matrixReindexed N]
  exact (matrixReindex d).symm.toLinearIsometry.toContinuousLinearMap.integrable_comp (integrable_polarDensity _)

theorem withDensityᵥ_matrixPolarDensity {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    N.variation.withDensityᵥ (matrixPolarDensity N) = N := by
  apply VectorMeasure.ext
  intro s hs
  rw [withDensityᵥ_apply (integrable_matrixPolarDensity N) hs]
  change (∫ x in s, (matrixReindex d).symm.toLinearIsometry.toContinuousLinearMap
    (polarDensity (matrixReindexed N) x)
    ∂N.variation) = N s
  rw [← variation_matrixReindexed N,
    (matrixReindex d).symm.toLinearIsometry.toContinuousLinearMap.integral_comp_comm
      (integrable_polarDensity (matrixReindexed N)).restrict]
  have h := congrArg (fun v : VectorMeasure X (EuclideanSpace ℝ (Fin (d * d))) => v s)
    (withDensityᵥ_polarDensity (matrixReindexed N))
  rw [withDensityᵥ_apply (integrable_polarDensity _) hs] at h
  rw [h]
  exact (matrixReindex d).symm_apply_apply (N s)

theorem norm_matrixPolarDensity_ae {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    ∀ᵐ x ∂N.variation, ‖matrixPolarDensity N x‖ = 1 := by
  rw [← variation_matrixReindexed N]
  simpa only [matrixPolarDensity, LinearIsometryEquiv.norm_map] using
    norm_polarDensity_ae (matrixReindexed N)

/-- Isometric currying of a Frobenius matrix into its Euclidean rows. -/
def matrixRows (d : ℕ) :
    MatrixSpace d ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin d => EuclideanSpace ℝ (Fin d)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.sigmaEquivProd (Fin d) (Fin d)).symm).trans
    (LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : Fin d) (_ : Fin d) => ℝ))

/-- The `i`-th row of a matrix, as a continuous linear map. -/
def rowCLM {d : ℕ} (i : Fin d) : MatrixSpace d →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => EuclideanSpace ℝ (Fin d)) i).comp
    (matrixRows d).toLinearIsometry.toContinuousLinearMap

@[simp] theorem rowCLM_apply {d : ℕ} (i j : Fin d) (P : MatrixSpace d) :
    rowCLM i P j = P (i, j) := rfl

theorem norm_rowCLM_le {d : ℕ} (i : Fin d) (P : MatrixSpace d) : ‖rowCLM i P‖ ≤ ‖P‖ := by
  change ‖(matrixRows d P) i‖ ≤ ‖P‖
  simpa only [LinearIsometryEquiv.norm_map] using PiLp.norm_apply_le (matrixRows d P) i

/-- The `i`-th row of a matrix-valued vector measure. -/
def rowMeasure {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) (i : Fin d) :
    VectorMeasure X (EuclideanSpace ℝ (Fin d)) :=
  N.mapRange (rowCLM i).toLinearMap.toAddMonoidHom (rowCLM i).continuous

@[simp] theorem rowMeasure_apply {d : ℕ} (N : VectorMeasure X (MatrixSpace d))
    (i : Fin d) (s : Set X) : rowMeasure N i s = rowCLM i (N s) := rfl

theorem rowMeasure_eq_withDensityᵥ {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) (i : Fin d) :
    rowMeasure N i = N.variation.withDensityᵥ (fun x => rowCLM i (matrixPolarDensity N x)) := by
  unfold rowMeasure
  conv_lhs => rw [← withDensityᵥ_matrixPolarDensity N]
  exact withDensityᵥ_mapRange _ (integrable_matrixPolarDensity N) (rowCLM i)

theorem variation_rowMeasure_le {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) (i : Fin d) :
    (rowMeasure N i).variation ≤ N.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro s _
  calc
    ‖rowMeasure N i s‖ₑ ≤ ‖N s‖ₑ := by
      simpa only [rowMeasure_apply, ← ofReal_norm] using ENNReal.ofReal_le_ofReal
        (norm_rowCLM_le i (N s))
    _ ≤ N.variation s := VectorMeasure.enorm_measure_le_variation N s

theorem eq_zero_of_matrix_dimension_zero (N : VectorMeasure X (MatrixSpace 0)) :
    N = 0 := by
  apply VectorMeasure.ext
  intro s _
  exact Subsingleton.elim _ _

/-- Insert a vector as one row and set all other rows to zero. -/
def rowInsertCLM {d : ℕ} (i : Fin d) : EuclideanSpace ℝ (Fin d) →L[ℝ] MatrixSpace d :=
  (matrixRows d).symm.toLinearIsometry.toContinuousLinearMap.comp
    (((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin d => EuclideanSpace ℝ (Fin d))).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin d => EuclideanSpace ℝ (Fin d)) i))

@[simp] theorem rowCLM_rowInsertCLM {d : ℕ} (i j : Fin d)
    (v : EuclideanSpace ℝ (Fin d)) : rowCLM i (rowInsertCLM j v) = if i = j then v else 0 := by
  change (Pi.single j v : Fin d → EuclideanSpace ℝ (Fin d)) i = _
  by_cases h : i = j
  · subst i; simp
  · simp [h]

/-- Finite sums of row insertions give the inverse to taking rows. -/
def stackRows {d : ℕ} (R : Fin d → VectorMeasure X (EuclideanSpace ℝ (Fin d))) :
    VectorMeasure X (MatrixSpace d) :=
  ∑ i : Fin d, (R i).mapRange (rowInsertCLM i).toLinearMap.toAddMonoidHom
    (rowInsertCLM i).continuous

@[simp] theorem stackRows_apply {d : ℕ}
    (R : Fin d → VectorMeasure X (EuclideanSpace ℝ (Fin d))) (s : Set X) :
    stackRows R s = ∑ i : Fin d, rowInsertCLM i (R i s) := by
  simp [stackRows]

@[simp] theorem rowMeasure_stackRows {d : ℕ}
    (R : Fin d → VectorMeasure X (EuclideanSpace ℝ (Fin d))) (i : Fin d) :
    rowMeasure (stackRows R) i = R i := by
  apply VectorMeasure.ext
  intro s _
  simp [rowMeasure_apply, stackRows_apply, map_sum, rowCLM_rowInsertCLM]

theorem polarDensity_rowMeasure {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) (i : Fin d) :
    polarDensity (rowMeasure N i) =ᵐ[(rowMeasure N i).variation]
      (fun x => ‖rowCLM i (matrixPolarDensity N x)‖⁻¹ • rowCLM i (matrixPolarDensity N x)) := by
  simpa only [rowMeasure_eq_withDensityᵥ] using
    polar_eq_normalize N.variation ((rowCLM i).integrable_comp (integrable_matrixPolarDensity N))

end GeometricMeasure
