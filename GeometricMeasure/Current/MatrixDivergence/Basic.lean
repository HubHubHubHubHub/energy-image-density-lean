import GeometricMeasure.Matrix.WaveCone
import GeometricMeasure.VectorMeasure.Matrix.Basic
import GeometricMeasure.Current.MeasureCurrent.Basic

/-!
# Frobenius coordinates and matrix divergence

This file contains the definitions and results of the development of
`GeometricMeasure.Current.MatrixDivergence` that the main statements of the library (the head
theorems listed in the README of the repository) use. `GeometricMeasure.Current.MatrixDivergence`
imports it and continues the development.

## Main definitions

* `matrixCoordinates`: Ordinary coordinates of an Frobenius matrix, preserving the index order; no
  isometry to an implicit norm.
* `HasMatrixMeasureDivergence`: Finite family of row-wise signed measure divergences in the
  distributional sense; no new vector measure is constructed.

## Main statements

* `matrixEuclideanCLM_matrixCoordinates`: The coordinate of Pξ is the real inner product of the
  corresponding row with ξ.

## References

Reference: De Philippis–Rindler, arXiv:1601.06543v2, pp. 2 and 15; Remark 1.3 and Corollary 1.13
provide the broader structure-theorem context.
-/
noncomputable section
open scoped Matrix
open WithLp
namespace GeometricMeasure
variable {n : ℕ}

/--
DPR p. 15. Ordinary coordinates of an Frobenius matrix, preserving the index order; no isometry to
an implicit norm.
-/
def matrixCoordinates (P : MatrixSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => P (i, j)

/-- DPR p. 15. Ordinary coordinates agree with row extraction. -/
theorem matrixCoordinates_row (P : MatrixSpace n) (i j : Fin n) :
    matrixCoordinates P i j = rowCLM i P j := rfl

/-- DPR p. 15. The coordinate of Pξ is the real inner product of the corresponding row with ξ. -/
theorem matrixEuclideanCLM_matrixCoordinates (P : MatrixSpace n)
    (ξ : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    matrixEuclideanCLM (matrixCoordinates P) ξ i = inner ℝ (rowCLM i P) ξ := by
  simp [matrixEuclideanCLM_apply, matrixCoordinates, Matrix.mulVec, dotProduct,
    PiLp.inner_apply, mul_comm]

/--
DPR pp. 2 and 15. Finite family of row-wise signed measure divergences in the distributional sense;
no new vector measure is constructed.
-/
def HasMatrixMeasureDivergence
    (M : MeasureTheory.VectorMeasure (EuclideanSpace ℝ (Fin n)) (MatrixSpace n))
    (D : Fin n → MeasureTheory.SignedMeasure (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ i, HasMeasureDivergence (rowMeasure M i) (D i)

end GeometricMeasure
