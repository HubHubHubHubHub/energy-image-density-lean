import GeometricMeasure.Matrix.WaveCone
import GeometricMeasure.VectorMeasure.Matrix
import GeometricMeasure.Current.MeasureCurrent

/-!
# Frobenius coordinates and matrix divergence

## Main results
Matrix coordinates identify row-wise signed measure divergence with the negative boundary functional
on tests.

Reference: De Philippis–Rindler, arXiv:1601.06543v2, pp. 2 and 15; Remark 1.3 and Corollary 1.13
provide the broader structure-theorem context.
-/

noncomputable section
open scoped Matrix
open WithLp
namespace GeometricMeasure
set_option autoImplicit false
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

/--
row convention of DPR p. 15 and distributional sign. Equivalence of functionals on tests: boundary =
negative divergence.
-/
theorem hasMatrixMeasureDivergence_iff_boundary
    (M : MeasureTheory.VectorMeasure (EuclideanSpace ℝ (Fin n)) (MatrixSpace n))
    (D : Fin n → MeasureTheory.SignedMeasure (EuclideanSpace ℝ (Fin n))) :
    HasMatrixMeasureDivergence M D ↔ ∀ i,
      oneCurrentBoundary (measureOneCurrent (rowMeasure M i)) = -signedTestCurrent (D i) := by
  constructor
  · intro h i
    exact boundary_measureOneCurrent_eq_neg _ _ (h i)
  · intro h i φ
    have hi := congrArg (fun T => T φ) (h i)
    change signedTestCurrent (D i) φ = -oneCurrentBoundary (measureOneCurrent (rowMeasure M i)) φ
    simpa using (congrArg Neg.neg hi).symm

end GeometricMeasure
