import GeometricMeasure.VectorMeasure.PolarFreezing
import GeometricMeasure.Current.LocalizedDilation

/-!
# exact transport and freezing of the matrix polar

## Main results
De Philippis–Rindler (2016), pp. 7–9. Restriction to the same closed source ball, Frobenius norm and
normalization by the singular part. The limits hold along every admissible sequence; they assume
neither divergence nor ellipticity.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ}

/--
Exact bridge to the Euclidean-valued representation of dilations; no change of normalization. DPR
pp. 7–9: transport and source estimate.
-/
theorem matrixReindexed_matrixDilation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    matrixReindexed (matrixDilation M x r hr c) =
      localizedDilation (matrixReindexed M) x r hr c := by
  apply VectorMeasure.ext
  intro A hA
  rw [matrixReindexed_apply, matrixDilation, smul_apply,
    VectorMeasure.map_apply _ (dilationEquiv x r hr).measurable hA,
    VectorMeasure.restrict_apply _ measurableSet_closedBall ((dilationEquiv x r hr).measurable hA),
    map_smul, localizedDilation, smul_apply,
    VectorMeasure.map_apply _ (dilationEquiv x r hr).measurable hA,
    VectorMeasure.restrict_apply _ measurableSet_closedBall ((dilationEquiv x r hr).measurable hA),
    matrixReindexed_apply]

end GeometricMeasure
