import GeometricMeasure.Current.BesselResolvent

/-!
# Heat kernels and scalar tests in dimension zero

## Main results
At positive times, the heat kernel on the one-point Euclidean space equals one. Constant functions
define smooth compactly supported scalar tests there.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped Topology RealInnerProductSpace Convolution
namespace GeometricMeasure
variable {d : ℕ}

/--
The heat kernel is one in dimension zero at positive times. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem heatKernel_zero_dimension {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin 0)) : heatKernel 0 t x = 1 := by
  have hx : x = 0 := Subsingleton.elim _ _
  simp [heatKernel, ht, hx]

/--
Constant test with value c on the one-point space; it is nonzero when c ≠ 0. Source: DPR p. 9
(context), heat-kernel representation.
-/
def zeroDimTest (c : ℝ) : ScalarCurrentTest 0 where
  toFun _ := c
  contDiff' := contDiff_const
  hasCompactSupport' := by
    apply (isCompact_singleton (x := (0 : EuclideanSpace ℝ (Fin 0)))).of_isClosed_subset isClosed_closure
    intro x _
    exact Set.mem_singleton_iff.2 (Subsingleton.elim _ _)
  tsupport_subset' := subset_univ _

end GeometricMeasure
