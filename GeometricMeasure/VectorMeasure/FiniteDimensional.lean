import GeometricMeasure.VectorMeasure.Coordinates
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-! Finite variation for Euclidean vector measures, without assuming it in the
construction. A finite sum of scalar Jordan variations is a common dominating measure.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GeometricMeasure

variable {X : Type*} [MeasurableSpace X] {m : ℕ}

/-- A coordinate-dependent finite dominating measure; it is not the Euclidean variation. -/
def sumTotalVariation (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) : Measure X :=
  ∑ i, (coord M i).totalVariation

theorem sumTotalVariation_apply (M : VectorMeasure X (EuclideanSpace ℝ (Fin m)))
    (s : Set X) : sumTotalVariation M s = ∑ i, (coord M i).totalVariation s :=
  Measure.finsetSum_apply _ _ _

/-- Only scalar Jordan finiteness is used here. -/
instance isFiniteMeasure_sumTotalVariation
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    IsFiniteMeasure (sumTotalVariation M) := by
  haveI (i : Fin m) : IsFiniteMeasure (coord M i).totalVariation := by
    unfold SignedMeasure.totalVariation
    infer_instance
  unfold sumTotalVariation
  infer_instance

theorem coord_absolutelyContinuous_sum_totalVariation
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (i : Fin m) :
    coord M i ≪ᵥ (sumTotalVariation M).toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro s hs hzero
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs, sumTotalVariation_apply] at hzero
  apply SignedMeasure.null_of_totalVariation_zero
  have hle : (coord M i).totalVariation s ≤ ∑ j, (coord M j).totalVariation s :=
    Finset.single_le_sum (f := fun j : Fin m => (coord M j).totalVariation s)
      (fun j _ => zero_le) (Finset.mem_univ i)
  exact le_antisymm (hzero ▸ hle) zero_le

/-- Reconstruction with a finite dominating measure, before proving finite variation. -/
theorem withDensityᵥ_rnDensity_sumTotalVariation
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    (sumTotalVariation M).withDensityᵥ (rnDensity M (sumTotalVariation M)) = M :=
  withDensityᵥ_rnDensity M (sumTotalVariation M)
    (coord_absolutelyContinuous_sum_totalVariation M)

/-- The density formula identifies the intrinsic Euclidean variation. -/
theorem variation_eq_sumTotalVariation_withDensity
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    M.variation = (sumTotalVariation M).withDensity
      (fun x => ‖rnDensity M (sumTotalVariation M) x‖ₑ) := by
  calc
    M.variation = ((sumTotalVariation M).withDensityᵥ
        (rnDensity M (sumTotalVariation M))).variation :=
      congrArg VectorMeasure.variation (withDensityᵥ_rnDensity_sumTotalVariation M).symm
    _ = _ := Measure.variation_withDensityᵥ (integrable_rnDensity M (sumTotalVariation M))

/--
Every Euclidean vector measure has finite variation. No
variation-finiteness instance is used upstream: the proof integrates against the scalar Jordan sum.
-/
instance isFiniteMeasure_variation (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    IsFiniteMeasure M.variation := by
  rw [variation_eq_sumTotalVariation_withDensity M]
  exact isFiniteMeasure_withDensity
    (hasFiniteIntegral_iff_enorm.mp (integrable_rnDensity M (sumTotalVariation M)).2).ne

@[simp] theorem sumTotalVariation_zero :
    sumTotalVariation (0 : VectorMeasure X (EuclideanSpace ℝ (Fin m))) = 0 := by
  simp [sumTotalVariation, SignedMeasure.totalVariation_zero]

end GeometricMeasure
