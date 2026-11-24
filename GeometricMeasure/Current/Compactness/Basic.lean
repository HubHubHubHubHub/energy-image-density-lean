import GeometricMeasure.Current.Mass.Basic
import GeometricMeasure.Current.WeakConvergence
import GeometricMeasure.VectorMeasure.Compactness.Basic

/-!
# Compactness of currents with measure divergence

This file contains the definitions and results of the development of
`GeometricMeasure.Current.Compactness` that the main statements of the library (the head theorems
listed in the README of the repository) use. `GeometricMeasure.Current.Compactness` imports it and
continues the development.

## Main definitions

* `signedMeasurePairing`: The pairing `∫ g dD⁺ - ∫ g dD⁻` of a signed measure with a bounded
  continuous function, through the Jordan decomposition of `D`.

## Main statements

* `signedMeasurePairing_sub`: For finite measures `α` and `β`, the pairing of `α.toSignedMeasure -
  β.toSignedMeasure` with a bounded continuous `g` is `∫ x, g x ∂α - ∫ x, g x ∂β`.
* `signedMeasurePairing_currentTest`: For a signed measure `D` and a scalar test `φ`, the pairing
  `signedMeasurePairing D φ` equals the current value `signedTestCurrent D φ`.
* `totalVariation_le_liminf_of_scalarTest_tendsto`: If `signedTestCurrent (Ds n) φ →
  signedTestCurrent D φ` for every scalar test `φ`, then `D.totalVariation U ≤ liminf (Ds
  n).totalVariation U` for every open `U`.
-/
noncomputable section
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ}

/-- The pairing `∫ g dD⁺ - ∫ g dD⁻` of a signed measure with a bounded continuous function, through
the Jordan decomposition of `D`. -/
def signedMeasurePairing (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) : ℝ :=
  (∫ x, g x ∂D.toJordanDecomposition.posPart) -
    (∫ x, g x ∂D.toJordanDecomposition.negPart)

theorem signedMeasurePairing_sub
    (α : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure α]
    (β : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure β]
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) :
    signedMeasurePairing (α.toSignedMeasure - β.toSignedMeasure) g =
      (∫ x, g x ∂α) - (∫ x, g x ∂β) := by
  let D := α.toSignedMeasure - β.toSignedMeasure
  have heq : α + D.toJordanDecomposition.negPart =
      β + D.toJordanDecomposition.posPart := by
    apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    have hj := D.toSignedMeasure_toJordanDecomposition
    change D.toJordanDecomposition.posPart.toSignedMeasure -
      D.toJordanDecomposition.negPart.toSignedMeasure =
      α.toSignedMeasure - β.toSignedMeasure at hj
    simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add.mp hj).symm
  have hi := congrArg (fun ν : Measure (EuclideanSpace ℝ (Fin d)) => ∫ x, g x ∂ν) heq
  rw [integral_add_measure (g.integrable _) (g.integrable _),
    integral_add_measure (g.integrable _) (g.integrable _)] at hi
  change (∫ x, g x ∂D.toJordanDecomposition.posPart) -
    (∫ x, g x ∂D.toJordanDecomposition.negPart) = _
  linarith

theorem signedMeasurePairing_currentTest
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (φ : ScalarCurrentTest d) :
    signedMeasurePairing D
      (φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) =
      signedTestCurrent D φ := (signedTestCurrent_apply D φ).symm

theorem totalVariation_le_liminf_of_scalarTest_tendsto
    (Ds : ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hconv : ∀ φ : ScalarCurrentTest d,
      Tendsto (fun n => signedTestCurrent (Ds n) φ) atTop (𝓝 (signedTestCurrent D φ)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    D.totalVariation U ≤ Filter.liminf (fun n => (Ds n).totalVariation U) atTop := by
  simpa only [signedTestCurrent_mass_eq_totalVariation _ hU] using
    testFunctionalMassOn_le_liminf (fun n => signedTestCurrent (Ds n))
      (signedTestCurrent D) hconv U


end GeometricMeasure

