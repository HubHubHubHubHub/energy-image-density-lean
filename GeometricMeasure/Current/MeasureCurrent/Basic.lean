import GeometricMeasure.Current.Tests
import GeometricMeasure.VectorMeasure.Polar
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The current of a vector measure

This file contains the definitions and results of the development of
`GeometricMeasure.Current.MeasureCurrent` that the main statements of the library (the head theorems
listed in the README of the repository) use, together with the basic API of their definitions.
`GeometricMeasure.Current.MeasureCurrent` imports it and continues the development.

## Main definitions

* `measureOneCurrent`: The one-current `ω ↦ ∫ x, ω x (polarDensity M x) ∂M.variation` of a vector
  measure.
* `positiveMeasureTestCurrent`: Total for every positive measure; evaluation requires local
  integrability.
* `signedTestCurrent`: The scalar current of a signed measure: the difference of the currents of the
  positive and negative parts of its Jordan decomposition.
* `HasMeasureDivergence`: `D` is the divergence of `M`: on every scalar test, the current of `D`
  equals minus the boundary of the one-current of `M`.

## Main statements

* `measureOneCurrent_smul_test`: The one-current of `M` is homogeneous in the test form:
  `measureOneCurrent M (c • ω) = c * measureOneCurrent M ω`.
* `signedTestCurrent_mass_le`: For every set `U`, the mass of `signedTestCurrent D` on `U` is at
  most `D.totalVariation U`.
-/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace GeometricMeasure
variable {d : ℕ}

theorem ofReal_integral_norm_currentTest_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (ω : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞))
    {U : Set (EuclideanSpace ℝ (Fin d))}
    (hs : tsupport (ω : EuclideanSpace ℝ (Fin d) → F) ⊆ U)
    (hn : ∀ x, ‖ω x‖ ≤ 1) :
    ENNReal.ofReal (∫ x, ‖ω x‖ ∂ν) ≤ ν U := by
  apply integral_le_measure (fun x _ => hn x)
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), norm_zero]

variable (M : VectorMeasure (EuclideanSpace ℝ (Fin d))
  (EuclideanSpace ℝ (Fin d)))

/-- The one-current `ω ↦ ∫ x, ω x (polarDensity M x) ∂M.variation` of a vector measure. -/
def measureOneCurrent : OneFormCurrentTest d →L[ℝ] ℝ :=
  TestFunction.integralAgainstBilinCLM
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    M.variation (polarDensity M)

theorem measureOneCurrent_apply (ω : OneFormCurrentTest d) :
    measureOneCurrent M ω = ∫ x, ω x (polarDensity M x) ∂M.variation :=
  TestFunction.integralAgainstBilinCLM_eq_integral
    ((integrable_polarDensity M).locallyIntegrable.locallyIntegrableOn _)

theorem measureOneCurrent_smul_test (c : ℝ) (ω : OneFormCurrentTest d) :
    measureOneCurrent M (c • ω) = c * measureOneCurrent M ω :=
  map_smul _ _ _

/-- Total for every positive measure; evaluation requires local integrability. -/
def positiveMeasureTestCurrent (ν : Measure (EuclideanSpace ℝ (Fin d))) :
    ScalarCurrentTest d →L[ℝ] ℝ :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) ν (fun _ => (1 : ℝ))

theorem positiveMeasureTestCurrent_apply
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (hν : LocallyIntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ)) Set.univ ν)
    (φ : ScalarCurrentTest d) :
    positiveMeasureTestCurrent ν φ = ∫ x, φ x ∂ν := by
  rw [positiveMeasureTestCurrent, TestFunction.integralAgainstBilinCLM_eq_integral hν]
  simp

theorem positiveMeasureTestCurrent_apply_of_locallyFinite
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsLocallyFiniteMeasure ν]
    (φ : ScalarCurrentTest d) :
    positiveMeasureTestCurrent ν φ = ∫ x, φ x ∂ν :=
  positiveMeasureTestCurrent_apply ν (locallyIntegrableOn_const (1 : ℝ)) φ

/-- The scalar current of a signed measure: the difference of the currents of the positive and
negative parts of its Jordan decomposition. -/
def signedTestCurrent (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) :
    ScalarCurrentTest d →L[ℝ] ℝ :=
  positiveMeasureTestCurrent D.toJordanDecomposition.posPart -
    positiveMeasureTestCurrent D.toJordanDecomposition.negPart

theorem signedTestCurrent_apply (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (φ : ScalarCurrentTest d) :
    signedTestCurrent D φ = (∫ x, φ x ∂D.toJordanDecomposition.posPart) -
      ∫ x, φ x ∂D.toJordanDecomposition.negPart := by
  simp [signedTestCurrent, positiveMeasureTestCurrent_apply_of_locallyFinite]

theorem signedTestCurrent_neg (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) :
    signedTestCurrent (-D) = -signedTestCurrent D := by
  simp [signedTestCurrent, SignedMeasure.toJordanDecomposition_neg]

theorem signedTestCurrent_abs_le_integral_norm
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (φ : ScalarCurrentTest d) :
    |signedTestCurrent D φ| ≤ ∫ x, ‖φ x‖ ∂D.totalVariation := by
  rw [signedTestCurrent_apply, SignedMeasure.totalVariation,
    integral_add_measure
      (φ.integrable (locallyIntegrableOn_const (1 : ℝ))).norm
      (φ.integrable (locallyIntegrableOn_const (1 : ℝ))).norm]
  apply (abs_sub _ _).trans
  simpa only [Real.norm_eq_abs] using add_le_add
    (norm_integral_le_integral_norm (fun x => φ x) (μ := D.toJordanDecomposition.posPart))
    (norm_integral_le_integral_norm (fun x => φ x) (μ := D.toJordanDecomposition.negPart))

theorem signedTestCurrent_mass_le (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (U : Set (EuclideanSpace ℝ (Fin d))) :
    testFunctionalMassOn (signedTestCurrent D) U ≤ D.totalVariation U := by
  apply testFunctionalMassOn_le
  intro φ hs hn
  exact (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
    (signedTestCurrent_abs_le_integral_norm D φ))).trans
      (ofReal_integral_norm_currentTest_le D.totalVariation φ hs hn)

/-- `D` is the divergence of `M`: on every scalar test, the current of `D` equals minus the boundary
of the one-current of `M`. -/
def HasMeasureDivergence (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ φ : ScalarCurrentTest d,
    signedTestCurrent D φ = -oneCurrentBoundary (measureOneCurrent M) φ

theorem signedTestCurrent_zero :
    signedTestCurrent (0 : SignedMeasure (EuclideanSpace ℝ (Fin d))) = 0 := by
  simp [signedTestCurrent, SignedMeasure.toJordanDecomposition_zero]

theorem measureOneCurrent_zero :
    measureOneCurrent (0 : VectorMeasure (EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d))) = 0 := by
  ext ω
  simp [measureOneCurrent_apply]

theorem hasMeasureDivergence_zero_iff :
    HasMeasureDivergence M 0 ↔ oneCurrentBoundary (measureOneCurrent M) = 0 := by
  constructor
  · intro h
    ext φ
    have hh := h φ
    simpa [signedTestCurrent_zero] using hh.symm
  · intro h φ
    simp [signedTestCurrent_zero, h]

end GeometricMeasure
