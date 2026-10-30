import GeometricMeasure.Current.Tests
import GeometricMeasure.VectorMeasure.Polar
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The current of a Euclidean vector measure, signed integration, and divergence. -/

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

def measureOneCurrent : OneFormCurrentTest d →L[ℝ] ℝ :=
  TestFunction.integralAgainstBilinCLM
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    M.variation (polarDensity M)

set_option maxHeartbeats 1000000 in
theorem integrable_measureOneCurrent_integrand (ω : OneFormCurrentTest d) :
    Integrable (fun x => ω x (polarDensity M x)) M.variation :=
  ω.integrable_bilin (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    ((integrable_polarDensity M).locallyIntegrable.locallyIntegrableOn _)

theorem measureOneCurrent_apply (ω : OneFormCurrentTest d) :
    measureOneCurrent M ω = ∫ x, ω x (polarDensity M x) ∂M.variation :=
  TestFunction.integralAgainstBilinCLM_eq_integral
    ((integrable_polarDensity M).locallyIntegrable.locallyIntegrableOn _)

theorem measureOneCurrent_apply_of_polar
    {q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hq : Integrable q M.variation) (hrep : M.variation.withDensityᵥ q = M)
    (ω : OneFormCurrentTest d) :
    measureOneCurrent M ω = ∫ x, ω x (q x) ∂M.variation := by
  rw [measureOneCurrent_apply]
  apply integral_congr_ae
  filter_upwards [polarDensity_ae_eq M hq hrep] with x hx
  rw [hx]

theorem measureOneCurrent_add_test (ω η : OneFormCurrentTest d) :
    measureOneCurrent M (ω + η) = measureOneCurrent M ω + measureOneCurrent M η :=
  map_add _ _ _

theorem measureOneCurrent_smul_test (c : ℝ) (ω : OneFormCurrentTest d) :
    measureOneCurrent M (c • ω) = c * measureOneCurrent M ω :=
  map_smul _ _ _

theorem measureOneCurrent_abs_le_integral_norm (ω : OneFormCurrentTest d) :
    |measureOneCurrent M ω| ≤ ∫ x, ‖ω x‖ ∂M.variation := by
  rw [measureOneCurrent_apply, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (integrable_measureOneCurrent_integrand M ω).norm
    (ω.integrable (locallyIntegrableOn_const (1 : ℝ))).norm
  filter_upwards [norm_polarDensity_ae M] with x hx
  simpa [hx] using (ω x).le_opNorm (polarDensity M x)

theorem measureOneCurrent_abs_le_supNorm (ω : OneFormCurrentTest d) :
    |measureOneCurrent M ω| ≤
      ‖(ω : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d))
        (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))‖ * M.variation.real Set.univ := by
  apply (measureOneCurrent_abs_le_integral_norm M ω).trans
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ (Fin d),
        ‖(ω : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d))
          (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))‖ ∂M.variation :=
      integral_mono (ω.integrable (locallyIntegrableOn_const (1 : ℝ))).norm
        (integrable_const _) (fun x => (ω : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d))
          (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)).norm_coe_le_norm x)
    _ = _ := by simp [integral_const, mul_comm]

theorem measureOneCurrent_mass_le (U : Set (EuclideanSpace ℝ (Fin d))) :
    testFunctionalMassOn (measureOneCurrent M) U ≤ M.variation U := by
  apply testFunctionalMassOn_le
  intro ω hs hn
  exact (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
    (measureOneCurrent_abs_le_integral_norm M ω))).trans
      (ofReal_integral_norm_currentTest_le M.variation ω hs hn)

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

def HasMeasureDivergence (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ φ : ScalarCurrentTest d,
    signedTestCurrent D φ = -oneCurrentBoundary (measureOneCurrent M) φ

theorem boundary_measureOneCurrent_eq_neg (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hD : HasMeasureDivergence M D) :
    oneCurrentBoundary (measureOneCurrent M) = -signedTestCurrent D := by
  ext φ
  simpa using (congrArg (fun r : ℝ => -r) (hD φ)).symm

theorem boundary_measureOneCurrent_mass_le (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hD : HasMeasureDivergence M D) (U : Set (EuclideanSpace ℝ (Fin d))) :
    testFunctionalMassOn (oneCurrentBoundary (measureOneCurrent M)) U ≤ D.totalVariation U := by
  rw [boundary_measureOneCurrent_eq_neg M D hD, ← signedTestCurrent_neg]
  simpa only [SignedMeasure.totalVariation_neg] using signedTestCurrent_mass_le (-D) U

theorem measureOneCurrent_isNormal (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hD : HasMeasureDivergence M D) : IsNormalOneCurrent (measureOneCurrent M) := by
  haveI : IsFiniteMeasure D.totalVariation := by
    unfold SignedMeasure.totalVariation
    infer_instance
  exact ⟨(measureOneCurrent_mass_le M _).trans_lt (measure_lt_top _ _),
    (boundary_measureOneCurrent_mass_le M D hD _).trans_lt (measure_lt_top _ _)⟩

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

theorem measureOneCurrent_dimension_zero
    (N : VectorMeasure (EuclideanSpace ℝ (Fin 0)) (EuclideanSpace ℝ (Fin 0))) :
    measureOneCurrent N = 0 := by
  rw [eq_zero_of_dimension_zero N, measureOneCurrent_zero]

end GeometricMeasure
