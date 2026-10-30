import GeometricMeasure.Current.LocalizedDilation

/-!
# Finite combinations of currents and local divergences

## Main results
Currents and their divergences add on the same set of tests. Jordan total variation is subadditive
on open sets. References: De Philippis–Rindler, pp. 8–9, and row-wise divergence on p. 15.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ}

/--
Additivity of the scalar test current of a signed measure (Jordan parts recombined). DPR connection
pp. 8–9, 15: finite combinations and Jordan variation on open sets.
-/
theorem signedTestCurrent_add (D₁ D₂ : SignedMeasure (EuclideanSpace ℝ (Fin d))) :
    signedTestCurrent (D₁ + D₂) = signedTestCurrent D₁ + signedTestCurrent D₂ := by
  ext φ
  have hrep : D₁ + D₂ =
      (D₁.toJordanDecomposition.posPart + D₂.toJordanDecomposition.posPart).toSignedMeasure -
      (D₁.toJordanDecomposition.negPart + D₂.toJordanDecomposition.negPart).toSignedMeasure := by
    conv_lhs => rw [← D₁.toSignedMeasure_toJordanDecomposition,
      ← D₂.toSignedMeasure_toJordanDecomposition]
    simp only [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_add]
    abel
  have hi := fun (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] =>
    φ.integrable (μ := μ) (locallyIntegrableOn_const (1 : ℝ))
  change signedTestCurrent (D₁ + D₂) φ = signedTestCurrent D₁ φ + signedTestCurrent D₂ φ
  rw [hrep, ← signedMeasurePairing_currentTest, signedMeasurePairing_sub,
    signedTestCurrent_apply, signedTestCurrent_apply]
  change (∫ x, φ x ∂(D₁.toJordanDecomposition.posPart + D₂.toJordanDecomposition.posPart)) -
      (∫ x, φ x ∂(D₁.toJordanDecomposition.negPart + D₂.toJordanDecomposition.negPart)) = _
  rw [integral_add_measure (hi _) (hi _), integral_add_measure (hi _) (hi _)]
  ring

/--
The scalar test current commutes with a finite sum of signed measures. DPR connection pp. 8–9, 15:
finite combinations and Jordan variation on open sets.
-/
theorem signedTestCurrent_finset_sum {ι : Type*} (t : Finset ι)
    (D : ι → SignedMeasure (EuclideanSpace ℝ (Fin d))) :
    signedTestCurrent (∑ i ∈ t, D i) = ∑ i ∈ t, signedTestCurrent (D i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [signedTestCurrent_zero]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, signedTestCurrent_add, ih]

/--
The one-dimensional current commutes with a finite sum of Euclidean vector measures. DPR connection
pp. 8–9, 15: finite combinations and Jordan variation on open sets.
-/
theorem measureOneCurrent_finset_sum {ι : Type*} (t : Finset ι)
    (R : ι → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d))) :
    measureOneCurrent (∑ i ∈ t, R i) = ∑ i ∈ t, measureOneCurrent (R i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [measureOneCurrent_zero]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, measureOneCurrent_add, ih]

/--
Finite real combinations of local divergence equations on the same arbitrary set. DPR connection pp.
8–9, 15: finite combinations and Jordan variation on open sets.
-/
theorem hasMeasureDivergenceOn_finset_sum_smul {ι : Type*} (t : Finset ι) (c : ι → ℝ)
    (R : ι → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (Q : ι → SignedMeasure (EuclideanSpace ℝ (Fin d))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (h : ∀ i, HasMeasureDivergenceOn (R i) (Q i) U) :
    HasMeasureDivergenceOn (∑ i ∈ t, c i • R i) (∑ i ∈ t, c i • Q i) U := by
  intro φ hφ
  rw [signedTestCurrent_finset_sum, measureOneCurrent_finset_sum, oneCurrentBoundary_apply]
  simp only [FunLike.coe_sum, Finset.sum_apply, signedTestCurrent_smul,
    measureOneCurrent_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hs : ∀ i ∈ t, c i * signedTestCurrent (Q i) φ =
      -(c i * measureOneCurrent (R i) (currentTestDerivative φ)) := fun i _ => by
    rw [h i φ hφ, oneCurrentBoundary_apply, mul_neg]
  rw [Finset.sum_congr rfl hs, Finset.sum_neg_distrib]

/--
Subadditivity of the Jordan total variation on open sets, through the current mass identity. DPR
connection pp. 8–9, 15: finite combinations and Jordan variation on open sets.
-/
theorem signedTotalVariation_add_le_of_isOpen (D₁ D₂ : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    (D₁ + D₂).totalVariation U ≤ D₁.totalVariation U + D₂.totalVariation U := by
  rw [← signedTestCurrent_mass_eq_totalVariation _ hU, ← signedTestCurrent_mass_eq_totalVariation _ hU,
    ← signedTestCurrent_mass_eq_totalVariation _ hU]
  apply testFunctionalMassOn_le
  intro φ hs hn
  rw [signedTestCurrent_add]
  change ENNReal.ofReal (signedTestCurrent D₁ φ + signedTestCurrent D₂ φ) ≤ _
  exact ENNReal.ofReal_add_le.trans (add_le_add
    (ofReal_apply_le_testFunctionalMassOn _ _ φ hs hn)
    (ofReal_apply_le_testFunctionalMassOn _ _ φ hs hn))

/--
On an open set, the variation of a finite combination is bounded by the sum of variations
weighted by absolute values. DPR connection pp. 8–9, 15: finite combinations and Jordan variation
on open
sets.
-/
theorem signedTotalVariation_finset_sum_smul_le {ι : Type*} (t : Finset ι) (c : ι → ℝ)
    (D : ι → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    (∑ i ∈ t, c i • D i).totalVariation U ≤
      ∑ i ∈ t, ENNReal.ofReal |c i| * (D i).totalVariation U := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [SignedMeasure.totalVariation_zero]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine (signedTotalVariation_add_le_of_isOpen _ _ hU).trans (add_le_add (le_of_eq ?_) ih)
    rw [signedTotalVariation_smul, Measure.smul_apply]
    change (‖c a‖₊ : ℝ≥0∞) * _ = _
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_eq_abs]

end GeometricMeasure
