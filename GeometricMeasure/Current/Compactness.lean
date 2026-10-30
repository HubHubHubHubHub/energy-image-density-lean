import GeometricMeasure.Current.VectorMeasureCompactness

/-! Compactness with measure divergences and lower semicontinuity of boundaries. -/
noncomputable section
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ}

def signedMeasurePairing (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) : ℝ :=
  (∫ x, g x ∂D.toJordanDecomposition.posPart) -
    (∫ x, g x ∂D.toJordanDecomposition.negPart)

def SignedMeasureWeaklyTendsto
    (Ds : ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ,
    Tendsto (fun n => signedMeasurePairing (Ds n) g) atTop (𝓝 (signedMeasurePairing D g))

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

theorem hasMeasureDivergence_of_weaklyTendsto
    (Ms : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (Ds : ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hM : VectorMeasureWeaklyTendsto Ms M) (hD : SignedMeasureWeaklyTendsto Ds D)
    (hdiv : ∀ n, HasMeasureDivergence (Ms n) (Ds n)) : HasMeasureDivergence M D := by
  intro φ
  have hleft := hD (φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
  simp only [signedMeasurePairing_currentTest] at hleft
  have hright := (hM ((currentTestDerivative φ) : BoundedCovectorField d d)).neg
  simp only [vectorMeasurePairing_currentTest] at hright
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Filter.Eventually.of_forall (fun n => (hdiv n φ).symm))

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

theorem totalVariation_le_liminf_of_weaklyTendsto
    (Ds : ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hD : SignedMeasureWeaklyTendsto Ds D)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    D.totalVariation U ≤ Filter.liminf (fun n => (Ds n).totalVariation U) atTop := by
  apply totalVariation_le_liminf_of_scalarTest_tendsto Ds D _ hU
  intro φ
  simpa only [signedMeasurePairing_currentTest] using
    hD (φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)

theorem boundary_tendsto_of_weaklyTendsto
    (Ms : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (hM : VectorMeasureWeaklyTendsto Ms M) (φ : ScalarCurrentTest d) :
    Tendsto (fun n => oneCurrentBoundary (measureOneCurrent (Ms n)) φ)
      atTop (𝓝 (oneCurrentBoundary (measureOneCurrent M) φ)) := by
  simpa only [oneCurrentBoundary_apply, vectorMeasurePairing_currentTest] using
    hM ((currentTestDerivative φ) : BoundedCovectorField d d)

theorem boundary_mass_le_liminf_of_weaklyTendsto
    (Ms : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (hM : VectorMeasureWeaklyTendsto Ms M) (U : Set (EuclideanSpace ℝ (Fin d))) :
    testFunctionalMassOn (oneCurrentBoundary (measureOneCurrent M)) U ≤
      Filter.liminf (fun n =>
        testFunctionalMassOn (oneCurrentBoundary (measureOneCurrent (Ms n))) U) atTop :=
  testFunctionalMassOn_le_liminf _ _ (boundary_tendsto_of_weaklyTendsto Ms M hM) U

def signedPositiveFinite (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) :
    FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
  ⟨D.toJordanDecomposition.posPart, inferInstance⟩

def signedNegativeFinite (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) :
    FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
  ⟨D.toJordanDecomposition.negPart, inferInstance⟩

def signedFiniteFamily (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (b : Bool) :
    FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
  if b then signedNegativeFinite D else signedPositiveFinite D

theorem signedFiniteFamily_le_totalVariation
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (b : Bool) :
    (signedFiniteFamily D b : Measure _) ≤ D.totalVariation := by
  cases b <;> intro s <;>
    simp only [signedFiniteFamily, Bool.false_eq_true, ↓reduceIte,
      signedPositiveFinite, signedNegativeFinite, FiniteMeasure.toMeasure_mk,
      SignedMeasure.totalVariation, Measure.add_apply]
  · exact le_self_add
  · exact le_add_self

theorem signedWeaklyTendsto_of_parts_tendsto
    (Ds : ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (αpos : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (αneg : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (hpos : Tendsto (fun n => signedPositiveFinite (Ds n)) atTop (𝓝 αpos))
    (hneg : Tendsto (fun n => signedNegativeFinite (Ds n)) atTop (𝓝 αneg)) :
    SignedMeasureWeaklyTendsto Ds
      ((αpos : Measure _).toSignedMeasure - (αneg : Measure _).toSignedMeasure) := by
  intro g
  rw [signedMeasurePairing_sub]
  exact ((FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hpos) g).sub
    ((FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hneg) g)


theorem exists_normalCurrent_weak_subseq
    (Ms : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (Ds : ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    {L : Set (EuclideanSpace ℝ (Fin d))} (hL : IsCompact L)
    (C : ℝ≥0) (C_D : ℝ≥0)
    (hMsupport : ∀ n, (Ms n).variation Kᶜ = 0)
    (hMmass : ∀ n, (Ms n).variation univ ≤ (C : ℝ≥0∞))
    (hDsupport : ∀ n, (Ds n).totalVariation Lᶜ = 0)
    (hDmass : ∀ n, (Ds n).totalVariation univ ≤ (C_D : ℝ≥0∞))
    (hdiv : ∀ n, HasMeasureDivergence (Ms n) (Ds n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)),
      ∃ D : SignedMeasure (EuclideanSpace ℝ (Fin d)),
        M.variation Kᶜ = 0 ∧ M.variation univ ≤ (C : ℝ≥0∞) ∧
        D.totalVariation Lᶜ = 0 ∧ D.totalVariation univ ≤ (C_D : ℝ≥0∞) ∧
        VectorMeasureWeaklyTendsto (Ms ∘ φ) M ∧
        SignedMeasureWeaklyTendsto (Ds ∘ φ) D ∧ HasMeasureDivergence M D ∧
        IsNormalOneCurrent (measureOneCurrent M) ∧
        testFunctionalMassOn (oneCurrentBoundary (measureOneCurrent M)) univ ≤
          (C_D : ℝ≥0∞) := by
  let μs (n : ℕ) : ((Fin d × Bool) ⊕ Bool) →
      FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
    Sum.elim (coordinateFiniteFamily (Ms n)) (signedFiniteFamily (Ds n))
  have hm (n : ℕ) (i : (Fin d × Bool) ⊕ Bool) : (μs n i).mass ≤ max C C_D := by
    cases i with
    | inl i =>
      exact finiteMeasure_mass_le_of_le _ _ (coordinateFiniteFamily_le_variation (Ms n) i) _
        ((hMmass n).trans (ENNReal.coe_le_coe.mpr (le_max_left C C_D)))
    | inr b =>
      exact finiteMeasure_mass_le_of_le _ _ (signedFiniteFamily_le_totalVariation (Ds n) b) _
        ((hDmass n).trans (ENNReal.coe_le_coe.mpr (le_max_right C C_D)))
  have hs (n : ℕ) (i : (Fin d × Bool) ⊕ Bool) : μs n i (K ∪ L)ᶜ = 0 := by
    cases i with
    | inl i =>
      apply finiteMeasure_compl_eq_zero_of_le _ _ (coordinateFiniteFamily_le_variation (Ms n) i)
      exact le_antisymm ((measure_mono (compl_subset_compl.mpr subset_union_left)).trans
        (hMsupport n).le) zero_le
    | inr b =>
      apply finiteMeasure_compl_eq_zero_of_le _ _ (signedFiniteFamily_le_totalVariation (Ds n) b)
      exact le_antisymm ((measure_mono (compl_subset_compl.mpr subset_union_right)).trans
        (hDsupport n).le) zero_le
  obtain ⟨φ, hφ, α, hαmass, hαsupp, hα⟩ :=
    exists_finiteMeasure_family_subseq μs (hK.union hL) (max C C_D) hm hs
  let αpos := fun i => α (Sum.inl (i, false))
  let αneg := fun i => α (Sum.inl (i, true))
  let M := assemblePositiveFamily αpos αneg
  let D := (α (Sum.inr false) : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure -
    (α (Sum.inr true) : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure
  have hMc : VectorMeasureWeaklyTendsto (Ms ∘ φ) M :=
    weaklyTendsto_assemble_of_coordinateParts_tendsto _ αpos αneg
      (fun i => hα (Sum.inl (i, false))) (fun i => hα (Sum.inl (i, true)))
  have hDc : SignedMeasureWeaklyTendsto (Ds ∘ φ) D :=
    signedWeaklyTendsto_of_parts_tendsto _ _ _ (hα (Sum.inr false)) (hα (Sum.inr true))
  have hlimdiv : HasMeasureDivergence M D :=
    hasMeasureDivergence_of_weaklyTendsto _ _ M D hMc hDc (fun n => hdiv (φ n))
  have hMs : M.variation Kᶜ = 0 := by
    apply le_antisymm _ zero_le
    have h := variation_le_liminf_of_weaklyTendsto _ M hMc hK.isClosed.isOpen_compl
    simpa [Function.comp_def, hMsupport] using h
  have hDs : D.totalVariation Lᶜ = 0 := by
    apply le_antisymm _ zero_le
    have h := totalVariation_le_liminf_of_weaklyTendsto _ D hDc hL.isClosed.isOpen_compl
    simpa [Function.comp_def, hDsupport] using h
  have hMm : M.variation univ ≤ (C : ℝ≥0∞) := by
    apply (variation_le_liminf_of_weaklyTendsto _ M hMc isOpen_univ).trans
    exact Filter.liminf_le_of_le (by isBoundedDefault) (fun b hb =>
      let ⟨n, hn⟩ := hb.exists
      hn.trans (hMmass (φ n)))
  have hDm : D.totalVariation univ ≤ (C_D : ℝ≥0∞) := by
    apply (totalVariation_le_liminf_of_weaklyTendsto _ D hDc isOpen_univ).trans
    exact Filter.liminf_le_of_le (by isBoundedDefault) (fun b hb =>
      let ⟨n, hn⟩ := hb.exists
      hn.trans (hDmass (φ n)))
  refine ⟨φ, hφ, M, D, hMs, hMm, hDs, hDm, hMc, hDc, hlimdiv,
    measureOneCurrent_isNormal M D hlimdiv, ?_⟩
  rw [boundary_measureOneCurrent_mass_eq M D hlimdiv isOpen_univ]
  exact hDm


end GeometricMeasure

