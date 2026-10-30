import GeometricMeasure.Current.StrongMeasureLimit

/-!
# Strong convergence and the contradiction for singular blow-ups

## Main results
Under the explicit `RegularPartL1Limit` hypothesis, the localized limit has a density and the
localized measures converge in total variation. The same conclusion holds for the original measures
restricted to B̄(0, 3/4). Singularity and a positive lower mass bound then contradict such blow-up
data. `Current.RegularPartLimit` constructs the required regular-part limit.

References: De Philippis–Rindler, arXiv p. 8, (2.3), (2.5), and p. 9.
The contradiction is used in `Current.MatrixStructure` to prove De Philippis–Rindler, Corollary
1.13.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace GeometricMeasure
namespace StrongConstancy
variable {d : ℕ}

/-- Localizing by a cutoff equal to one on a set preserves the restriction there. -/
theorem localPositive_restrict_of_one
    (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : MeasurableSet s)
    (hχ : ∀ x ∈ s, χ x = 1) :
    (localPositive χ μ : Measure (EuclideanSpace ℝ (Fin d))).restrict s =
      (μ : Measure (EuclideanSpace ℝ (Fin d))).restrict s := by
  change ((μ : Measure (EuclideanSpace ℝ (Fin d))).withDensity _).restrict s = _
  rw [restrict_withDensity hs]
  calc
    _ = ((μ : Measure (EuclideanSpace ℝ (Fin d))).restrict s).withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hs] with x hx
      simp only [hχ x hx, ENNReal.ofReal_one, Pi.one_apply]
    _ = _ := withDensity_one

end StrongConstancy
namespace MatrixPolarBlowupData
variable {d : ℕ} {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}

/--
The regular resolvent terms converge in L¹ to the specified integrable function h. This predicate is
realized by `MatrixPolarBlowupData.regularPartL1Limit_holds`.
-/
def RegularPartL1Limit (b : MatrixPolarBlowupData M D x)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  Integrable h ∧ Tendsto
    (fun n => ∫ y, ‖resolventRegular (b.mollifiedPositiveTest n)
      (b.mollifiedRemainderTest n) y - h y‖) atTop (𝓝 0)

/--
Under `RegularPartL1Limit h`, the Bessel error tends to zero in L¹ and the mollified positive
densities converge to h in L¹. References: De Philippis–Rindler, arXiv p. 9 and p. 13, Lemma 2.2.
-/
theorem mollified_l1_of_regularPartL1Limit (b : MatrixPolarBlowupData M D x)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (h14 : b.RegularPartL1Limit h) :
    Tendsto (fun n => ∫ y, ‖resolventError (b.mollifiedDefectTest n) y‖) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ y, ‖b.mollifiedPositive n y - h y‖) atTop (𝓝 0) := by
  have hl := StrongConstancy.positivity_zero_mass_balls
    (fun n => (b.mollified_resolvent_L6_uncond n).2.1)
    (fun n => (b.mollified_resolvent_L6_uncond n).2.2.1) h14.1
    (fun n => Filter.Eventually.of_forall (fun y => by
      have hz := b.mollifiedPositive_nonneg n y
      rw [(b.mollified_resolvent_L6_uncond n).1] at hz
      exact hz))
    (fun n => (b.mollified_resolvent_L6_uncond n).2.2.2)
    h14.2 b.mollified_resolvent_estimates.2.2.2
  refine ⟨hl.1, ?_⟩
  simpa only [fun n => (b.mollified_resolvent_L6_uncond n).1, Pi.add_apply] using hl.2

/--
Under `RegularPartL1Limit h`, the localized tangent has signed density h, is absolutely continuous,
and the localized positive measures converge to it in total variation. Reference: De
Philippis–Rindler, arXiv p. 8, (2.3), (2.5).
-/
theorem localized_totalVariation_of_regularPartL1Limit (b : MatrixPolarBlowupData M D x)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (h14 : b.RegularPartL1Limit h) :
    (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure =
      volume.withDensityᵥ h ∧
    (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))) ≪ volume ∧
    Tendsto (fun n =>
      ((b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure -
        (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0) := by
  have hz n : Integrable (b.mollifiedPositive n) := by
    exact scalarTest_integrable (b.mollifiedPositiveTest n)
  have hout := StrongConstancy.totalVariation_of_diagonal
    (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure
    (fun n => (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure)
    hz h14.1 (b.mollified_l1_of_regularPartL1Limit h14).2
    (fun φ => by
      simpa only [signedTestCurrent_toSignedMeasure] using b.mollifiedPositive_test_tendsto φ)
    diagonalError diagonalError_tendsto (by
      simpa only [b.signedMollification_localized_eq] using b.localizationMollifierIndex_spec.2.2.2)
  exact ⟨hout.1, StrongConstancy.absolutelyContinuous_of_signed_density _ h14.1 hout.1, hout.2⟩

/-- The localizer equals one on the closed ball of radius 3/4. -/
theorem localized_restrict_three_quarters (b : MatrixPolarBlowupData M D x) :
    (∀ n, (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).restrict
      (closedBall 0 (3 / 4)) =
      (b.positive n : Measure (EuclideanSpace ℝ (Fin d))).restrict (closedBall 0 (3 / 4))) ∧
    (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).restrict (closedBall 0 (3 / 4)) =
      (b.tangent : Measure (EuclideanSpace ℝ (Fin d))).restrict (closedBall 0 (3 / 4)) := by
  constructor
  · intro n
    exact StrongConstancy.localPositive_restrict_of_one _ _ measurableSet_closedBall
      (fun _ hy => interiorCutoff_one hy)
  · exact StrongConstancy.localPositive_restrict_of_one _ _ measurableSet_closedBall
      (fun _ hy => interiorCutoff_one hy)

/--
Under `RegularPartL1Limit`, the tangent restricted to B̄(0, 3/4) is absolutely continuous and the
original positive measures converge there in total variation. Reference: De Philippis–Rindler, arXiv
p. 8, (2.3), with the stated interior ball.
-/
theorem interior_totalVariation_of_regularPartL1Limit (b : MatrixPolarBlowupData M D x)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (h14 : b.RegularPartL1Limit h) :
    (b.tangent : Measure (EuclideanSpace ℝ (Fin d))).restrict (closedBall 0 (3 / 4)) ≪ volume ∧
    Tendsto (fun n =>
      ((b.positive n : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure -
        (b.tangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure).totalVariation.real
          (closedBall 0 (3 / 4))) atTop (𝓝 0) := by
  have hout := b.localized_totalVariation_of_regularPartL1Limit h14
  constructor
  · rw [← b.localized_restrict_three_quarters.2]
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hout.2.1
  · have he n :
        ((b.positive n : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure -
          (b.tangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure).restrict (closedBall 0 (3 / 4)) =
        ((b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure -
          (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure).restrict (closedBall 0 (3 / 4)) := by
      rw [VectorMeasure.restrict_sub, VectorMeasure.restrict_sub,
        VectorMeasure.restrict_toSignedMeasure measurableSet_closedBall,
        VectorMeasure.restrict_toSignedMeasure measurableSet_closedBall,
        VectorMeasure.restrict_toSignedMeasure measurableSet_closedBall,
        VectorMeasure.restrict_toSignedMeasure measurableSet_closedBall]
      congr 1
      · exact (Measure.toSignedMeasure_congr (b.localized_restrict_three_quarters.1 n)).symm
      · exact (Measure.toSignedMeasure_congr b.localized_restrict_three_quarters.2).symm
    have ht := StrongConstancy.totalVariation_on_set_tendsto
      (fun n => (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure)
      (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure
      hout.2.2 (closedBall 0 (3 / 4))
    apply ht.congr'
    apply Filter.Eventually.of_forall
    intro n
    have hv := congrArg (fun q : SignedMeasure (EuclideanSpace ℝ (Fin d)) => q.totalVariation.real univ) (he n)
    simpa only [signedTotalVariation_restrict _ measurableSet_closedBall,
      measureReal_def, Measure.restrict_apply_univ] using hv.symm

end MatrixPolarBlowupData
end GeometricMeasure

/-!
## Singularity contradicts the positive absolutely continuous limit

The localized blow-ups are singular, their masses converge to a positive limit, and the total
variation conclusion forces convergence on the singular support. These properties are
incompatible with the absolutely continuous limit. Reference: De Philippis–Rindler, arXiv p. 8,
after
(2.2)–(2.3).
-/
namespace GeometricMeasure
namespace MatrixPolarBlowupData
variable {d : ℕ} {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}

/--
No matrix polar blow-up datum can satisfy `RegularPartL1Limit`: total variation convergence to a
positive absolutely continuous limit contradicts singularity of the approximating measures. The
regular-part limit is constructed in `Current.RegularPartLimit`. Reference: De Philippis–Rindler,
arXiv p. 8, after (2.3).
This contradiction yields De Philippis–Rindler, Corollary 1.13, in `Current.MatrixStructure`.
-/
theorem false_of_regularPartL1Limit (b : MatrixPolarBlowupData M D x)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (h14 : b.RegularPartL1Limit h) : False := by
  have hout := b.localized_totalVariation_of_regularPartL1Limit h14
  have hle : ∀ n, (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).real univ ≤
      ((b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure -
        (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure).totalVariation.real
          univ := by
    intro n
    obtain ⟨S, hSm, hS0, hSc⟩ := b.localizedPositive_singular n
    have hT : (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))) Sᶜ = 0 := hout.2.1 hSc
    have hw : (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).real univ =
        (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).real Sᶜ := by
      rw [← measureReal_add_measureReal_compl hSm, measureReal_def, hS0, ENNReal.toReal_zero,
        zero_add]
    have hs := StrongConstancy.signedMeasure_apply_le_totalVariation
      ((b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure -
        (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure) hSm.compl
    rw [Measure.toSignedMeasure_sub_apply hSm.compl, measureReal_def (s := Sᶜ) (μ := (b.localizedTangent : Measure _)), hT,
      ENNReal.toReal_zero, sub_zero] at hs
    haveI : IsFiniteMeasure ((b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure -
        (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure).totalVariation := by
      unfold SignedMeasure.totalVariation
      infer_instance
    rw [hw]
    exact hs.trans (measureReal_mono (subset_univ _))
  have hzero : Tendsto (fun n => (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).real univ)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => measureReal_nonneg) hle hout.2.2
  have hmass : Tendsto (fun n => (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).real univ)
      atTop (𝓝 ((b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).real univ)) := by
    simpa only [b.mollifiedPositive_mass] using b.mollifiedPositive_mass_tendsto
  have he := tendsto_nhds_unique hmass hzero
  have hlow := (b.localizedTangent_mass_bounds).1
  rw [he] at hlow
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ d)⁻¹ := by positivity
  linarith

end MatrixPolarBlowupData
end GeometricMeasure
