import GeometricMeasure.Current.FirstOrderStructure

/-!
# Finite Normal Family

## Main results
Finite spanning families of normal one-dimensional currents.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Corollaries 1.12 and 1.13. The
equations use globally finite measures; local conclusions use interior tests.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace GeometricMeasure

namespace VectorMeasure
variable {X : Type*} [MeasurableSpace X] {r d : ℕ}
variable (R : Fin r → MeasureTheory.VectorMeasure X (EuclideanSpace ℝ (Fin d)))

/-- The common finite mass of a finite family of vector measures. -/
def familyMass : Measure X := ∑ i, (R i).variation

/-- Finiteness follows from the finite variations of the members of the family. -/
instance instIsFiniteMeasureFamilyMass : IsFiniteMeasure (familyMass R) := by
  unfold familyMass
  infer_instance

/-- Every member's variation is dominated by the common mass. -/
theorem variation_le_familyMass (i : Fin r) : (R i).variation ≤ familyMass R :=
  Finset.single_le_sum (f := fun j => (R j).variation)
    (fun _ _ => bot_le) (Finset.mem_univ i)

/--
A vector density with respect to the common mass, without any reference to the dominated measure.
-/
def familyDensity (i : Fin r) : X → EuclideanSpace ℝ (Fin d) :=
  rnDensity (R i) (familyMass R)

/-- The common-mass vector densities are integrable. -/
theorem integrable_familyDensity (i : Fin r) : Integrable (familyDensity R i) (familyMass R) :=
  integrable_rnDensity _ _

/-- Common-mass reconstruction follows from domination of every signed coordinate. -/
theorem withDensity_familyDensity (i : Fin r) :
    (familyMass R).withDensityᵥ (familyDensity R i) = R i := by
  apply withDensityᵥ_rnDensity
  intro a
  apply coord_absolutelyContinuous
  apply (absolutelyContinuous_iff_variation (R i) (familyMass R)).mpr
  exact Measure.absolutelyContinuous_of_le (variation_le_familyMass R i)

/-- The rectangular density has the vector densities as its rows. -/
def familyMatrixDensity (x : X) : RectMatrixSpace r d :=
  WithLp.toLp 2 (fun ij => familyDensity R ij.1 x ij.2)

/-- The rectangular matrix density is integrable. -/
theorem integrable_familyMatrixDensity : Integrable (familyMatrixDensity R) (familyMass R) := by
  apply integrable_piLp_iff.mpr
  intro ij
  exact (integrable_piLp_iff.mp (integrable_familyDensity R ij.1)) ij.2

/-- Stacking the family over its common mass produces a finite rectangular vector measure. -/
def familyMatrixMeasure : MeasureTheory.VectorMeasure X (RectMatrixSpace r d) :=
  (familyMass R).withDensityᵥ (familyMatrixDensity R)

/-- Extracting a row of the stacked rectangular measure recovers the original member. -/
@[simp] theorem rectRow_familyMatrixMeasure (i : Fin r) :
    rectRow (familyMatrixMeasure R) i = R i := by
  unfold rectRow familyMatrixMeasure linearImage
  rw [withDensityᵥ_mapRange _ (integrable_familyMatrixDensity R)]
  exact withDensity_familyDensity R i

/-- The stacked variation is the common mass weighted by the Frobenius norm of its density. -/
theorem variation_familyMatrixMeasure :
    (familyMatrixMeasure R).variation =
      (familyMass R).withDensity (fun x => ‖familyMatrixDensity R x‖ₑ) :=
  Measure.variation_withDensityᵥ (integrable_familyMatrixDensity R)

/-- Each rectangular row variation is absolutely continuous with respect to the full variation. -/
theorem variation_rectRow_absolutelyContinuous
    (N : MeasureTheory.VectorMeasure X (RectMatrixSpace r d)) (i : Fin r) :
    (rectRow N i).variation ≪ N.variation := by
  rw [rectRow, variation_linearImage]
  exact withDensity_absolutelyContinuous _ _

/--
The common mass is absolutely continuous with respect to the stacked variation, including for an
empty family.
-/
theorem familyMass_absolutelyContinuous_variation_familyMatrixMeasure :
    familyMass R ≪ (familyMatrixMeasure R).variation := by
  intro s hs
  have hi : ∀ i, (R i).variation s = 0 := fun i => by
    have h := variation_rectRow_absolutelyContinuous (familyMatrixMeasure R) i hs
    simpa only [rectRow_familyMatrixMeasure] using h
  simp only [familyMass, Measure.finsetSum_apply, hi, Finset.sum_const_zero]

/-- The stacked variation is absolutely continuous with respect to the common mass. -/
theorem variation_familyMatrixMeasure_absolutelyContinuous_familyMass :
    (familyMatrixMeasure R).variation ≪ familyMass R := by
  rw [variation_familyMatrixMeasure]
  exact withDensity_absolutelyContinuous _ _

/-- The original row polar is the normalized row of the rectangular polar. -/
theorem polarDensity_rectRow (N : MeasureTheory.VectorMeasure X (RectMatrixSpace r d)) (i : Fin r) :
    polarDensity (rectRow N i) =ᵐ[(rectRow N i).variation]
      (fun x => ‖RectMatrixSpace.row i (polar N x)‖⁻¹ • RectMatrixSpace.row i (polar N x)) := by
  exact (polar_ae_eq_polarDensity (rectRow N i)).symm.trans
    (polar_linearImage (RectMatrixSpace.row i) N)

end VectorMeasure

/-- Full Euclidean row span forces full column rank for every rectangular shape. -/
theorem rank_eq_of_span_rectRows_eq_top {r d : ℕ} (P : RectMatrixSpace r d)
    (h : Submodule.span ℝ (range fun i => RectMatrixSpace.row i P) = ⊤) :
    (RectMatrixSpace.coordinates P).rank = d := by
  have hle : (RectMatrixSpace.coordinates P).rank ≤ d := by
    simpa using Matrix.rank_le_card_width (RectMatrixSpace.coordinates P)
  by_contra hne
  have hlt : (RectMatrixSpace.coordinates P).rank < d := by omega
  obtain ⟨v, hn, hv⟩ := (rank_lt_iff_exists_mulVec_eq_zero _).mp hlt
  let ξ : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 v
  have hrow : ∀ i, inner ℝ (RectMatrixSpace.row i P) ξ = 0 := by
    intro i
    have hi := congrFun hv i
    simpa [Matrix.mulVec, dotProduct, RectMatrixSpace.coordinates,
      PiLp.inner_apply, RectMatrixSpace.row, ξ, mul_comm] using hi
  have hsub : Submodule.span ℝ (range fun i => RectMatrixSpace.row i P) ≤
      LinearMap.ker (innerSL ℝ ξ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply, real_inner_comm]
    exact hrow i
  rw [h] at hsub
  have hξ : ξ = 0 := inner_self_eq_zero.mp (hsub (Submodule.mem_top (x := ξ)))
  exact hn (congrArg WithLp.ofLp hξ)

/-- Under row domination, spanning original polars force full rank of the stacked polar. -/
theorem ae_rank_polar_familyMatrixMeasure_eq {r d : ℕ}
    (R : Fin r → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (hν : ∀ i, ν ≪ (R i).variation)
    (hspan : ∀ᵐ x ∂ν, Submodule.span ℝ (range fun i => polarDensity (R i) x) = ⊤) :
    ∀ᵐ x ∂ν, (RectMatrixSpace.coordinates
      (VectorMeasure.polar (VectorMeasure.familyMatrixMeasure R) x)).rank = d := by
  let N := VectorMeasure.familyMatrixMeasure R
  have hp : ∀ᵐ x ∂ν, ∀ i, polarDensity (R i) x =
      ‖RectMatrixSpace.row i (VectorMeasure.polar N x)‖⁻¹ •
        RectMatrixSpace.row i (VectorMeasure.polar N x) := by
    apply ae_all_iff.mpr
    intro i
    apply (hν i).ae_le
    change ∀ᵐ x ∂(R i).variation, polarDensity (R i) x =
      ‖RectMatrixSpace.row i (VectorMeasure.polar N x)‖⁻¹ •
        RectMatrixSpace.row i (VectorMeasure.polar N x)
    have hpol := VectorMeasure.polarDensity_rectRow (VectorMeasure.familyMatrixMeasure R) i
    simp only [VectorMeasure.rectRow_familyMatrixMeasure] at hpol
    filter_upwards [hpol] with x hx
    exact hx
  filter_upwards [hspan, hp] with x hx hp
  apply rank_eq_of_span_rectRows_eq_top
  rw [eq_top_iff, ← hx, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  change polarDensity (R i) x ∈ _
  rw [hp i]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/--
A finite family of any size yields absolute continuity under local domination and spanning. The
measures and their divergences are globally finite; this is not the Radon extension. The argument
follows the method of De Philippis–Rindler, Corollary 1.12.

Following the method of De Philippis–Rindler (2016), Corollaries 1.12 and 1.13; extended to
arbitrary dominated positive measures.
-/
theorem restrict_absolutelyContinuous_volume_of_finite_span_polar_on {r d : ℕ}
    (R : Fin r → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hdiv : ∀ i, HasMeasureDivergenceOn (R i) (D i) U)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (hν : ∀ i, ν.restrict U ≪ (R i).variation)
    (hspan : ∀ᵐ x ∂ν.restrict U,
      Submodule.span ℝ (range fun i => polarDensity (R i) x) = ⊤) :
    ν.restrict U ≪ volume := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact absolutelyContinuous_volume_of_dimension_zero _
  by_cases hr : r = 0
  · subst r
    have he : ∀ᵐ x ∂ν.restrict U, False := by
      filter_upwards [hspan] with x hx
      have hbot : (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) = ⊤ := by simpa using hx
      haveI : NeZero d := ⟨hd.ne'⟩
      exact bot_ne_top hbot
    have hz : ν.restrict U = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      simpa using (ae_iff.mp he)
    rw [hz]
    exact Measure.AbsolutelyContinuous.zero _
  let i : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
  let N := VectorMeasure.familyMatrixMeasure R
  have hN : HasRectMeasureDivergenceOn N D U := by
    intro j
    simpa only [N, VectorMeasure.rectRow_familyMatrixMeasure] using hdiv j
  have hνN : ν.restrict U ≪ N.variation := by
    apply (hν i).trans
    simpa only [N, VectorMeasure.rectRow_familyMatrixMeasure] using
      VectorMeasure.variation_rectRow_absolutelyContinuous N i
  have hs := HasRectMeasureDivergenceOn.ae_rank_polar_le N D hU hN
  rw [ae_restrict_iff' hU.measurableSet] at hs
  apply absolutelyContinuous_of_ae_singularPart (μ := N.variation)
    (p := fun x => x ∈ U → (RectMatrixSpace.coordinates (VectorMeasure.polar N x)).rank ≤ d - 1)
    hνN hs
  filter_upwards [ae_restrict_mem hU.measurableSet,
    ae_rank_polar_familyMatrixMeasure_eq R (ν.restrict U) hν hspan] with x hx hrank hbad
  have hb := hbad hx
  change (RectMatrixSpace.coordinates (VectorMeasure.polar N x)).rank = d at hrank
  omega

/--
A globally normal finite family of any size forces absolute continuity of an arbitrary positive
measure dominated by every member variation, when the member polars span the spatial space almost
everywhere for that measure.

Following the method of De Philippis–Rindler (2016), Corollaries 1.12 and 1.13; extended to
arbitrary dominated positive measures.
-/
theorem absolutelyContinuous_volume_of_finite_span_polar {r d : ℕ}
    (R : Fin r → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hdiv : ∀ i, HasMeasureDivergence (R i) (D i))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (hν : ∀ i, ν ≪ (R i).variation)
    (hspan : ∀ᵐ x ∂ν, Submodule.span ℝ (range fun i => polarDensity (R i) x) = ⊤) :
    ν ≪ volume := by
  simpa using restrict_absolutelyContinuous_volume_of_finite_span_polar_on R D isOpen_univ
    (fun i φ _ => hdiv i φ) ν (by simpa using hν) (by simpa using hspan)

/--
For a globally normal finite family, a positive measure restricted to any set is absolutely
continuous if it is dominated by every member variation and the member polars span the spatial space
almost everywhere for the restricted measure.

Following the method of De Philippis–Rindler (2016), Corollaries 1.12 and 1.13; extended to
arbitrary dominated positive measures.
-/
theorem restrict_absolutelyContinuous_volume_of_finite_span_polar {r d : ℕ}
    (R : Fin r → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hdiv : ∀ i, HasMeasureDivergence (R i) (D i))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hν : ∀ i, ν.restrict S ≪ (R i).variation)
    (hspan : ∀ᵐ x ∂ν.restrict S,
      Submodule.span ℝ (range fun i => polarDensity (R i) x) = ⊤) :
    ν.restrict S ≪ volume :=
  absolutelyContinuous_volume_of_finite_span_polar R D hdiv (ν.restrict S) hν hspan

end GeometricMeasure
