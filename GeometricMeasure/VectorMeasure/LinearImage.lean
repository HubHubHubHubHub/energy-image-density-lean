import GeometricMeasure.VectorMeasure.Matrix

/-!
# Linear Image

## Main results
Linear images, polar reconstruction, and conic transfer for finite Euclidean vector measures.

Source: De Philippis–Rindler (2016), cor. 1.13, pp. 5 and 15; rectangular extension by linear images
and maximal minors.
-/

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal

namespace GeometricMeasure.VectorMeasure

variable {X : Type*} [MeasurableSpace X]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The action of a continuous linear map on the values of a vector measure. -/
def linearImage (L : E →L[ℝ] F) (M : VectorMeasure X E) : VectorMeasure X F :=
  M.mapRange L.toLinearMap.toAddMonoidHom L.continuous

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The linear image evaluated on a set is the linear map of the measure value. -/
@[simp] theorem linearImage_apply (L : E →L[ℝ] F) (M : VectorMeasure X E)
    (s : Set X) : linearImage L M s = L (M s) := rfl

/-- An orthonormal coordinate isometry for a finite dimensional real inner product space. -/
def valueCoordinates (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  (stdOrthonormalBasis ℝ E).repr

/-- The vector measure transported to orthonormal value coordinates. -/
def coordinateMeasure (M : VectorMeasure X E) :=
  linearImage (valueCoordinates E).toLinearIsometry.toContinuousLinearMap M

/-- Transport to orthonormal value coordinates preserves variation. -/
theorem variation_coordinateMeasure (M : VectorMeasure X E) :
    (coordinateMeasure M).variation = M.variation :=
  variation_mapRange_linearIsometryEquiv M (valueCoordinates E)

/-- The variation of a vector measure with finite dimensional Euclidean values is finite. -/
instance instIsFiniteMeasureVariation (M : VectorMeasure X E) : IsFiniteMeasure M.variation := by
  rw [← variation_coordinateMeasure M]
  exact isFiniteMeasure_variation (coordinateMeasure M)

/-- The polar representative obtained from the coordinate polar by the inverse value isometry. -/
def polar (M : VectorMeasure X E) : X → E :=
  fun x => (valueCoordinates E).symm (polarDensity (coordinateMeasure M) x)

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- The chosen polar representative is measurable for the Borel structure on the values. -/
theorem measurable_polar (M : VectorMeasure X E) : Measurable (polar M) :=
  (valueCoordinates E).symm.continuous.measurable.comp (measurable_polarDensity _)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The chosen polar representative is integrable against the variation. -/
theorem integrable_polar (M : VectorMeasure X E) : Integrable (polar M) M.variation := by
  rw [← variation_coordinateMeasure M]
  exact (valueCoordinates E).symm.toLinearIsometry.toContinuousLinearMap.integrable_comp
    (integrable_polarDensity _)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The variation with the chosen polar as vector density equals the original measure. -/
theorem withDensity_polar (M : VectorMeasure X E) :
    M.variation.withDensityᵥ (polar M) = M := by
  apply VectorMeasure.ext
  intro s hs
  rw [withDensityᵥ_apply (integrable_polar M) hs]
  change (∫ x in s, (valueCoordinates E).symm.toLinearIsometry.toContinuousLinearMap
    (polarDensity (coordinateMeasure M) x) ∂M.variation) = M s
  rw [← variation_coordinateMeasure M,
    (valueCoordinates E).symm.toLinearIsometry.toContinuousLinearMap.integral_comp_comm
      (integrable_polarDensity (coordinateMeasure M)).restrict]
  have h := congrArg (fun v => v s) (withDensityᵥ_polarDensity (coordinateMeasure M))
  rw [withDensityᵥ_apply (integrable_polarDensity _) hs] at h
  rw [h]
  exact (valueCoordinates E).symm_apply_apply (M s)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The chosen polar has norm one almost everywhere for the variation. -/
theorem ae_norm_polar_eq_one (M : VectorMeasure X E) : ∀ᵐ x ∂M.variation, ‖polar M x‖ = 1 := by
  rw [← variation_coordinateMeasure M]
  simpa only [polar, LinearIsometryEquiv.norm_map] using norm_polarDensity_ae (coordinateMeasure M)

omit [MeasurableSpace E] [BorelSpace E] in
/--
Every integrable density representing the measure against its variation agrees with the polar almost
everywhere for that variation.
-/
theorem polar_ae_eq_of_withDensity_eq (M : VectorMeasure X E) {q : X → E}
    (hq : Integrable q M.variation) (hr : M.variation.withDensityᵥ q = M) :
    polar M =ᵐ[M.variation] q :=
  (integrable_polar M).ae_eq_of_withDensityᵥ_eq hq ((withDensity_polar M).trans hr.symm)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/--
The linear image is the vector density obtained by applying the linear map to the polar, against the
original variation.
-/
theorem linearImage_eq_withDensity_polar (L : E →L[ℝ] F) (M : VectorMeasure X E) :
    linearImage L M = M.variation.withDensityᵥ (fun x => L (polar M x)) := by
  unfold linearImage
  conv_lhs => rw [← withDensity_polar M]
  exact withDensityᵥ_mapRange _ (integrable_polar M) L

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/--
The image variation equals the original variation weighted by the norm of the linear image of the
original polar, including its zero set.
-/
theorem variation_linearImage (L : E →L[ℝ] F) (M : VectorMeasure X E) :
    (linearImage L M).variation =
      M.variation.withDensity (fun x => ENNReal.ofReal ‖L (polar M x)‖) := by
  rw [linearImage_eq_withDensity_polar, Measure.variation_withDensityᵥ
    (L.integrable_comp (integrable_polar M))]
  simp only [ofReal_norm]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/--
The polar of an integrable vector density is its norm inverse times that density, almost
everywhere for its variation; the inverse at zero is zero.
-/
theorem polar_withDensity (μ : Measure X) {f : X → F} (hf : Integrable f μ) :
    polar (μ.withDensityᵥ f) =ᵐ[(μ.withDensityᵥ f).variation]
      (fun x => ‖f x‖⁻¹ • f x) := by
  let q : X → F := fun x => ‖f x‖⁻¹ • f x
  have hq : AEStronglyMeasurable q (μ.withDensityᵥ f).variation := by
    rw [Measure.variation_withDensityᵥ hf]
    exact (hf.aestronglyMeasurable.norm.inv₀.smul hf.aestronglyMeasurable).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hi : Integrable q (μ.withDensityᵥ f).variation := by
    apply Integrable.of_bound hq 1
    filter_upwards with x using by simp [q, norm_smul, inv_mul_le_one]
  have hprod : (fun x => (‖f x‖ₑ).toReal • q x) = f := by
    funext x
    by_cases hx : f x = 0
    · simp [q, hx]
    · simp only [q, toReal_enorm, smul_smul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  have hfg : Integrable (fun x => (‖f x‖ₑ).toReal • q x) μ := by
    simpa only [hprod] using hf
  have hflt : ∀ᵐ x ∂μ, ‖f x‖ₑ < ∞ := by
    filter_upwards with x using enorm_lt_top
  apply polar_ae_eq_of_withDensity_eq _ hi
  rw [Measure.variation_withDensityᵥ hf]
  exact (withDensityᵥ_smul_eq_withDensityᵥ_withDensity'
    hf.aestronglyMeasurable.enorm hflt hfg).symm.trans
      (congrArg (μ.withDensityᵥ) hprod)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/--
The image polar is the normalized linear image of the original polar, almost everywhere for the
image variation.
-/
theorem polar_linearImage (L : E →L[ℝ] F) (M : VectorMeasure X E) :
    polar (linearImage L M) =ᵐ[(linearImage L M).variation]
      (fun x => ‖L (polar M x)‖⁻¹ • L (polar M x)) := by
  simpa only [linearImage_eq_withDensity_polar] using
    polar_withDensity M.variation (L.integrable_comp (integrable_polar M))

/--
Weighting commutes with the singular part relative to a sigma-finite reference when both the
original and weighted measures are finite.
-/
theorem singularPart_withDensity (μ ν : Measure X) [IsFiniteMeasure μ] [SigmaFinite ν]
    (w : X → ℝ≥0∞) [IsFiniteMeasure (μ.withDensity w)] :
    (μ.withDensity w).singularPart ν = (μ.singularPart ν).withDensity w := by
  let A := (ν.withDensity (μ.rnDeriv ν)).withDensity w
  let S := (μ.singularPart ν).withDensity w
  have hsum : A + S = μ.withDensity w := by
    rw [← withDensity_add_measure, Measure.rnDeriv_add_singularPart]
  haveI : IsFiniteMeasure A := isFiniteMeasure_of_le (μ.withDensity w)
    (hsum ▸ Measure.le_add_right (le_refl A))
  haveI : IsFiniteMeasure S := isFiniteMeasure_of_le (μ.withDensity w)
    (hsum ▸ Measure.le_add_left (le_refl S))
  have hA : A ≪ ν := (withDensity_absolutelyContinuous _ _).trans
    (withDensity_absolutelyContinuous _ _)
  have hS : S ⟂ₘ ν := (μ.mutuallySingular_singularPart ν).mono_ac
    (withDensity_absolutelyContinuous _ _) Measure.AbsolutelyContinuous.rfl
  rw [← hsum, Measure.singularPart_add, Measure.singularPart_eq_zero_of_ac hA,
    Measure.singularPart_eq_self.mpr hS, zero_add]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/--
The singular image variation is the original singular variation weighted by the norm of the linear
image of its polar, for a sigma-finite reference.
-/
theorem singularPart_variation_linearImage (L : E →L[ℝ] F) (M : VectorMeasure X E)
    (ν : Measure X) [SigmaFinite ν] :
    (linearImage L M).variation.singularPart ν =
      (M.variation.singularPart ν).withDensity
        (fun x => ENNReal.ofReal ‖L (polar M x)‖) := by
  haveI : IsFiniteMeasure (M.variation.withDensity
      (fun x => ENNReal.ofReal ‖L (polar M x)‖)) := by
    rw [← variation_linearImage L M]
    infer_instance
  rw [variation_linearImage, singularPart_withDensity]

/--
The norm of the linear image of the original polar times the image polar recovers that linear image
almost everywhere for the original variation, including its zero set.
-/
theorem ae_norm_smul_polar_linearImage (L : E →L[ℝ] F) (M : VectorMeasure X E) :
    ∀ᵐ x ∂M.variation,
      ‖L (polar M x)‖ • polar (linearImage L M) x = L (polar M x) := by
  have h := polar_linearImage L M
  rw [variation_linearImage] at h
  have hw := (L.continuous.measurable.comp (measurable_polar M)).norm.ennreal_ofReal
  have hn := (ae_withDensity_iff hw).mp h
  filter_upwards [hn] with x hx
  by_cases hz : L (polar M x) = 0
  · simp [hz]
  · have hg : 0 < ‖L (polar M x)‖ := norm_pos_iff.mpr hz
    rw [hx (ne_of_gt (ENNReal.ofReal_pos.mpr hg)), smul_smul,
      mul_inv_cancel₀ hg.ne', one_smul]

/-- The singular vector part is the original polar as density against the singular variation. -/
def singularVector (M : VectorMeasure X E) (ν : Measure X) : VectorMeasure X E :=
  (M.variation.singularPart ν).withDensityᵥ (polar M)

/-- Linear images commute with the singular vector part for a sigma-finite reference. -/
theorem singularVector_linearImage (L : E →L[ℝ] F) (M : VectorMeasure X E)
    (ν : Measure X) [SigmaFinite ν] :
    singularVector (linearImage L M) ν = linearImage L (singularVector M ν) := by
  let σ := M.variation.singularPart ν
  let w := fun x => ENNReal.ofReal ‖L (polar M x)‖
  let q := polar (linearImage L M)
  have hi : Integrable (polar M) σ :=
    (integrable_polar M).mono_measure (M.variation.singularPart_le ν)
  have hp : (fun x => (w x).toReal • q x) =ᵐ[σ] (fun x => L (polar M x)) := by
    have h := (Measure.absolutelyContinuous_of_le (M.variation.singularPart_le ν)).ae_le
      (ae_norm_smul_polar_linearImage L M)
    filter_upwards [h] with x hx
    simpa only [w, q, ENNReal.toReal_ofReal (norm_nonneg _)] using hx
  have hprod : Integrable (fun x => (w x).toReal • q x) σ :=
    (L.integrable_comp hi).congr hp.symm
  have hw : Measurable w :=
    (L.continuous.measurable.comp (measurable_polar M)).norm.ennreal_ofReal
  have hfinite : ∀ᵐ x ∂σ, w x < ∞ := by
    filter_upwards with x using ENNReal.ofReal_lt_top
  calc
    singularVector (linearImage L M) ν = (σ.withDensity w).withDensityᵥ q := by
      rw [singularVector, singularPart_variation_linearImage]
    _ = σ.withDensityᵥ (fun x => (w x).toReal • q x) :=
      (withDensityᵥ_smul_eq_withDensityᵥ_withDensity' hw.aemeasurable hfinite hprod).symm
    _ = σ.withDensityᵥ (fun x => L (polar M x)) := by
      apply VectorMeasure.ext
      intro s hs
      rw [withDensityᵥ_apply hprod hs, withDensityᵥ_apply (L.integrable_comp hi) hs]
      exact integral_congr_ae (ae_restrict_of_ae hp)
    _ = linearImage L (singularVector M ν) := (withDensityᵥ_mapRange σ hi L).symm

/--
On a set, membership of the image polar in a cone containing zero and stable under positive scaling
transfers from the singular image variation to membership of the linear image of the original polar
under the original singular variation. The reference is sigma-finite; neither the cone nor the set
needs to be measurable.

The proof uses polar reconstruction under linear maps and positive homogeneity of the cone.
-/
theorem ae_apply_polar_mem_of_polar_linearImage_mem_on (L : E →L[ℝ] F) (M : VectorMeasure X E)
    (ν : Measure X) [SigmaFinite ν] (C : Set F) (h0 : (0 : F) ∈ C)
    (hcone : ∀ a : ℝ, 0 < a → ∀ v ∈ C, a • v ∈ C) (U : Set X)
    (hN : ∀ᵐ x ∂(linearImage L M).variation.singularPart ν,
      x ∈ U → polar (linearImage L M) x ∈ C) :
    ∀ᵐ x ∂M.variation.singularPart ν, x ∈ U → L (polar M x) ∈ C := by
  rw [singularPart_variation_linearImage] at hN
  have hw := (L.continuous.measurable.comp (measurable_polar M)).norm.ennreal_ofReal
  have h := (ae_withDensity_iff hw).mp hN
  have hr := (Measure.absolutelyContinuous_of_le (M.variation.singularPart_le ν)).ae_le
    (ae_norm_smul_polar_linearImage L M)
  filter_upwards [h, hr] with x hx hrec hxU
  by_cases hz : L (polar M x) = 0
  · simpa only [hz] using h0
  · have hg : 0 < ‖L (polar M x)‖ := norm_pos_iff.mpr hz
    rw [← hrec]
    exact hcone _ hg _ (hx (ne_of_gt (ENNReal.ofReal_pos.mpr hg)) hxU)

/--
Membership of the image polar in a cone containing zero and stable under positive scaling
transfers from the singular image variation to membership of the linear image of the original polar
under the
original singular variation, for a sigma-finite reference.

The proof uses polar reconstruction under linear maps and positive homogeneity of the cone.
-/
theorem ae_apply_polar_mem_of_polar_linearImage_mem (L : E →L[ℝ] F) (M : VectorMeasure X E)
    (ν : Measure X) [SigmaFinite ν] (C : Set F) (h0 : (0 : F) ∈ C)
    (hcone : ∀ a : ℝ, 0 < a → ∀ v ∈ C, a • v ∈ C)
    (hN : ∀ᵐ x ∂(linearImage L M).variation.singularPart ν,
      polar (linearImage L M) x ∈ C) :
    ∀ᵐ x ∂M.variation.singularPart ν, L (polar M x) ∈ C := by
  simpa using ae_apply_polar_mem_of_polar_linearImage_mem_on L M ν C h0 hcone univ (by simpa using hN)

/--
Away from the zero linear image of the original polar, the normalized formula for the image polar
holds almost everywhere for the original variation.
-/
theorem polar_linearImage_of_apply_ne_zero (L : E →L[ℝ] F) (M : VectorMeasure X E) :
    ∀ᵐ x ∂M.variation, L (polar M x) ≠ 0 →
      polar (linearImage L M) x = ‖L (polar M x)‖⁻¹ • L (polar M x) := by
  filter_upwards [ae_norm_smul_polar_linearImage L M] with x hx hn
  have h := congrArg (fun v : F => ‖L (polar M x)‖⁻¹ • v) hx
  simpa only [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn), one_smul] using h

omit [MeasurableSpace E] [BorelSpace E] in
/--
The singular vector part has exactly the singular variation of the original measure, for any
reference measure.
-/
theorem variation_singularVector (M : VectorMeasure X E) (ν : Measure X) :
    (singularVector M ν).variation = M.variation.singularPart ν := by
  have hi := (integrable_polar M).mono_measure (M.variation.singularPart_le ν)
  rw [singularVector, Measure.variation_withDensityᵥ hi]
  have hn := (Measure.absolutelyContinuous_of_le (M.variation.singularPart_le ν)).ae_le
    (ae_norm_polar_eq_one M)
  have hw : (fun x => ‖polar M x‖ₑ) =ᵐ[M.variation.singularPart ν]
      (fun _ => (1 : ℝ≥0∞)) := by
    filter_upwards [hn] with x hx
    simp [← ofReal_norm, hx]
  simpa using withDensity_congr_ae hw

end GeometricMeasure.VectorMeasure
