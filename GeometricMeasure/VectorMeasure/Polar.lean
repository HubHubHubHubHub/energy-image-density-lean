import GeometricMeasure.VectorMeasure.FiniteDimensional

/-! Polar decomposition for Euclidean vector measures. The total variation and
the variation formula for a density are supplied by Mathlib. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GeometricMeasure

variable {X : Type*} [MeasurableSpace X] {m : ℕ}

/-- A density representing a measure with respect to its variation is a.e. unit. -/
theorem norm_ae_eq_one_of_withDensityᵥ_eq
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) [SigmaFinite M.variation]
    {p : X → EuclideanSpace ℝ (Fin m)} (hp : Integrable p M.variation)
    (hrep : M.variation.withDensityᵥ p = M) :
    ∀ᵐ x ∂M.variation, ‖p x‖ = 1 := by
  have hv : M.variation.withDensity (fun x => ‖p x‖ₑ) = M.variation := by
    rw [← Measure.variation_withDensityᵥ hp, hrep]
  have hnorm : (fun x => ‖p x‖ₑ) =ᵐ[M.variation] (fun _ => (1 : ℝ≥0∞)) :=
    (withDensity_eq_iff_of_sigmaFinite hp.aestronglyMeasurable.enorm
      measurable_const.aemeasurable).mp (by simpa using hv)
  filter_upwards [hnorm] with x hx
  simpa using congrArg ENNReal.toReal hx

/-- Polar decomposition under the explicit finite-variation hypothesis. -/
theorem exists_polar_of_finiteVariation
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) [IsFiniteMeasure M.variation] :
    ∃ p : X → EuclideanSpace ℝ (Fin m), Measurable p ∧ Integrable p M.variation ∧
      M.variation.withDensityᵥ p = M ∧ (∀ᵐ x ∂M.variation, ‖p x‖ = 1) := by
  have hrep := withDensityᵥ_rnDensity M M.variation
    (coord_absolutelyContinuous_variation M)
  exact ⟨rnDensity M M.variation, measurable_rnDensity M M.variation,
    integrable_rnDensity M M.variation, hrep,
    norm_ae_eq_one_of_withDensityᵥ_eq M (integrable_rnDensity M M.variation) hrep⟩

/-- Uniqueness needs integrability and reconstruction, but no unit-norm hypothesis. -/
theorem polar_ae_unique (M : VectorMeasure X (EuclideanSpace ℝ (Fin m)))
    {p q : X → EuclideanSpace ℝ (Fin m)}
    (hp : Integrable p M.variation) (hq : Integrable q M.variation)
    (hMp : M.variation.withDensityᵥ p = M) (hMq : M.variation.withDensityᵥ q = M) :
    p =ᵐ[M.variation] q :=
  hp.ae_eq_of_withDensityᵥ_eq hq (hMp.trans hMq.symm)

/-- The zero vector is a valid polar representative for the zero measure. -/
theorem zero_is_polar :
    Measurable (fun _ : X => (0 : EuclideanSpace ℝ (Fin m))) ∧
      Integrable (fun _ : X => (0 : EuclideanSpace ℝ (Fin m)))
        (0 : VectorMeasure X (EuclideanSpace ℝ (Fin m))).variation ∧
      (0 : VectorMeasure X (EuclideanSpace ℝ (Fin m))).variation.withDensityᵥ
        (fun _ : X => (0 : EuclideanSpace ℝ (Fin m))) = 0 ∧
      (∀ᵐ _x ∂(0 : VectorMeasure X (EuclideanSpace ℝ (Fin m))).variation,
        ‖(0 : EuclideanSpace ℝ (Fin m))‖ = 1) := by
  simp
  exact withDensityᵥ_zero

/-- The empty Euclidean dimension has zero mass, so the unit-norm assertion is vacuous. -/
theorem variation_eq_zero_of_dimension_zero
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin 0))) : M.variation = 0 := by
  rw [eq_zero_of_dimension_zero M, VectorMeasure.variation_zero]

/-- Unconditional polar decomposition in finite Euclidean dimension. -/
theorem exists_polar (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    ∃ p : X → EuclideanSpace ℝ (Fin m), Measurable p ∧ Integrable p M.variation ∧
      M.variation.withDensityᵥ p = M ∧ (∀ᵐ x ∂M.variation, ‖p x‖ = 1) :=
  exists_polar_of_finiteVariation M

/-- A fixed measurable polar representative, chosen from the existence theorem.
Only its a.e. class is intrinsic; no pointwise normalization on null sets is claimed. -/
noncomputable def polarDensity (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    X → EuclideanSpace ℝ (Fin m) :=
  Classical.choose (exists_polar M)

theorem measurable_polarDensity (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    Measurable (polarDensity M) :=
  (Classical.choose_spec (exists_polar M)).1

theorem integrable_polarDensity (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    Integrable (polarDensity M) M.variation :=
  (Classical.choose_spec (exists_polar M)).2.1

theorem withDensityᵥ_polarDensity (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    M.variation.withDensityᵥ (polarDensity M) = M :=
  (Classical.choose_spec (exists_polar M)).2.2.1

theorem eq_withDensityᵥ_polarDensity (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    M = M.variation.withDensityᵥ (polarDensity M) :=
  (withDensityᵥ_polarDensity M).symm

theorem norm_polarDensity_ae (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    ∀ᵐ x ∂M.variation, ‖polarDensity M x‖ = 1 :=
  (Classical.choose_spec (exists_polar M)).2.2.2

/-- Identification of the chosen representative with any integrable density of M. -/
theorem polarDensity_ae_eq (M : VectorMeasure X (EuclideanSpace ℝ (Fin m)))
    {q : X → EuclideanSpace ℝ (Fin m)} (hq : Integrable q M.variation)
    (hrep : M.variation.withDensityᵥ q = M) : polarDensity M =ᵐ[M.variation] q :=
  polar_ae_unique M (integrable_polarDensity M) hq (withDensityᵥ_polarDensity M) hrep

theorem polarDensity_ae_eq_rnDensity (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    polarDensity M =ᵐ[M.variation] rnDensity M M.variation :=
  polarDensity_ae_eq M (integrable_rnDensity M M.variation)
    (withDensityᵥ_rnDensity M M.variation (coord_absolutelyContinuous_variation M))

/-- The chosen representative of zero agrees a.e. with zero, without a pointwise claim. -/
theorem polarDensity_zero_ae :
    polarDensity (0 : VectorMeasure X (EuclideanSpace ℝ (Fin m))) =ᵐ[
      (0 : VectorMeasure X (EuclideanSpace ℝ (Fin m))).variation] 0 := by
  simp
  exact Filter.eventually_bot

@[simp] theorem polarDensity_dimension_zero
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin 0))) : polarDensity M = 0 :=
  Subsingleton.elim _ _

/-- An a.e. strongly measurable, a.e. unit density against a finite measure is integrable. -/
theorem integrable_of_norm_one (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → EuclideanSpace ℝ (Fin m)} (hf : AEStronglyMeasurable f μ)
    (hnorm : ∀ᵐ x ∂μ, ‖f x‖ = 1) : Integrable f μ :=
  Integrable.of_bound hf 1 (hnorm.mono (fun _ hx => hx.le))

/--
For an a.e. strongly measurable unit density against a finite measure, the variation of the
represented vector measure equals that base measure.
-/
theorem variation_withDensityᵥ_eq_of_norm_one (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → EuclideanSpace ℝ (Fin m)} (hf : AEStronglyMeasurable f μ)
    (hnorm : ∀ᵐ x ∂μ, ‖f x‖ = 1) : (μ.withDensityᵥ f).variation = μ := by
  rw [Measure.variation_withDensityᵥ (integrable_of_norm_one μ hf hnorm)]
  have h : (fun x => ‖f x‖ₑ) =ᵐ[μ] (fun _ => (1 : ℝ≥0∞)) := by
    filter_upwards [hnorm] with x hx
    simp [← ofReal_norm, hx]
  simpa using withDensity_congr_ae h

/--
The polar of an integrable density equals its normalization almost everywhere for the
variation of the represented vector measure. The inverse of zero
is zero, so the formula also specifies zero on the zero set of the density.
The base measure need not be finite or sigma-finite.
-/
theorem polar_eq_normalize (μ : Measure X) {f : X → EuclideanSpace ℝ (Fin m)}
    (hf : Integrable f μ) :
    polarDensity (μ.withDensityᵥ f) =ᵐ[(μ.withDensityᵥ f).variation]
      (fun x => ‖f x‖⁻¹ • f x) := by
  let q : X → EuclideanSpace ℝ (Fin m) := fun x => ‖f x‖⁻¹ • f x
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
  have hrep : (μ.withDensityᵥ f).variation.withDensityᵥ q = μ.withDensityᵥ f := by
    rw [Measure.variation_withDensityᵥ hf]
    exact (withDensityᵥ_smul_eq_withDensityᵥ_withDensity'
      hf.aestronglyMeasurable.enorm hflt hfg).symm.trans
        (congrArg (μ.withDensityᵥ) hprod)
  exact polarDensity_ae_eq (μ.withDensityᵥ f) hi hrep

end GeometricMeasure
