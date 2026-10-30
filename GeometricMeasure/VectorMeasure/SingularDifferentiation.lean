import GeometricMeasure.VectorMeasure.Differentiation
import GeometricMeasure.VectorMeasure.Matrix

/-! Differentiation at the scale of the singular part of the variation.
The auxiliary family is countable and locally finite; its finite case is automatic. -/

noncomputable section
open MeasureTheory Filter Metric
open scoped ENNReal Topology

namespace GeometricMeasure

variable {d m : ℕ}
variable (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
variable (ν : Measure (EuclideanSpace ℝ (Fin d)))

theorem ae_tendsto_acPart_singular_closedBall_ratio :
    ∀ᵐ x ∂M.variation.singularPart ν, Tendsto
      (fun r => (ν.withDensity (M.variation.rnDeriv ν)) (closedBall x r) /
        (M.variation.singularPart ν) (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hs := ((M.variation.mutuallySingular_singularPart ν).mono_ac
    (Measure.AbsolutelyContinuous.refl _)
    (withDensity_absolutelyContinuous ν (M.variation.rnDeriv ν))).symm
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv
    (ν.withDensity (M.variation.rnDeriv ν)) (M.variation.singularPart ν),
    hs.rnDeriv_ae_eq_zero] with x hx hz
  simpa only [hz, Pi.zero_apply] using hx

theorem ae_tendsto_acPart_singular_closedBall_ratio_real :
    ∀ᵐ x ∂M.variation.singularPart ν, Tendsto
      (fun r => (ν.withDensity (M.variation.rnDeriv ν)).real (closedBall x r) /
        (M.variation.singularPart ν).real (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_acPart_singular_closedBall_ratio M ν] with x hx
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_zero, Measure.real]
    using (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hx

theorem ae_tendsto_variation_singular_closedBall_ratio
    [M.variation.HaveLebesgueDecomposition ν] :
    ∀ᵐ x ∂M.variation.singularPart ν, Tendsto
      (fun r => M.variation (closedBall x r) /
        (M.variation.singularPart ν) (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  filter_upwards [ae_tendsto_acPart_singular_closedBall_ratio M ν,
    ae_eventually_closedBall_mass_pos (M.variation.singularPart ν)] with x hx hp
  have hlim : Tendsto (fun r => 1 +
      (ν.withDensity (M.variation.rnDeriv ν)) (closedBall x r) /
        (M.variation.singularPart ν) (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.add hx
  apply hlim.congr'
  filter_upwards [hp] with r hr
  have heq := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin d)) => μ (closedBall x r))
    (M.variation.haveLebesgueDecomposition_add ν)
  simp only [Measure.add_apply] at heq
  rw [heq, ENNReal.add_div, ENNReal.div_self hr.ne'
    (measure_ne_top (M.variation.singularPart ν) _)]

theorem ae_tendsto_variation_singular_closedBall_ratio_real
    [M.variation.HaveLebesgueDecomposition ν] :
    ∀ᵐ x ∂M.variation.singularPart ν, Tendsto
      (fun r => M.variation.real (closedBall x r) /
        (M.variation.singularPart ν).real (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  filter_upwards [ae_tendsto_variation_singular_closedBall_ratio M ν] with x hx
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one, Measure.real]
    using (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp hx

/-- The explicit bound by two used for the absolutely continuous contribution. -/
theorem lintegral_polar_sub_le_two_mul
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (hμ : μ ≤ M.variation)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ‖polarDensity M x‖ = 1)
    (A : Set (EuclideanSpace ℝ (Fin d))) :
    (∫⁻ y in A, ‖polarDensity M y - polarDensity M x‖ₑ ∂μ) ≤ 2 * μ A := by
  have hu := (Measure.absolutelyContinuous_of_le hμ).ae_le (norm_polarDensity_ae M)
  have hi : ∀ᵐ y ∂μ, ‖polarDensity M y - polarDensity M x‖ₑ ≤ 2 := by
    filter_upwards [hu] with y hy
    have hn := norm_sub_le (polarDensity M y) (polarDensity M x)
    rw [hy, hx] at hn
    calc
      ‖polarDensity M y - polarDensity M x‖ₑ =
          ENNReal.ofReal ‖polarDensity M y - polarDensity M x‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (1 + 1) := ENNReal.ofReal_le_ofReal hn
      _ = 2 := by norm_num
  calc
    (∫⁻ y in A, ‖polarDensity M y - polarDensity M x‖ₑ ∂μ) ≤
        ∫⁻ _y in A, (2 : ℝ≥0∞) ∂μ := lintegral_mono_ae (ae_restrict_of_ae hi)
    _ = 2 * μ A := by simp

theorem ae_tendsto_polar_singular_closedBall_error_enorm
    [M.variation.HaveLebesgueDecomposition ν] :
    ∀ᵐ x ∂M.variation.singularPart ν, Tendsto
      (fun r => (∫⁻ y in closedBall x r, ‖polarDensity M y - polarDensity M x‖ₑ
        ∂M.variation) / (M.variation.singularPart ν) (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hu := (Measure.absolutelyContinuous_of_le (M.variation.singularPart_le ν)).ae_le
    (norm_polarDensity_ae M)
  filter_upwards [ae_tendsto_closedBall_lintegral_enorm_sub_div _
    (integrable_polarDensity_lebesgueSingularMeasure M ν),
    ae_tendsto_acPart_singular_closedBall_ratio M ν, hu] with x hs ha hx
  have htwo := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) ha (Or.inr (by norm_num))
  have hsum : Tendsto (fun r =>
      (∫⁻ y in closedBall x r, ‖polarDensity M y - polarDensity M x‖ₑ
        ∂M.variation.singularPart ν) / (M.variation.singularPart ν) (closedBall x r) +
      2 * ((ν.withDensity (M.variation.rnDeriv ν)) (closedBall x r) /
        (M.variation.singularPart ν) (closedBall x r)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using hs.add htwo
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hsum ε hε] with r hr
  apply le_trans ?_ hr
  have hsplit :
      (∫⁻ y in closedBall x r, ‖polarDensity M y - polarDensity M x‖ₑ ∂M.variation) =
      (∫⁻ y in closedBall x r, ‖polarDensity M y - polarDensity M x‖ₑ
        ∂M.variation.singularPart ν) +
      (∫⁻ y in closedBall x r, ‖polarDensity M y - polarDensity M x‖ₑ
        ∂ν.withDensity (M.variation.rnDeriv ν)) := by
    conv_lhs => rw [M.variation.haveLebesgueDecomposition_add ν,
      Measure.restrict_add, lintegral_add_measure]
  rw [hsplit, ENNReal.add_div]
  apply add_le_add le_rfl
  calc
    _ ≤ (2 * (ν.withDensity (M.variation.rnDeriv ν)) (closedBall x r)) /
        (M.variation.singularPart ν) (closedBall x r) :=
      ENNReal.div_le_div_right
        (lintegral_polar_sub_le_two_mul M _ (M.variation.withDensity_rnDeriv_le ν) hx _) _
    _ = _ := by rw [mul_div_assoc]

theorem ae_tendsto_polar_singular_closedBall_error
    [M.variation.HaveLebesgueDecomposition ν] :
    ∀ᵐ x ∂M.variation.singularPart ν, Tendsto
      (fun r => (∫ y in closedBall x r, ‖polarDensity M y - polarDensity M x‖
        ∂M.variation) / (M.variation.singularPart ν).real (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_polar_singular_closedBall_error_enorm M ν] with x hx
  have heq (r : ℝ) :
      (∫⁻ y in closedBall x r, ‖polarDensity M y - polarDensity M x‖ₑ ∂M.variation).toReal =
        ∫ y in closedBall x r, ‖polarDensity M y - polarDensity M x‖ ∂M.variation :=
    (integral_norm_eq_lintegral_enorm
      (((integrable_polarDensity M).sub (integrable_const _)).restrict.aestronglyMeasurable)).symm
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_zero, heq, Measure.real]
    using (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hx

theorem ae_tendsto_polar_singular_closedBall_div
    [M.variation.HaveLebesgueDecomposition ν] :
    ∀ᵐ x ∂M.variation.singularPart ν, Tendsto
      (fun r => ((M.variation.singularPart ν).real (closedBall x r))⁻¹ • M (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (polarDensity M x)) := by
  have hv := (Measure.absolutelyContinuous_of_le (M.variation.singularPart_le ν)).ae_le
    (ae_tendsto_polar_closedBall_div M)
  filter_upwards [hv, ae_tendsto_variation_singular_closedBall_ratio_real M ν,
    ae_eventually_closedBall_mass_pos (M.variation.singularPart ν)] with x hx hr hp
  have hlim := hr.smul hx
  simp only [one_smul] at hlim
  apply hlim.congr'
  filter_upwards [hp] with r hpos
  have hρ : M.variation.real (closedBall x r) ≠ 0 :=
    (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le hpos
      (M.variation.singularPart_le ν (closedBall x r)))) (measure_ne_top _ _)).ne'
  rw [smul_smul]
  congr 1
  rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hρ, one_mul]

theorem ae_tendsto_singularPart_closedBall_div :
    ∀ᵐ x ∂M.variation.singularPart ν, Tendsto
      (fun r => ((M.variation.singularPart ν).real (closedBall x r))⁻¹ •
        lebesgueSingularPart M ν (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (polarDensity M x)) :=
  ae_tendsto_withDensityᵥ_closedBall_div _ (integrable_polarDensity_lebesgueSingularMeasure M ν)

theorem ae_tendsto_polar_singular_closedBall_div_enorm
    [M.variation.HaveLebesgueDecomposition ν] :
    ∀ᵐ x ∂M.variation.singularPart ν, Tendsto
      (fun r => ‖((M.variation.singularPart ν).real (closedBall x r))⁻¹ •
        M (closedBall x r) - polarDensity M x‖ₑ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_polar_singular_closedBall_div M ν] with x hx
  simpa only [ofReal_norm, ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.mp hx)

theorem ae_tendsto_singularPart_closedBall_div_enorm :
    ∀ᵐ x ∂M.variation.singularPart ν, Tendsto
      (fun r => ‖((M.variation.singularPart ν).real (closedBall x r))⁻¹ •
        lebesgueSingularPart M ν (closedBall x r) - polarDensity M x‖ₑ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_singularPart_closedBall_div M ν] with x hx
  simpa only [ofReal_norm, ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.mp hx)

/-- One simultaneous statement for a countable, locally finite family.
The real limits are recorded on exactly the same full-measure set. -/
theorem ae_tendsto_countable_singular_closedBall_ratios
    {ι : Type*} [Countable ι] (β : ι → Measure (EuclideanSpace ℝ (Fin d)))
    [∀ k, IsLocallyFiniteMeasure (β k)] :
    ∀ᵐ x ∂M.variation.singularPart ν, ∀ k,
      (β k).rnDeriv (M.variation.singularPart ν) x < ∞ ∧
      Tendsto (fun r => β k (closedBall x r) / (M.variation.singularPart ν) (closedBall x r))
        (𝓝[>] (0 : ℝ)) (𝓝 ((β k).rnDeriv (M.variation.singularPart ν) x)) ∧
      Tendsto (fun r => (β k).real (closedBall x r) /
        (M.variation.singularPart ν).real (closedBall x r))
        (𝓝[>] (0 : ℝ)) (𝓝 (((β k).rnDeriv (M.variation.singularPart ν) x).toReal)) := by
  rw [ae_all_iff]
  intro k
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv (β k) (M.variation.singularPart ν),
    (β k).rnDeriv_lt_top (M.variation.singularPart ν)] with x hx hfin
  refine ⟨hfin, hx, ?_⟩
  simpa only [Function.comp_def, ENNReal.toReal_div, Measure.real] using
    (ENNReal.tendsto_toReal hfin.ne).comp hx

def singularBesicovitchPoints
    {ι : Type*} (β : ι → Measure (EuclideanSpace ℝ (Fin d))) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ‖polarDensity M x‖ = 1 ∧
    (∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < (M.variation.singularPart ν) (closedBall x r)) ∧
    Tendsto (fun r => (ν.withDensity (M.variation.rnDeriv ν)) (closedBall x r) /
      (M.variation.singularPart ν) (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun r => M.variation (closedBall x r) /
      (M.variation.singularPart ν) (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
    Tendsto (fun r => (∫⁻ y in closedBall x r, ‖polarDensity M y - polarDensity M x‖ₑ
      ∂M.variation) / (M.variation.singularPart ν) (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun r => ((M.variation.singularPart ν).real (closedBall x r))⁻¹ •
      M (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 (polarDensity M x)) ∧
    Tendsto (fun r => ((M.variation.singularPart ν).real (closedBall x r))⁻¹ •
      lebesgueSingularPart M ν (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 (polarDensity M x)) ∧
    (∀ k, (β k).rnDeriv (M.variation.singularPart ν) x < ∞ ∧
      Tendsto (fun r => β k (closedBall x r) / (M.variation.singularPart ν) (closedBall x r))
        (𝓝[>] (0 : ℝ)) (𝓝 ((β k).rnDeriv (M.variation.singularPart ν) x)) ∧
      Tendsto (fun r => (β k).real (closedBall x r) /
        (M.variation.singularPart ν).real (closedBall x r))
        (𝓝[>] (0 : ℝ)) (𝓝 (((β k).rnDeriv (M.variation.singularPart ν) x).toReal)))}

theorem ae_mem_singularBesicovitchPoints
    [M.variation.HaveLebesgueDecomposition ν]
    {ι : Type*} [Countable ι] (β : ι → Measure (EuclideanSpace ℝ (Fin d)))
    [∀ k, IsLocallyFiniteMeasure (β k)] :
    ∀ᵐ x ∂M.variation.singularPart ν, x ∈ singularBesicovitchPoints M ν β := by
  have hu := (Measure.absolutelyContinuous_of_le (M.variation.singularPart_le ν)).ae_le
    (norm_polarDensity_ae M)
  filter_upwards [hu, ae_eventually_closedBall_mass_pos (M.variation.singularPart ν),
    ae_tendsto_acPart_singular_closedBall_ratio M ν,
    ae_tendsto_variation_singular_closedBall_ratio M ν,
    ae_tendsto_polar_singular_closedBall_error_enorm M ν,
    ae_tendsto_polar_singular_closedBall_div M ν,
    ae_tendsto_singularPart_closedBall_div M ν,
    ae_tendsto_countable_singular_closedBall_ratios M ν β]
    with x hx hp ha hr he hv hs hb
  exact ⟨hx, hp, ha, hr, he, hv, hs, hb⟩

theorem exists_measurable_singularBesicovitchSet
    [M.variation.HaveLebesgueDecomposition ν]
    {ι : Type*} [Countable ι] (β : ι → Measure (EuclideanSpace ℝ (Fin d)))
    [∀ k, IsLocallyFiniteMeasure (β k)] :
    ∃ G : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet G ∧
      (M.variation.singularPart ν) Gᶜ = 0 ∧ G ⊆ singularBesicovitchPoints M ν β := by
  obtain ⟨N, hsub, hN, hz⟩ := exists_measurable_superset_of_null
    (ae_iff.mp (ae_mem_singularBesicovitchPoints M ν β))
  refine ⟨Nᶜ, hN.compl, by simpa using hz, ?_⟩
  intro x hx
  by_contra hbad
  exact hx (hsub hbad)

/-- With no singular mass the good-point predicate supplies no point. -/
theorem singularBesicovitchPoints_eq_empty_of_singularPart_eq_zero
    (hs : M.variation.singularPart ν = 0)
    {ι : Type*} (β : ι → Measure (EuclideanSpace ℝ (Fin d))) :
    singularBesicovitchPoints M ν β = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hp := hx.2.1
  obtain ⟨r, hr⟩ := hp.exists
  simp [hs] at hr

@[simp] theorem singularBesicovitchPoints_zero
    {ι : Type*} (β : ι → Measure (EuclideanSpace ℝ (Fin d))) :
    singularBesicovitchPoints
      (0 : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m))) ν β = ∅ :=
  singularBesicovitchPoints_eq_empty_of_singularPart_eq_zero 0 ν (by simp) β

theorem singularBesicovitchPoints_codomain_zero
    (M0 : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin 0)))
    {ι : Type*} (β : ι → Measure (EuclideanSpace ℝ (Fin d))) :
    singularBesicovitchPoints M0 ν β = ∅ := by
  rw [eq_zero_of_dimension_zero M0]
  exact singularBesicovitchPoints_zero ν β

/-! Differentiation relative to the reference measure. -/

theorem ae_tendsto_lebesgueACDensity_closedBall_div [IsLocallyFiniteMeasure ν] :
    ∀ᵐ x ∂ν, Tendsto
      (fun r => (ν.real (closedBall x r))⁻¹ • M (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (lebesgueACDensity M ν x)) := by
  have hac : ∀ᵐ x ∂ν, Tendsto
      (fun r => (ν.real (closedBall x r))⁻¹ • lebesgueACPart M ν (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (lebesgueACDensity M ν x)) := by
    simpa only [withDensityᵥ_lebesgueACDensity] using
      ae_tendsto_withDensityᵥ_closedBall_div ν (integrable_lebesgueACDensity M ν)
  filter_upwards [hac, Besicovitch.ae_tendsto_rnDeriv (M.variation.singularPart ν) ν,
    (M.variation.mutuallySingular_singularPart ν).rnDeriv_ae_eq_zero] with x ha hr hz
  have hr0 : Tendsto
      (fun r => (M.variation.singularPart ν) (closedBall x r) / ν (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa only [hz, Pi.zero_apply] using hr
  have hrR : Tendsto
      (fun r => (M.variation.singularPart ν).real (closedBall x r) / ν.real (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_zero, Measure.real]
      using (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hr0
  have hbound (r : ℝ) :
      ‖lebesgueSingularPart M ν (closedBall x r)‖ ≤
        (M.variation.singularPart ν).real (closedBall x r) := by
    have hb := (lebesgueSingularPart M ν).enorm_measure_le_variation (closedBall x r)
    rw [variation_lebesgueSingularPart] at hb
    simpa only [toReal_enorm, Measure.real] using
      ENNReal.toReal_mono (measure_ne_top (M.variation.singularPart ν) _) hb
  have hnorm : Tendsto
      (fun r => ‖(ν.real (closedBall x r))⁻¹ • lebesgueSingularPart M ν (closedBall x r)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (Eventually.of_forall (fun r => ?_)) hrR
    have hc : 0 ≤ (ν.real (closedBall x r))⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
    rw [norm_smul, Real.norm_of_nonneg hc]
    calc
      _ ≤ (ν.real (closedBall x r))⁻¹ * (M.variation.singularPart ν).real (closedBall x r) :=
        mul_le_mul_of_nonneg_left (hbound r) (inv_nonneg.mpr ENNReal.toReal_nonneg)
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  have hs0 : Tendsto
      (fun r => (ν.real (closedBall x r))⁻¹ • lebesgueSingularPart M ν (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : EuclideanSpace ℝ (Fin m))) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using hnorm)
  have hlim := ha.add hs0
  simp only [add_zero] at hlim
  apply hlim.congr'
  apply Eventually.of_forall
  intro r
  dsimp only
  rw [← smul_add]
  congr 1
  exact congrArg (fun V : VectorMeasure (EuclideanSpace ℝ (Fin d))
    (EuclideanSpace ℝ (Fin m)) => V (closedBall x r))
    (lebesgueACPart_add_lebesgueSingularPart M ν)

theorem ae_tendsto_lebesgueACDensity_closedBall_div_enorm [IsLocallyFiniteMeasure ν] :
    ∀ᵐ x ∂ν, Tendsto
      (fun r => ‖(ν.real (closedBall x r))⁻¹ • M (closedBall x r) -
        lebesgueACDensity M ν x‖ₑ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_lebesgueACDensity_closedBall_div M ν] with x hx
  simpa only [ofReal_norm, ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.mp hx)

/-! Frobenius-valued measures and simultaneous row limits. -/

variable {n : ℕ}
variable (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace n))

theorem ae_tendsto_matrixPolar_closedBall_error_enorm :
    ∀ᵐ x ∂N.variation, Tendsto
      (fun r => (∫⁻ y in closedBall x r, ‖matrixPolarDensity N y - matrixPolarDensity N x‖ₑ
        ∂N.variation) / N.variation (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  ae_tendsto_closedBall_lintegral_enorm_sub_div _ (integrable_matrixPolarDensity N)

theorem ae_tendsto_matrixPolar_closedBall_error :
    ∀ᵐ x ∂N.variation, Tendsto
      (fun r => (∫ y in closedBall x r, ‖matrixPolarDensity N y - matrixPolarDensity N x‖
        ∂N.variation) / N.variation.real (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  ae_tendsto_closedBall_integral_norm_sub_div _ (integrable_matrixPolarDensity N)

theorem ae_tendsto_matrixPolar_closedBall_div :
    ∀ᵐ x ∂N.variation, Tendsto
      (fun r => (N.variation.real (closedBall x r))⁻¹ • N (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (matrixPolarDensity N x)) := by
  simpa only [withDensityᵥ_matrixPolarDensity] using
    ae_tendsto_withDensityᵥ_closedBall_div _ (integrable_matrixPolarDensity N)

theorem ae_tendsto_matrixPolar_closedBall_div_enorm :
    ∀ᵐ x ∂N.variation, Tendsto
      (fun r => ‖(N.variation.real (closedBall x r))⁻¹ • N (closedBall x r) -
        matrixPolarDensity N x‖ₑ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_matrixPolar_closedBall_div N] with x hx
  simpa only [ofReal_norm, ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.mp hx)

theorem ae_tendsto_rowMeasure_matrixVariation_closedBall_div (i : Fin n) :
    ∀ᵐ x ∂N.variation, Tendsto
      (fun r => (N.variation.real (closedBall x r))⁻¹ • rowMeasure N i (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (rowCLM i (matrixPolarDensity N x))) := by
  filter_upwards [ae_tendsto_matrixPolar_closedBall_div N] with x hx
  simpa only [Function.comp_def, map_smul, rowMeasure_apply] using
    ((rowCLM i).continuous.tendsto (matrixPolarDensity N x)).comp hx

theorem ae_tendsto_rowMeasure_matrixVariation_closedBall_div_enorm (i : Fin n) :
    ∀ᵐ x ∂N.variation, Tendsto
      (fun r => ‖(N.variation.real (closedBall x r))⁻¹ • rowMeasure N i (closedBall x r) -
        rowCLM i (matrixPolarDensity N x)‖ₑ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_rowMeasure_matrixVariation_closedBall_div N i] with x hx
  simpa only [ofReal_norm, ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.mp hx)

theorem ae_tendsto_all_rows_matrixVariation_closedBall_div :
    ∀ᵐ x ∂N.variation, ∀ i : Fin n, Tendsto
      (fun r => (N.variation.real (closedBall x r))⁻¹ • rowMeasure N i (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (rowCLM i (matrixPolarDensity N x))) :=
  ae_all_iff.mpr (ae_tendsto_rowMeasure_matrixVariation_closedBall_div N)

end GeometricMeasure
