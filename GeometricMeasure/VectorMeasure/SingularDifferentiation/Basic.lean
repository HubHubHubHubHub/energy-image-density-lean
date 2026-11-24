import GeometricMeasure.VectorMeasure.Differentiation
import GeometricMeasure.VectorMeasure.Matrix.Basic

/-!
# Differentiation with respect to the singular part

This file contains the definitions and results of the development of
`GeometricMeasure.VectorMeasure.SingularDifferentiation` that the main statements of the library
(the head theorems listed in the README of the repository) use, together with the basic API of their
definitions. `GeometricMeasure.VectorMeasure.SingularDifferentiation` imports it and continues the
development.

## Main definitions

* `singularBesicovitchPoints`: The points at which the singular blow-up conditions relative to `ν`
  hold together: unit polar density, positive singular mass on small closed balls, vanishing
  relative mass of the absolutely continuous part, relative total variation tending to `1`, Lebesgue
  point of the polar density, convergence of the normalized averages of `M` and of its singular part
  to the polar density, and finite Besicovitch derivatives of every `β k`.

## Main statements

* `ae_mem_singularBesicovitchPoints`: Under a Lebesgue decomposition of `M.variation` by `ν`, for a
  countable family `β` of locally finite measures, a.e. point of the singular part lies in
  `singularBesicovitchPoints M ν β`.
* `singularBesicovitchPoints_codomain_zero`: For a vector measure `M0` with values in
  `EuclideanSpace ℝ (Fin 0)`, the set `singularBesicovitchPoints M0 ν β` is empty.
-/
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

/-- The points at which the singular blow-up conditions relative to `ν` hold together: unit polar
density, positive singular mass on small closed balls, vanishing relative mass of the absolutely
continuous part, relative total variation tending to `1`, Lebesgue point of the polar density,
convergence of the normalized averages of `M` and of its singular part to the polar density, and
finite Besicovitch derivatives of every `β k`. -/
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

end GeometricMeasure
