import GeometricMeasure.VectorMeasure.Lebesgue
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-! Closed-ball differentiation on finite-dimensional Euclidean spaces.
Scalar errors use ENNReal; vector averages use the real mass of the ball. -/

noncomputable section
open MeasureTheory Filter Metric
open scoped ENNReal Topology

namespace GeometricMeasure

variable {d m : ℕ}

theorem ae_eventually_closedBall_mass_pos
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [SFinite μ] :
    ∀ᵐ x ∂μ, ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < μ (closedBall x r) := by
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_eventually_measure_pos] with x hx
  exact (Besicovitch.tendsto_filterAt μ x).eventually hx

theorem ae_tendsto_closedBall_lintegral_enorm_sub_div
    {F : Type*} [NormedAddCommGroup F]
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsLocallyFiniteMeasure μ]
    {f : EuclideanSpace ℝ (Fin d) → F} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto
      (fun r => (∫⁻ y in closedBall x r, ‖f y - f x‖ₑ ∂μ) / μ (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [VitaliFamily.ae_tendsto_lintegral_enorm_sub_div_of_integrable
    (Besicovitch.vitaliFamily μ) hf] with x hx
  exact hx.comp (Besicovitch.tendsto_filterAt μ x)

theorem ae_tendsto_closedBall_integral_norm_sub_div
    {F : Type*} [NormedAddCommGroup F]
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    {f : EuclideanSpace ℝ (Fin d) → F} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto
      (fun r => (∫ y in closedBall x r, ‖f y - f x‖ ∂μ) / μ.real (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_closedBall_lintegral_enorm_sub_div μ hf] with x hx
  have h := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hx
  have heq (r : ℝ) :
      (∫⁻ y in closedBall x r, ‖f y - f x‖ₑ ∂μ).toReal =
        ∫ y in closedBall x r, ‖f y - f x‖ ∂μ :=
    (integral_norm_eq_lintegral_enorm
      ((hf.sub (integrable_const (f x))).restrict.aestronglyMeasurable)).symm
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_zero,
    heq, Measure.real] using h

theorem ae_tendsto_withDensityᵥ_closedBall_div
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsLocallyFiniteMeasure μ]
    {f : EuclideanSpace ℝ (Fin d) → F} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto
      (fun r => (μ.real (closedBall x r))⁻¹ • μ.withDensityᵥ f (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_average hf.locallyIntegrable]
    with x hx
  simpa only [Function.comp_def, setAverage_eq,
    withDensityᵥ_apply hf isClosed_closedBall.measurableSet] using
    hx.comp (Besicovitch.tendsto_filterAt μ x)

theorem ae_tendsto_polar_closedBall_error_enorm
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m))) :
    ∀ᵐ x ∂M.variation, Tendsto
      (fun r => (∫⁻ y in closedBall x r, ‖polarDensity M y - polarDensity M x‖ₑ
        ∂M.variation) / M.variation (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  ae_tendsto_closedBall_lintegral_enorm_sub_div _ (integrable_polarDensity M)

theorem ae_tendsto_polar_closedBall_error
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m))) :
    ∀ᵐ x ∂M.variation, Tendsto
      (fun r => (∫ y in closedBall x r, ‖polarDensity M y - polarDensity M x‖
        ∂M.variation) / M.variation.real (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  ae_tendsto_closedBall_integral_norm_sub_div _ (integrable_polarDensity M)

/-- The centering identity underlying the vector quotient. -/
theorem integral_polarDensity_sub_const
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (c : EuclideanSpace ℝ (Fin m)) {A : Set (EuclideanSpace ℝ (Fin d))}
    (hA : MeasurableSet A) :
    (∫ y in A, polarDensity M y - c ∂M.variation) = M A - M.variation.real A • c := by
  rw [integral_sub (integrable_polarDensity M).restrict (integrable_const c),
    setIntegral_const]
  rw [← withDensityᵥ_apply (integrable_polarDensity M) hA, withDensityᵥ_polarDensity]

theorem ae_tendsto_polar_closedBall_div
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m))) :
    ∀ᵐ x ∂M.variation, Tendsto
      (fun r => (M.variation.real (closedBall x r))⁻¹ • M (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (polarDensity M x)) := by
  simpa only [withDensityᵥ_polarDensity] using
    ae_tendsto_withDensityᵥ_closedBall_div _ (integrable_polarDensity M)

theorem ae_tendsto_polar_closedBall_div_enorm
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m))) :
    ∀ᵐ x ∂M.variation, Tendsto
      (fun r => ‖(M.variation.real (closedBall x r))⁻¹ • M (closedBall x r) -
        polarDensity M x‖ₑ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_polar_closedBall_div M] with x hx
  simpa only [ofReal_norm, ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.mp hx)

end GeometricMeasure
