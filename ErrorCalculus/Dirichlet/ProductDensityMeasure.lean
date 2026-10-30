import ErrorCalculus.Dirichlet.ProductDensityBasic
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal
namespace ErrorCalculus
variable {d₁ d₂ : ℕ}

/-- Transport of a density through a measure-preserving measurable equivalence. -/
theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (f : β → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (f ∘ e)).map e = ν.withDensity f := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map_equiv]
  calc
    _ = ∫⁻ a, ((f ∘ e) * (g ∘ e)) a ∂μ :=
      lintegral_withDensity_eq_lintegral_mul μ (hf.comp e.measurable) (hg.comp e.measurable)
    _ = ∫⁻ b, (f * g) b ∂ν := he.lintegral_comp (hf.mul hg)
    _ = _ := (lintegral_withDensity_eq_lintegral_mul ν hf hg).symm

variable (ρ₁ : (Fin d₁ → ℝ) → ℝ) (ρ₂ : (Fin d₂ → ℝ) → ℝ)
    [SmoothDensityD ρ₁] [SmoothDensityD ρ₂]

/-- The density product is precisely the transported product measure. -/
theorem densityMeasureD_prod : densityMeasureD (prodDensity ρ₁ ρ₂) =
    ((densityMeasureD ρ₁).prod (densityMeasureD ρ₂)).map (appendEquivM d₁ d₂) := by
  have h₁ := (SmoothDensityD.contDiff (ρ := ρ₁)).continuous.measurable.ennreal_ofReal
  have h₂ := (SmoothDensityD.contDiff (ρ := ρ₂)).continuous.measurable.ennreal_ofReal
  unfold densityMeasureD
  rw [prod_withDensity h₁ h₂]
  have hf : (fun z : (Fin d₁ → ℝ) × (Fin d₂ → ℝ) =>
      ENNReal.ofReal (ρ₁ z.1) * ENNReal.ofReal (ρ₂ z.2)) =
      (fun z => ENNReal.ofReal (prodDensity ρ₁ ρ₂ z)) ∘ appendEquivM d₁ d₂ := by
    funext z
    rcases z with ⟨x, y⟩
    simp [prodDensity, ENNReal.ofReal_mul (SmoothDensityD.pos (ρ := ρ₁) x).le]
  rw [hf, map_withDensity_equiv _ (appendEquivM_volume_preserving d₁ d₂) _
    (SmoothDensityD.contDiff (ρ := prodDensity ρ₁ ρ₂)).continuous.measurable.ennreal_ofReal]

/-- The concatenation also preserves the probability density measures. -/
theorem appendEquivM_density_preserving : MeasurePreserving (appendEquivM d₁ d₂)
    ((densityMeasureD ρ₁).prod (densityMeasureD ρ₂)) (densityMeasureD (prodDensity ρ₁ ρ₂)) :=
  ⟨(appendEquivM d₁ d₂).measurable, (densityMeasureD_prod ρ₁ ρ₂).symm⟩

instance prodDensity_probability [IsProbabilityMeasure (densityMeasureD ρ₁)]
    [IsProbabilityMeasure (densityMeasureD ρ₂)] :
    IsProbabilityMeasure (densityMeasureD (prodDensity ρ₁ ρ₂)) := by
  rw [densityMeasureD_prod]
  exact isProbabilityMeasure_map (appendEquivM d₁ d₂).measurable.aemeasurable

/-- Fubini after concatenation. -/
theorem integral_prodDensity (f : (Fin (d₁ + d₂) → ℝ) → ℝ)
    (hf : Integrable f (densityMeasureD (prodDensity ρ₁ ρ₂))) :
    (∫ z, f z ∂densityMeasureD (prodDensity ρ₁ ρ₂)) =
      ∫ x, ∫ y, f (appendEquivM d₁ d₂ (x,y)) ∂densityMeasureD ρ₂ ∂densityMeasureD ρ₁ := by
  haveI : SigmaFinite (densityMeasureD ρ₁) := by unfold densityMeasureD; infer_instance
  haveI : SigmaFinite (densityMeasureD ρ₂) := by unfold densityMeasureD; infer_instance
  rw [← (appendEquivM_density_preserving ρ₁ ρ₂).integral_comp']
  exact integral_prod _ (((appendEquivM_density_preserving ρ₁ ρ₂).integrable_comp_emb
    (appendEquivM d₁ d₂).measurableEmbedding).mpr hf)

/-- A separable integral factors, with no extra integrability hypothesis needed. -/
theorem integral_tensorFun (g₁ : (Fin d₁ → ℝ) → ℝ) (g₂ : (Fin d₂ → ℝ) → ℝ) :
    (∫ z, tensorFun g₁ g₂ z ∂densityMeasureD (prodDensity ρ₁ ρ₂)) =
      (∫ x, g₁ x ∂densityMeasureD ρ₁) * ∫ y, g₂ y ∂densityMeasureD ρ₂ := by
  haveI : SigmaFinite (densityMeasureD ρ₁) := by unfold densityMeasureD; infer_instance
  haveI : SigmaFinite (densityMeasureD ρ₂) := by unfold densityMeasureD; infer_instance
  rw [← (appendEquivM_density_preserving ρ₁ ρ₂).integral_comp']
  simp only [show ∀ z, tensorFun g₁ g₂ (appendEquivM d₁ d₂ z) = g₁ z.1 * g₂ z.2 from
    fun z => tensorFun_append g₁ g₂ z.1 z.2]
  exact integral_prod_mul _ _

/-- The inverse concatenation is the pair of coordinate projections. -/
@[simp] theorem appendEquivM_symm_apply (z : Fin (d₁ + d₂) → ℝ) :
    (appendEquivM d₁ d₂).symm z = (prodProj₁ d₁ d₂ z, prodProj₂ d₁ d₂ z) := by
  apply (appendEquivM d₁ d₂).injective
  simp only [MeasurableEquiv.apply_symm_apply, appendEquivM_apply]
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- Marginal of the first block under the product density. -/
theorem prodProj₁_density_preserving [IsProbabilityMeasure (densityMeasureD ρ₁)]
    [IsProbabilityMeasure (densityMeasureD ρ₂)] :
    MeasurePreserving (prodProj₁ d₁ d₂) (densityMeasureD (prodDensity ρ₁ ρ₂)) (densityMeasureD ρ₁) := by
  have h := (measurePreserving_fst (μ := densityMeasureD ρ₁) (ν := densityMeasureD ρ₂)).comp
    (appendEquivM_density_preserving ρ₁ ρ₂).symm
  simpa only [Function.comp_def, appendEquivM_symm_apply] using h

/-- Marginal of the second block under the product density. -/
theorem prodProj₂_density_preserving [IsProbabilityMeasure (densityMeasureD ρ₁)]
    [IsProbabilityMeasure (densityMeasureD ρ₂)] :
    MeasurePreserving (prodProj₂ d₁ d₂) (densityMeasureD (prodDensity ρ₁ ρ₂)) (densityMeasureD ρ₂) := by
  have h := (measurePreserving_snd (μ := densityMeasureD ρ₁) (ν := densityMeasureD ρ₂)).comp
    (appendEquivM_density_preserving ρ₁ ρ₂).symm
  simpa only [Function.comp_def, appendEquivM_symm_apply] using h

end ErrorCalculus
