import ErrorCalculus.Dirichlet.ProductDensityGamma

noncomputable section
open MeasureTheory Filter
namespace ErrorCalculus
variable {d d₁ d₂ : ℕ}

/-- Integrability of the canonical mixed carré du champ. -/
theorem integrable_pointGammaD (ρ : (Fin d → ℝ) → ℝ) [SmoothDensityD ρ]
    [IsProbabilityMeasure (densityMeasureD ρ)] {g h : (Fin d → ℝ) → ℝ}
    (hg : IsC1BoundedD g) (hh : IsC1BoundedD h) : Integrable (pointGammaD g h) (densityMeasureD ρ) :=
  (L1.integrable_coeFn (gammaD ρ (protoOfFunctionD _ g hg) (protoOfFunctionD _ h hh))).congr
    (gammaD_ofFunction ρ hg hh)

/-- Energy on C¹_b computed with the canonical derivative representative. -/
theorem protoFormD_ofFunction (ρ : (Fin d → ℝ) → ℝ) [SmoothDensityD ρ]
    [IsProbabilityMeasure (densityMeasureD ρ)] {g h : (Fin d → ℝ) → ℝ}
    (hg : IsC1BoundedD g) (hh : IsC1BoundedD h) :
    (protoFormD ρ).E (protoOfFunctionD _ g hg) (protoOfFunctionD _ h hh) =
      (1/2 : ℝ) * ∫ x, pointGammaD g h x ∂densityMeasureD ρ := by
  change (1/2 : ℝ) * (∫ x, gammaD ρ _ _ x ∂densityMeasureD ρ) = _
  rw [integral_congr_ae (gammaD_ofFunction ρ hg hh)]

/-- Squared L² norm of the actual class of a bounded C¹ function. -/
theorem protoOfFunctionD_norm_sq (ρ : (Fin d → ℝ) → ℝ)
    [IsProbabilityMeasure (densityMeasureD ρ)] {g : (Fin d → ℝ) → ℝ} (hg : IsC1BoundedD g) :
    (∫ x, g x ^ 2 ∂densityMeasureD ρ) = ‖(protoOfFunctionD ρ g hg : Lp ℝ 2 (densityMeasureD ρ))‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hg.memLp (densityMeasureD ρ) 2).coeFn_toLp] with x hx
  change g x ^ 2 = inner ℝ ((hg.memLp (densityMeasureD ρ) 2).toLp g x)
    ((hg.memLp (densityMeasureD ρ) 2).toLp g x)
  rw [hx]
  simp

/-- Closing the form preserves its energy on the original domain. -/
theorem densityStructureD_energy_ofProto (ρ : (Fin d → ℝ) → ℝ) [SmoothDensityD ρ]
    [IsProbabilityMeasure (densityMeasureD ρ)] (u v : protoDomD ρ) :
    (densityStructureD ρ).energy.E ((protoFormD ρ).inclusion u) ((protoFormD ρ).inclusion v) =
      (protoFormD ρ).E u v := by
  change (1/2 : ℝ) * (∫ x, (densityStructureD ρ).Γ _ _ x ∂densityMeasureD ρ) =
    (1/2 : ℝ) * (∫ x, gammaD ρ u v x ∂densityMeasureD ρ)
  rw [densityStructure_Γ_extendsD]

variable (ρ₁ : (Fin d₁ → ℝ) → ℝ) (ρ₂ : (Fin d₂ → ℝ) → ℝ)
    [SmoothDensityD ρ₁] [SmoothDensityD ρ₂]
    [IsProbabilityMeasure (densityMeasureD ρ₁)] [IsProbabilityMeasure (densityMeasureD ρ₂)]
variable {g₁ h₁ : (Fin d₁ → ℝ) → ℝ} {g₂ h₂ : (Fin d₂ → ℝ) → ℝ}

omit [IsProbabilityMeasure (densityMeasureD ρ₁)] [IsProbabilityMeasure (densityMeasureD ρ₂)] in
/-- Integrability is transported from the ordinary product space. -/
theorem integrable_tensorFun {f₁ : (Fin d₁ → ℝ) → ℝ} {f₂ : (Fin d₂ → ℝ) → ℝ}
    (h₁ : Integrable f₁ (densityMeasureD ρ₁)) (h₂ : Integrable f₂ (densityMeasureD ρ₂)) :
    Integrable (tensorFun f₁ f₂) (densityMeasureD (prodDensity ρ₁ ρ₂)) := by
  apply ((appendEquivM_density_preserving ρ₁ ρ₂).integrable_comp_emb
    (appendEquivM d₁ d₂).measurableEmbedding).mp
  convert h₁.mul_prod h₂ using 1
  ext z
  exact tensorFun_append f₁ f₂ z.1 z.2

/-- The mixed energy formula of B19, by transported Fubini. -/
theorem protoForm_tensor (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂)
    (hh₁ : IsC1BoundedD h₁) (hh₂ : IsC1BoundedD h₂) :
    (protoFormD (prodDensity ρ₁ ρ₂)).E
      (protoOfFunctionD _ (tensorFun g₁ g₂) (hg₁.tensor hg₂))
      (protoOfFunctionD _ (tensorFun h₁ h₂) (hh₁.tensor hh₂)) =
      (protoFormD ρ₁).E (protoOfFunctionD _ g₁ hg₁) (protoOfFunctionD _ h₁ hh₁) *
        (∫ y, g₂ y * h₂ y ∂densityMeasureD ρ₂) +
      (∫ x, g₁ x * h₁ x ∂densityMeasureD ρ₁) *
        (protoFormD ρ₂).E (protoOfFunctionD _ g₂ hg₂) (protoOfFunctionD _ h₂ hh₂) := by
  have hi₁ := integrable_tensorFun ρ₁ ρ₂ (integrable_pointGammaD ρ₁ hg₁ hh₁)
    ((hg₂.memLp (densityMeasureD ρ₂) 2).integrable_mul (hh₂.memLp (densityMeasureD ρ₂) 2))
  have hi₂ := integrable_tensorFun ρ₁ ρ₂
    ((hg₁.memLp (densityMeasureD ρ₁) 2).integrable_mul (hh₁.memLp (densityMeasureD ρ₁) 2))
    (integrable_pointGammaD ρ₂ hg₂ hh₂)
  rw [protoFormD_ofFunction, protoFormD_ofFunction, protoFormD_ofFunction]
  have hp : pointGammaD (tensorFun g₁ g₂) (tensorFun h₁ h₂) =
      fun z => tensorFun (pointGammaD g₁ h₁) (g₂ * h₂) z +
        tensorFun (g₁ * h₁) (pointGammaD g₂ h₂) z := by
    funext z
    exact pointGammaD_tensor hg₁.differentiable hg₂.differentiable hh₁.differentiable hh₂.differentiable z
  rw [hp, integral_add hi₁ hi₂, integral_tensorFun, integral_tensorFun]
  simp only [Pi.mul_apply]
  ring

/-- Diagonal energy, with the norms of the actual L² classes. -/
theorem protoForm_tensor_diag (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂) :
    (protoFormD (prodDensity ρ₁ ρ₂)).E
      (protoOfFunctionD _ (tensorFun g₁ g₂) (hg₁.tensor hg₂))
      (protoOfFunctionD _ (tensorFun g₁ g₂) (hg₁.tensor hg₂)) =
      (protoFormD ρ₁).E (protoOfFunctionD _ g₁ hg₁) (protoOfFunctionD _ g₁ hg₁) *
        ‖(protoOfFunctionD ρ₂ g₂ hg₂ : Lp ℝ 2 (densityMeasureD ρ₂))‖ ^ 2 +
      ‖(protoOfFunctionD ρ₁ g₁ hg₁ : Lp ℝ 2 (densityMeasureD ρ₁))‖ ^ 2 *
        (protoFormD ρ₂).E (protoOfFunctionD _ g₂ hg₂) (protoOfFunctionD _ g₂ hg₂) := by
  rw [protoForm_tensor ρ₁ ρ₂ hg₁ hg₂ hg₁ hg₂]
  simp only [← pow_two, protoOfFunctionD_norm_sq ρ₁ hg₁, protoOfFunctionD_norm_sq ρ₂ hg₂]

/-- Tensoring with one preserves the mixed energy of the first factor. -/
theorem protoForm_tensor_one (hg₁ : IsC1BoundedD g₁) (hh₁ : IsC1BoundedD h₁) :
    (protoFormD (prodDensity ρ₁ ρ₂)).E
      (protoOfFunctionD _ (tensorFun g₁ (fun _ => 1)) (hg₁.tensor (IsC1BoundedD.const 1)))
      (protoOfFunctionD _ (tensorFun h₁ (fun _ => 1)) (hh₁.tensor (IsC1BoundedD.const 1))) =
      (protoFormD ρ₁).E (protoOfFunctionD _ g₁ hg₁) (protoOfFunctionD _ h₁ hh₁) := by
  rw [protoForm_tensor ρ₁ ρ₂ hg₁ (IsC1BoundedD.const 1) hh₁ (IsC1BoundedD.const 1)]
  simp [protoFormD_ofFunction, pointGammaD]

/-- Tensor norms factor, and hence tensoring with one is an L² isometry. -/
theorem protoOfFunctionD_tensor_norm_sq (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂) :
    ‖(protoOfFunctionD (prodDensity ρ₁ ρ₂) (tensorFun g₁ g₂) (hg₁.tensor hg₂) :
      Lp ℝ 2 (densityMeasureD (prodDensity ρ₁ ρ₂)))‖ ^ 2 =
      ‖(protoOfFunctionD ρ₁ g₁ hg₁ : Lp ℝ 2 (densityMeasureD ρ₁))‖ ^ 2 *
      ‖(protoOfFunctionD ρ₂ g₂ hg₂ : Lp ℝ 2 (densityMeasureD ρ₂))‖ ^ 2 := by
  rw [← protoOfFunctionD_norm_sq, ← protoOfFunctionD_norm_sq, ← protoOfFunctionD_norm_sq]
  have h : (fun z => tensorFun g₁ g₂ z ^ 2) = tensorFun (fun x => g₁ x ^ 2) (fun y => g₂ y ^ 2) := by
    funext z; exact mul_pow _ _ _
  rw [h, integral_tensorFun]

end ErrorCalculus
