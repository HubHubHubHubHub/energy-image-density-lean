import ErrorCalculus.Dirichlet.ProductDensityEnergy

noncomputable section
open MeasureTheory Filter
namespace ErrorCalculus
variable {d₁ d₂ : ℕ}
variable (ρ₁ : (Fin d₁ → ℝ) → ℝ) (ρ₂ : (Fin d₂ → ℝ) → ℝ)
    [SmoothDensityD ρ₁] [SmoothDensityD ρ₂]
    [IsProbabilityMeasure (densityMeasureD ρ₁)] [IsProbabilityMeasure (densityMeasureD ρ₂)]
variable {g₁ h₁ : (Fin d₁ → ℝ) → ℝ} {g₂ h₂ : (Fin d₂ → ℝ) → ℝ}

/-- The elementary tensor belongs to the actual closed density domain. -/
def densityTensor (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂) :
    (densityStructureD (prodDensity ρ₁ ρ₂)).dom :=
  (protoFormD (prodDensity ρ₁ ρ₂)).inclusion
    (protoOfFunctionD _ (tensorFun g₁ g₂) (hg₁.tensor hg₂))

/-- The closed carré du champ has exactly B19's mixed tensor formula. -/
theorem densityStructureD_Γ_tensor (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂)
    (hh₁ : IsC1BoundedD h₁) (hh₂ : IsC1BoundedD h₂) :
    ⇑((densityStructureD (prodDensity ρ₁ ρ₂)).Γ
      (densityTensor ρ₁ ρ₂ hg₁ hg₂) (densityTensor ρ₁ ρ₂ hh₁ hh₂))
      =ᵐ[densityMeasureD (prodDensity ρ₁ ρ₂)] fun z =>
      pointGammaD g₁ h₁ (prodProj₁ d₁ d₂ z) * (g₂ (prodProj₂ d₁ d₂ z) * h₂ (prodProj₂ d₁ d₂ z)) +
      (g₁ (prodProj₁ d₁ d₂ z) * h₁ (prodProj₁ d₁ d₂ z)) * pointGammaD g₂ h₂ (prodProj₂ d₁ d₂ z) := by
  unfold densityTensor
  rw [densityStructure_Γ_extendsD]
  exact gammaD_tensor ρ₁ ρ₂ hg₁ hg₂ hh₁ hh₂

theorem densityStructureD_Γ_tensor_diag (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂) :
    ⇑((densityStructureD (prodDensity ρ₁ ρ₂)).Γ
      (densityTensor ρ₁ ρ₂ hg₁ hg₂) (densityTensor ρ₁ ρ₂ hg₁ hg₂))
      =ᵐ[densityMeasureD (prodDensity ρ₁ ρ₂)] fun z =>
      pointGammaD g₁ g₁ (prodProj₁ d₁ d₂ z) * g₂ (prodProj₂ d₁ d₂ z)^2 +
      g₁ (prodProj₁ d₁ d₂ z)^2 * pointGammaD g₂ g₂ (prodProj₂ d₁ d₂ z) := by
  simpa only [pow_two] using densityStructureD_Γ_tensor ρ₁ ρ₂ hg₁ hg₂ hg₁ hg₂

/-- The first factor embeds by tensoring with the constant one. -/
theorem densityStructureD_Γ_tensor_one (hg₁ : IsC1BoundedD g₁) (hh₁ : IsC1BoundedD h₁) :
    ⇑((densityStructureD (prodDensity ρ₁ ρ₂)).Γ
      (densityTensor ρ₁ ρ₂ hg₁ (IsC1BoundedD.const 1))
      (densityTensor ρ₁ ρ₂ hh₁ (IsC1BoundedD.const 1)))
      =ᵐ[densityMeasureD (prodDensity ρ₁ ρ₂)] fun z => pointGammaD g₁ h₁ (prodProj₁ d₁ d₂ z) := by
  unfold densityTensor
  rw [densityStructure_Γ_extendsD]
  exact gammaD_tensor_one ρ₁ ρ₂ hg₁ hh₁

/-- P.4 in terms of the closed carré du champ of each factor. -/
theorem densityStructureD_Γ_tensor_classes (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂)
    (hh₁ : IsC1BoundedD h₁) (hh₂ : IsC1BoundedD h₂) :
    ⇑((densityStructureD (prodDensity ρ₁ ρ₂)).Γ
      (densityTensor ρ₁ ρ₂ hg₁ hg₂) (densityTensor ρ₁ ρ₂ hh₁ hh₂))
      =ᵐ[densityMeasureD (prodDensity ρ₁ ρ₂)] fun z =>
      (densityStructureD ρ₁).Γ ((protoFormD ρ₁).inclusion (protoOfFunctionD _ g₁ hg₁))
        ((protoFormD ρ₁).inclusion (protoOfFunctionD _ h₁ hh₁)) (prodProj₁ d₁ d₂ z) *
        (g₂ (prodProj₂ d₁ d₂ z) * h₂ (prodProj₂ d₁ d₂ z)) +
      (g₁ (prodProj₁ d₁ d₂ z) * h₁ (prodProj₁ d₁ d₂ z)) *
      (densityStructureD ρ₂).Γ ((protoFormD ρ₂).inclusion (protoOfFunctionD _ g₂ hg₂))
        ((protoFormD ρ₂).inclusion (protoOfFunctionD _ h₂ hh₂)) (prodProj₂ d₁ d₂ z) := by
  unfold densityTensor
  simp only [densityStructure_Γ_extendsD]
  exact gammaD_tensor_classes ρ₁ ρ₂ hg₁ hg₂ hh₁ hh₂

/-- The mixed tensor energy in the closed structures. -/
theorem densityStructureD_energy_tensor (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂)
    (hh₁ : IsC1BoundedD h₁) (hh₂ : IsC1BoundedD h₂) :
    (densityStructureD (prodDensity ρ₁ ρ₂)).energy.E
      (densityTensor ρ₁ ρ₂ hg₁ hg₂) (densityTensor ρ₁ ρ₂ hh₁ hh₂) =
      (densityStructureD ρ₁).energy.E ((protoFormD ρ₁).inclusion (protoOfFunctionD _ g₁ hg₁))
        ((protoFormD ρ₁).inclusion (protoOfFunctionD _ h₁ hh₁)) *
        (∫ y, g₂ y * h₂ y ∂densityMeasureD ρ₂) +
      (∫ x, g₁ x * h₁ x ∂densityMeasureD ρ₁) *
      (densityStructureD ρ₂).energy.E ((protoFormD ρ₂).inclusion (protoOfFunctionD _ g₂ hg₂))
        ((protoFormD ρ₂).inclusion (protoOfFunctionD _ h₂ hh₂)) := by
  simp only [densityTensor, densityStructureD_energy_ofProto]
  exact protoForm_tensor ρ₁ ρ₂ hg₁ hg₂ hh₁ hh₂

/-- The diagonal is E₁[g₁]‖g₂‖² + ‖g₁‖²E₂[g₂]. -/
theorem densityStructureD_energy_tensor_diag (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂) :
    (densityStructureD (prodDensity ρ₁ ρ₂)).energy.E
      (densityTensor ρ₁ ρ₂ hg₁ hg₂) (densityTensor ρ₁ ρ₂ hg₁ hg₂) =
      (densityStructureD ρ₁).energy.E ((protoFormD ρ₁).inclusion (protoOfFunctionD _ g₁ hg₁))
        ((protoFormD ρ₁).inclusion (protoOfFunctionD _ g₁ hg₁)) *
        ‖(protoOfFunctionD ρ₂ g₂ hg₂ : Lp ℝ 2 (densityMeasureD ρ₂))‖ ^ 2 +
      ‖(protoOfFunctionD ρ₁ g₁ hg₁ : Lp ℝ 2 (densityMeasureD ρ₁))‖ ^ 2 *
      (densityStructureD ρ₂).energy.E ((protoFormD ρ₂).inclusion (protoOfFunctionD _ g₂ hg₂))
        ((protoFormD ρ₂).inclusion (protoOfFunctionD _ g₂ hg₂)) := by
  simp only [densityTensor, densityStructureD_energy_ofProto]
  exact protoForm_tensor_diag ρ₁ ρ₂ hg₁ hg₂

/-- Energy of the first factor is preserved inside the closed product structure. -/
theorem densityStructureD_energy_tensor_one (hg₁ : IsC1BoundedD g₁) (hh₁ : IsC1BoundedD h₁) :
    (densityStructureD (prodDensity ρ₁ ρ₂)).energy.E
      (densityTensor ρ₁ ρ₂ hg₁ (IsC1BoundedD.const 1))
      (densityTensor ρ₁ ρ₂ hh₁ (IsC1BoundedD.const 1)) =
      (densityStructureD ρ₁).energy.E ((protoFormD ρ₁).inclusion (protoOfFunctionD _ g₁ hg₁))
        ((protoFormD ρ₁).inclusion (protoOfFunctionD _ h₁ hh₁)) := by
  simp only [densityTensor, densityStructureD_energy_ofProto]
  exact protoForm_tensor_one ρ₁ ρ₂ hg₁ hh₁

end ErrorCalculus
