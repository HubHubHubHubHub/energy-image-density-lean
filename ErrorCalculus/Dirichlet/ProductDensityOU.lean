import ErrorCalculus.Dirichlet.ProductDensityStructure
import ErrorCalculus.Dirichlet.OrnsteinUhlenbeckDMeasure

noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace ErrorCalculus
variable {d₁ d₂ : ℕ}

/-- The Gaussian density factors across the two coordinate blocks. -/
theorem ouDensityD_add (d₁ d₂ : ℕ) :
    ouDensityD (d₁ + d₂) = prodDensity (ouDensityD d₁) (ouDensityD d₂) := by
  funext z
  exact Fin.prod_univ_add (fun i => gaussianPDFReal 0 1 (z i))

/-- The Gaussian measure in dimension d₁+d₂ is the transported product law. -/
theorem ouDensityD_measure_add (d₁ d₂ : ℕ) :
    densityMeasureD (ouDensityD (d₁ + d₂)) =
      ((densityMeasureD (ouDensityD d₁)).prod (densityMeasureD (ouDensityD d₂))).map (appendEquivM d₁ d₂) := by
  rw [ouDensityD_add, densityMeasureD_prod]

/-- Compatibility with Mathlib's finite products of standard Gaussian laws. -/
theorem gaussianPi_measure_add (d₁ d₂ : ℕ) :
    Measure.pi (fun _ : Fin (d₁ + d₂) => gaussianReal 0 1) =
      ((Measure.pi fun _ : Fin d₁ => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin d₂ => gaussianReal 0 1)).map (appendEquivM d₁ d₂) := by
  simpa only [ouDensityD_measure] using ouDensityD_measure_add d₁ d₂

variable {g₁ h₁ : (Fin d₁ → ℝ) → ℝ} {g₂ h₂ : (Fin d₂ → ℝ) → ℝ}

/-- A tensor in the actual OU domain in dimension d₁+d₂. -/
def ouTensor (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂) : (ouStructureD (d₁ + d₂)).dom :=
  (protoFormD (ouDensityD (d₁ + d₂))).inclusion
    (protoOfFunctionD _ (tensorFun g₁ g₂) (hg₁.tensor hg₂))

/-- OU tensor rule, including mixed carré du champ. -/
theorem ouStructureD_Γ_tensor (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂)
    (hh₁ : IsC1BoundedD h₁) (hh₂ : IsC1BoundedD h₂) :
    ⇑((ouStructureD (d₁ + d₂)).Γ (ouTensor hg₁ hg₂) (ouTensor hh₁ hh₂))
      =ᵐ[densityMeasureD (ouDensityD (d₁ + d₂))] fun z =>
      (ouStructureD d₁).Γ ((protoFormD (ouDensityD d₁)).inclusion (protoOfFunctionD _ g₁ hg₁))
        ((protoFormD (ouDensityD d₁)).inclusion (protoOfFunctionD _ h₁ hh₁)) (prodProj₁ d₁ d₂ z) *
        (g₂ (prodProj₂ d₁ d₂ z) * h₂ (prodProj₂ d₁ d₂ z)) +
      (g₁ (prodProj₁ d₁ d₂ z) * h₁ (prodProj₁ d₁ d₂ z)) *
      (ouStructureD d₂).Γ ((protoFormD (ouDensityD d₂)).inclusion (protoOfFunctionD _ g₂ hg₂))
        ((protoFormD (ouDensityD d₂)).inclusion (protoOfFunctionD _ h₂ hh₂)) (prodProj₂ d₁ d₂ z) := by
  have hp₁ : MeasurePreserving (prodProj₁ d₁ d₂)
      (densityMeasureD (ouDensityD (d₁ + d₂))) (densityMeasureD (ouDensityD d₁)) := by
    rw [ouDensityD_add]
    exact prodProj₁_density_preserving _ _
  have hp₂ : MeasurePreserving (prodProj₂ d₁ d₂)
      (densityMeasureD (ouDensityD (d₁ + d₂))) (densityMeasureD (ouDensityD d₂)) := by
    rw [ouDensityD_add]
    exact prodProj₂_density_preserving _ _
  unfold ouTensor ouStructureD
  simp only [densityStructure_Γ_extendsD]
  filter_upwards [gammaD_ofFunction (ouDensityD (d₁ + d₂)) (hg₁.tensor hg₂) (hh₁.tensor hh₂),
    hp₁.quasiMeasurePreserving.ae (gammaD_ofFunction (ouDensityD d₁) hg₁ hh₁),
    hp₂.quasiMeasurePreserving.ae (gammaD_ofFunction (ouDensityD d₂) hg₂ hh₂)] with z hz hz₁ hz₂
  rw [hz, hz₁, hz₂]
  exact pointGammaD_tensor hg₁.differentiable hg₂.differentiable hh₁.differentiable hh₂.differentiable z

/-- OU diagonal tensor formula with the canonical derivative representatives. -/
theorem ouStructureD_Γ_tensor_diag (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂) :
    ⇑((ouStructureD (d₁ + d₂)).Γ (ouTensor hg₁ hg₂) (ouTensor hg₁ hg₂))
      =ᵐ[densityMeasureD (ouDensityD (d₁ + d₂))] fun z =>
      pointGammaD g₁ g₁ (prodProj₁ d₁ d₂ z) * g₂ (prodProj₂ d₁ d₂ z)^2 +
      g₁ (prodProj₁ d₁ d₂ z)^2 * pointGammaD g₂ g₂ (prodProj₂ d₁ d₂ z) := by
  unfold ouTensor ouStructureD
  rw [densityStructure_Γ_extendsD]
  filter_upwards [gammaD_ofFunction (ouDensityD (d₁ + d₂)) (hg₁.tensor hg₂) (hg₁.tensor hg₂)] with z hz
  rw [hz]
  simpa only [pow_two] using
    pointGammaD_tensor hg₁.differentiable hg₂.differentiable hg₁.differentiable hg₂.differentiable z

/-- OU mixed energy is the sum of the two factor energies weighted by L² pairings. -/
theorem ouStructureD_energy_tensor (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂)
    (hh₁ : IsC1BoundedD h₁) (hh₂ : IsC1BoundedD h₂) :
    (ouStructureD (d₁ + d₂)).energy.E (ouTensor hg₁ hg₂) (ouTensor hh₁ hh₂) =
      (ouStructureD d₁).energy.E ((protoFormD (ouDensityD d₁)).inclusion (protoOfFunctionD _ g₁ hg₁))
        ((protoFormD (ouDensityD d₁)).inclusion (protoOfFunctionD _ h₁ hh₁)) *
        (∫ y, g₂ y * h₂ y ∂densityMeasureD (ouDensityD d₂)) +
      (∫ x, g₁ x * h₁ x ∂densityMeasureD (ouDensityD d₁)) *
      (ouStructureD d₂).energy.E ((protoFormD (ouDensityD d₂)).inclusion (protoOfFunctionD _ g₂ hg₂))
        ((protoFormD (ouDensityD d₂)).inclusion (protoOfFunctionD _ h₂ hh₂)) := by
  unfold ouTensor ouStructureD
  simp only [densityStructureD_energy_ofProto, protoFormD_ofFunction]
  have h := protoForm_tensor (ouDensityD d₁) (ouDensityD d₂) hg₁ hg₂ hh₁ hh₂
  simp only [protoFormD_ofFunction] at h
  rw [← ouDensityD_add] at h
  exact h

/-- OU diagonal energy with the actual L² norms. -/
theorem ouStructureD_energy_tensor_diag (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂) :
    (ouStructureD (d₁ + d₂)).energy.E (ouTensor hg₁ hg₂) (ouTensor hg₁ hg₂) =
      (ouStructureD d₁).energy.E ((protoFormD (ouDensityD d₁)).inclusion (protoOfFunctionD _ g₁ hg₁))
        ((protoFormD (ouDensityD d₁)).inclusion (protoOfFunctionD _ g₁ hg₁)) *
        ‖(protoOfFunctionD (ouDensityD d₂) g₂ hg₂ : Lp ℝ 2 (densityMeasureD (ouDensityD d₂)))‖ ^ 2 +
      ‖(protoOfFunctionD (ouDensityD d₁) g₁ hg₁ : Lp ℝ 2 (densityMeasureD (ouDensityD d₁)))‖ ^ 2 *
      (ouStructureD d₂).energy.E ((protoFormD (ouDensityD d₂)).inclusion (protoOfFunctionD _ g₂ hg₂))
        ((protoFormD (ouDensityD d₂)).inclusion (protoOfFunctionD _ g₂ hg₂)) := by
  rw [ouStructureD_energy_tensor hg₁ hg₂ hg₁ hg₂]
  simp only [← pow_two, protoOfFunctionD_norm_sq (ouDensityD d₁) hg₁,
    protoOfFunctionD_norm_sq (ouDensityD d₂) hg₂]

end ErrorCalculus
