import ErrorCalculus.Dirichlet.ClosureStructure
import ErrorCalculus.Dirichlet.DensityDCalculus
import ErrorCalculus.Dirichlet.DensityDClosure

noncomputable section
open MeasureTheory
namespace ErrorCalculus
variable {d : ℕ}
variable (ρ : (Fin d → ℝ) → ℝ) [IsProbabilityMeasure (densityMeasureD ρ)] [SmoothDensityD ρ]

/-- The closed error structure of a positive C¹ probability density. -/
def densityStructureD : ErrorStructure (Fin d → ℝ) (densityMeasureD ρ) :=
  (densityProtoD ρ).closure (protoFormD_isClosable ρ)

@[simp] theorem densityStructure_energyD : (densityStructureD ρ).energy = dirichletFormD ρ :=
  (densityProtoD ρ).closure_energy (protoFormD_isClosable ρ)

@[simp] theorem densityStructure_domD : (densityStructureD ρ).dom = (dirichletFormD ρ).dom := rfl

/-- The closed carré du champ is the original sum of products of partial derivatives on C¹_b. -/
theorem densityStructure_Γ_extendsD (u v : protoDomD ρ) :
    (densityStructureD ρ).Γ ((protoFormD ρ).inclusion u) ((protoFormD ρ).inclusion v) = gammaD ρ u v :=
  (densityProtoD ρ).closure_Γ_extends (protoFormD_isClosable ρ) u v

theorem densityStructure_Γ_diagonalD (u : protoDomD ρ) :
    ⇑((densityStructureD ρ).Γ ((protoFormD ρ).inclusion u) ((protoFormD ρ).inclusion u)) =ᵐ[densityMeasureD ρ]
      fun x => ∑ i, (fderiv ℝ (repD ρ u) x (Pi.single i 1))^2 := by
  rw [densityStructure_Γ_extendsD]
  filter_upwards [coeFn_gammaD ρ u u] with x hx
  simpa only [pow_two] using hx

/-- The same diagonal identity for an explicitly supplied bounded C¹ function. -/
theorem densityStructureD_Γ_ofFunction (g : (Fin d → ℝ) → ℝ) (hg : IsC1BoundedD g) :
    ⇑((densityStructureD ρ).Γ ((protoFormD ρ).inclusion (protoOfFunctionD ρ g hg))
      ((protoFormD ρ).inclusion (protoOfFunctionD ρ g hg))) =ᵐ[densityMeasureD ρ]
      fun x => ∑ i, (fderiv ℝ g x (Pi.single i 1))^2 := by
  simpa only [rep_protoOfFunctionD] using densityStructure_Γ_diagonalD ρ (protoOfFunctionD ρ g hg)

end ErrorCalculus
