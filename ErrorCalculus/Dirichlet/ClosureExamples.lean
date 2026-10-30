import ErrorCalculus.Dirichlet.ClosureStructure
import ErrorCalculus.Dirichlet.DensityGaussian

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ErrorCalculus
variable (ρ : ℝ → ℝ) [IsProbabilityMeasure (densityMeasure ρ)] [SmoothDensity ρ]

/-- The closed error structure of a positive C¹ probability density. -/
def densityStructure : ErrorStructure ℝ (densityMeasure ρ) :=
  (densityProto ρ).closure (protoForm_isClosable ρ)

@[simp] theorem densityStructure_energy : (densityStructure ρ).energy = dirichletForm ρ :=
  (densityProto ρ).closure_energy (protoForm_isClosable ρ)

@[simp] theorem densityStructure_dom : (densityStructure ρ).dom = (dirichletForm ρ).dom := rfl

/-- The closed carré du champ is the original product of derivatives on C¹_b. -/
theorem densityStructure_Γ_extends (u v : protoDom ρ) :
    (densityStructure ρ).Γ ((protoForm ρ).inclusion u) ((protoForm ρ).inclusion v) = gamma₀ ρ u v :=
  (densityProto ρ).closure_Γ_extends (protoForm_isClosable ρ) u v

theorem densityStructure_Γ_diagonal (u : protoDom ρ) :
    ⇑((densityStructure ρ).Γ ((protoForm ρ).inclusion u) ((protoForm ρ).inclusion u)) =ᵐ[densityMeasure ρ]
      fun x => (deriv (rep ρ u) x)^2 := by
  rw [densityStructure_Γ_extends]
  filter_upwards [coeFn_gamma₀ ρ u u] with x hx
  simpa only [pow_two] using hx

/-- The same diagonal identity for an explicitly supplied bounded C¹ function. -/
theorem densityStructure_Γ_ofFunction (g : ℝ → ℝ) (hg : IsC1Bounded g) :
    ⇑((densityStructure ρ).Γ ((protoForm ρ).inclusion (protoOfFunction ρ g hg))
      ((protoForm ρ).inclusion (protoOfFunction ρ g hg))) =ᵐ[densityMeasure ρ]
      fun x => (deriv g x)^2 := by
  simpa only [rep_protoOfFunction] using densityStructure_Γ_diagonal ρ (protoOfFunction ρ g hg)

/-- Transport of a domain element along equality of measures. -/
def ProtoErrorStructure.transportDom {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ = ν) (S : ProtoErrorStructure Ω μ)
    (u : S.dom) : (S.transport h).dom := by
  subst ν
  exact u

theorem ProtoErrorStructure.transport_diagonal {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ = ν) (S : ProtoErrorStructure Ω μ)
    (u : S.dom) (g : Ω → ℝ) (hg : ⇑(S.Γ u u) =ᵐ[μ] g) :
    ⇑((S.transport h).Γ (S.transportDom h u) (S.transportDom h u)) =ᵐ[ν] g := by
  subst ν
  exact hg

/-- Ornstein--Uhlenbeck error structure on Mathlib's standard Gaussian. -/
def ouStructure : ErrorStructure ℝ (gaussianReal 0 1) := ouProto.closure ouProto_isClosable

@[simp] theorem ouStructure_energy : ouStructure.energy = ouProto.energy.closure ouProto_isClosable :=
  ouProto.closure_energy ouProto_isClosable

@[simp] theorem ouStructure_dom : ouStructure.dom = ouProto.energy.closureDom := rfl

theorem ouStructure_Γ_extends (u v : ouProto.dom) :
    ouStructure.Γ (ouProto.energy.inclusion u) (ouProto.energy.inclusion v) = ouProto.Γ u v :=
  ouProto.closure_Γ_extends ouProto_isClosable u v

/-- Explicit C¹_b elements of the Gaussian proto-domain. -/
def ouProtoOfFunction (g : ℝ → ℝ) (hg : IsC1Bounded g) : ouProto.dom :=
  (densityProto ouDensity).transportDom ouDensity_measure (protoOfFunction ouDensity g hg)

/-- Γ[u]=u′² on C¹_b, on gaussianReal 0 1 itself. -/
theorem ouStructure_Γ_ofFunction (g : ℝ → ℝ) (hg : IsC1Bounded g) :
    ⇑(ouStructure.Γ (ouProto.energy.inclusion (ouProtoOfFunction g hg))
      (ouProto.energy.inclusion (ouProtoOfFunction g hg))) =ᵐ[gaussianReal 0 1]
      fun x => (deriv g x)^2 := by
  rw [ouStructure_Γ_extends]
  apply (densityProto ouDensity).transport_diagonal ouDensity_measure (protoOfFunction ouDensity g hg)
  filter_upwards [coeFn_gamma₀ ouDensity (protoOfFunction ouDensity g hg) (protoOfFunction ouDensity g hg)] with x hx
  simp only [rep_protoOfFunction] at hx
  exact hx.trans (pow_two _).symm

end ErrorCalculus
