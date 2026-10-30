import ErrorCalculus.Dirichlet.ClosureExamples
import ErrorCalculus.Dirichlet.LipschitzEID
import Foundations.EnergyImageDensity.C1

noncomputable section
open MeasureTheory Filter ProbabilityTheory
namespace ErrorCalculus
variable (ρ : ℝ → ℝ) [IsProbabilityMeasure (densityMeasure ρ)] [SmoothDensity ρ]

/-- First replace Γ almost everywhere for the original measure, then multiply densities. -/
theorem energyMeasure_densityStructure_proto (u : protoDom ρ) :
    (densityStructure ρ).energyMeasure ((protoForm ρ).inclusion u) =
      volume.withDensity (fun x => ENNReal.ofReal ((deriv (rep ρ u) x)^2 * ρ x)) := by
  unfold ErrorStructure.energyMeasure
  refine (withDensity_congr_ae
    ((densityStructure_Γ_diagonal ρ u).fun_comp ENNReal.ofReal)).trans ?_
  change (densityMeasure ρ).withDensity (fun x => ENNReal.ofReal ((deriv (rep ρ u) x)^2)) = _
  unfold densityMeasure
  rw [← withDensity_mul volume
    (SmoothDensity.contDiff (ρ := ρ)).continuous.measurable.ennreal_ofReal
    ((measurable_deriv (rep ρ u)).pow_const 2).ennreal_ofReal]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_mul (sq_nonneg _)]
  exact mul_comm _ _

/-- The measurable representative agrees with the original C¹ representative. -/
theorem densityStructure_representative_proto (u : protoDom ρ) :
    (densityStructure ρ).representative ((protoForm ρ).inclusion u) =ᵐ[densityMeasure ρ]
      rep ρ u :=
  ((densityStructure ρ).coeFn_representative ((protoForm ρ).inclusion u)).symm.trans
    (coeFn_rep ρ u)

/-- The image of the energy measure can be computed with the C¹ representative. -/
theorem energyMeasure_densityStructure_map_rep (u : protoDom ρ) :
    ((densityStructure ρ).energyMeasure ((protoForm ρ).inclusion u)).map (rep ρ u) =
      ((densityStructure ρ).energyMeasure ((protoForm ρ).inclusion u)).map
        ((densityStructure ρ).representative ((protoForm ρ).inclusion u)) :=
  (densityStructure ρ).energyMeasure_map_eq (densityStructure_representative_proto ρ u).symm

/-- scalar energy image density for every element of the bounded C¹ proto-domain. -/
theorem densityStructure_hasEID_proto (u : protoDom ρ) :
    (densityStructure ρ).HasEID ((protoForm ρ).inclusion u) := by
  unfold ErrorStructure.HasEID
  rw [← energyMeasure_densityStructure_map_rep, energyMeasure_densityStructure_proto]
  exact Foundations.map_withDensity_sq_deriv_mul_absolutelyContinuous
    (rep_isC1Bounded ρ u).1 (SmoothDensity.contDiff (ρ := ρ)).continuous.measurable

/-- Transport preserves EID on the proto-domain of the closure. -/
theorem ProtoErrorStructure.closure_hasEID_transport {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ = ν) (P : ProtoErrorStructure Ω μ) (hP : P.energy.IsClosable)
    (hQ : (P.transport h).energy.IsClosable)
    (he : ∀ u : P.dom, (P.closure hP).HasEID (P.energy.inclusion u))
    (u : (P.transport h).dom) :
    ((P.transport h).closure hQ).HasEID ((P.transport h).energy.inclusion u) := by
  subst ν
  exact he u

/-- The same statement on Mathlib's standard Gaussian probability space. -/
theorem ouStructure_hasEID_proto (u : ouProto.dom) :
    ouStructure.HasEID (ouProto.energy.inclusion u) :=
  ProtoErrorStructure.closure_hasEID_transport ouDensity_measure (densityProto ouDensity)
    (protoForm_isClosable ouDensity) ouProto_isClosable
    (densityStructure_hasEID_proto ouDensity) u

/-- Equality of measures transports an almost everywhere representative. -/
theorem ProtoErrorStructure.coeFn_transportDom {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ = ν) (P : ProtoErrorStructure Ω μ) (u : P.dom) (g : Ω → ℝ)
    (hg : ⇑(u : Lp ℝ 2 μ) =ᵐ[μ] g) :
    ⇑(P.transportDom h u : Lp ℝ 2 ν) =ᵐ[ν] g := by
  subst ν
  exact hg

/-- The explicit Gaussian proto-element has the supplied representative. -/
theorem coeFn_ouProtoOfFunction (g : ℝ → ℝ) (hg : IsC1Bounded g) :
    ⇑(ouProtoOfFunction g hg : Lp ℝ 2 (gaussianReal 0 1)) =ᵐ[gaussianReal 0 1] g := by
  apply ProtoErrorStructure.coeFn_transportDom ouDensity_measure (densityProto ouDensity)
  simpa only [rep_protoOfFunction] using
    coeFn_rep ouDensity (protoOfFunction ouDensity g hg)

end ErrorCalculus
