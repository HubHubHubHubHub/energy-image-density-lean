import ErrorCalculus.Dirichlet.DensityDomainEquality
import ErrorCalculus.Dirichlet.DensityDomainEID
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

noncomputable section
open MeasureTheory Filter ProbabilityTheory Topology

namespace ErrorCalculus

/-- The AC characterization of a closed domain transports along equality of measures. -/
theorem ProtoErrorStructure.closure_ac_iff_transport {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ = ν) (P : ProtoErrorStructure ℝ μ) (hP : P.energy.IsClosable)
    (hQ : (P.transport h).energy.IsClosable)
    (he : ∀ u : Lp ℝ 2 μ, u ∈ (P.closure hP).dom ↔ ∃ g : ℝ → ℝ,
      u =ᵐ[μ] g ∧ (∀ a b, AbsolutelyContinuousOnInterval g a b) ∧ MemLp (deriv g) 2 μ)
    (u : Lp ℝ 2 ν) : u ∈ ((P.transport h).closure hQ).dom ↔ ∃ g : ℝ → ℝ,
      u =ᵐ[ν] g ∧ (∀ a b, AbsolutelyContinuousOnInterval g a b) ∧ MemLp (deriv g) 2 ν := by
  subst ν
  exact he u

/-- The OU domain is Gaussian H¹. -/
theorem mem_ouStructure_dom_iff (u : Lp ℝ 2 (gaussianReal 0 1)) :
    u ∈ ouStructure.dom ↔ ∃ g : ℝ → ℝ, u =ᵐ[gaussianReal 0 1] g ∧
      (∀ a b, AbsolutelyContinuousOnInterval g a b) ∧ MemLp (deriv g) 2 (gaussianReal 0 1) :=
  ProtoErrorStructure.closure_ac_iff_transport ouDensity_measure (densityProto ouDensity)
    (protoForm_isClosable ouDensity) ouProto_isClosable (mem_densityStructure_dom_iff ouDensity) u

/-- Γ expressed by any finite-energy AC representative transports with the measure. -/
theorem ProtoErrorStructure.closure_Γ_ac_transport {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ = ν) (P : ProtoErrorStructure ℝ μ) (hP : P.energy.IsClosable)
    (hQ : (P.transport h).energy.IsClosable)
    (he : ∀ (u : (P.closure hP).dom) (g : ℝ → ℝ), (u : Lp ℝ 2 μ) =ᵐ[μ] g →
      (∀ a b, AbsolutelyContinuousOnInterval g a b) → MemLp (deriv g) 2 μ →
      (P.closure hP).Γ u u =ᵐ[μ] fun x => (deriv g x)^2)
    (u : ((P.transport h).closure hQ).dom) (g : ℝ → ℝ)
    (hu : (u : Lp ℝ 2 ν) =ᵐ[ν] g) (hac : ∀ a b, AbsolutelyContinuousOnInterval g a b)
    (hd : MemLp (deriv g) 2 ν) :
    ((P.transport h).closure hQ).Γ u u =ᵐ[ν] fun x => (deriv g x)^2 := by
  subst ν
  exact he u g hu hac hd

/-- Γ on OU computed from any finite-energy AC representative. -/
theorem ouStructure_Γ_representative (u : ouStructure.dom) {g : ℝ → ℝ}
    (hu : (u : Lp ℝ 2 (gaussianReal 0 1)) =ᵐ[gaussianReal 0 1] g)
    (hac : ∀ a b, AbsolutelyContinuousOnInterval g a b)
    (hd : MemLp (deriv g) 2 (gaussianReal 0 1)) :
    ouStructure.Γ u u =ᵐ[gaussianReal 0 1] fun x => (deriv g x)^2 := by
  apply ProtoErrorStructure.closure_Γ_ac_transport ouDensity_measure (densityProto ouDensity)
    (protoForm_isClosable ouDensity) ouProto_isClosable ?_ u g hu hac hd
  intro v f hv hf hdf
  exact densityStructure_Γ_representative ouDensity v
    (weakDeriv_eq_deriv_of_representative ouDensity v hv hf hdf).symm

/-- C¹ functions with Gaussian L² derivative belong to the OU domain. -/
theorem mem_ouStructure_dom_of_C1 (g : ℝ → ℝ) (hC : ContDiff ℝ 1 g)
    (hg : MemLp g 2 (gaussianReal 0 1)) (hd : MemLp (deriv g) 2 (gaussianReal 0 1)) :
    hg.toLp g ∈ ouStructure.dom :=
  (mem_ouStructure_dom_iff _).mpr
    ⟨g, hg.coeFn_toLp, fun _ _ => hC.contDiffOn.absolutelyContinuousOnInterval, hd⟩

/-- The derivative-square formula does not require bounded C¹ representatives. -/
theorem ouStructure_Γ_C1 (g : ℝ → ℝ) (hC : ContDiff ℝ 1 g)
    (hg : MemLp g 2 (gaussianReal 0 1)) (hd : MemLp (deriv g) 2 (gaussianReal 0 1)) :
    ouStructure.Γ ⟨hg.toLp g, mem_ouStructure_dom_of_C1 g hC hg hd⟩
      ⟨hg.toLp g, mem_ouStructure_dom_of_C1 g hC hg hd⟩ =ᵐ[gaussianReal 0 1]
      fun x => (deriv g x)^2 :=
  ouStructure_Γ_representative _ hg.coeFn_toLp
    (fun _ _ => hC.contDiffOn.absolutelyContinuousOnInterval) hd

/-- The Gaussian coordinate, as an actual L² class. -/
def ouCoordinateLp : Lp ℝ 2 (gaussianReal 0 1) :=
  (memLp_id_gaussianReal' 2 (by norm_num)).toLp id

theorem coeFn_ouCoordinateLp : ouCoordinateLp =ᵐ[gaussianReal 0 1] id :=
  MemLp.coeFn_toLp _

/-- The unbounded coordinate belongs to the OU domain. -/
theorem ouStructure_coordinate_mem : ouCoordinateLp ∈ ouStructure.dom := by
  apply mem_ouStructure_dom_of_C1 id contDiff_id
  simpa using (memLp_const (1:ℝ) : MemLp (fun _ : ℝ => (1:ℝ)) 2 (gaussianReal 0 1))

/-- The coordinate bundled with its closed-domain membership. -/
def ouCoordinate : ouStructure.dom := ⟨ouCoordinateLp, ouStructure_coordinate_mem⟩

theorem coeFn_ouCoordinate : (ouCoordinate : Lp ℝ 2 (gaussianReal 0 1)) =ᵐ[gaussianReal 0 1] id :=
  coeFn_ouCoordinateLp

/-- The coordinate has carré du champ one almost everywhere. -/
theorem ouStructure_Γ_coordinate : ouStructure.Γ ouCoordinate ouCoordinate =ᵐ[gaussianReal 0 1]
    fun _ => (1:ℝ) := by
  have hd : MemLp (deriv id) 2 (gaussianReal 0 1) := by
    simpa using (memLp_const (1:ℝ) : MemLp (fun _ : ℝ => (1:ℝ)) 2 (gaussianReal 0 1))
  simpa using ouStructure_Γ_representative ouCoordinate coeFn_ouCoordinate
    (fun _ _ => contDiff_id.contDiffOn.absolutelyContinuousOnInterval) hd

/-- With the paper's normalization the coordinate energy is one half. -/
theorem ouStructure_energy_coordinate : ouStructure.energy.E ouCoordinate ouCoordinate = (1/2:ℝ) := by
  change (1/2:ℝ) * (∫ x, ouStructure.Γ ouCoordinate ouCoordinate x ∂gaussianReal 0 1) = _
  rw [integral_congr_ae ouStructure_Γ_coordinate]
  simp

end ErrorCalculus
