import ErrorCalculus.Dirichlet.DensityDomainRepresentative
import ErrorCalculus.Dirichlet.EIDDensity
import ErrorCalculus.Dirichlet.EIDStability

noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal
namespace ErrorCalculus
variable (ρ : ℝ → ℝ) [SmoothDensity ρ] [IsProbabilityMeasure (densityMeasure ρ)]

/-- The closed-domain energy measure computed through the AC representative. -/
theorem energyMeasure_densityStructure_dom (u : (densityStructure ρ).dom) {ũ : ℝ → ℝ}
    (hd : deriv ũ =ᵐ[densityMeasure ρ] (weakDeriv ρ u : ℝ → ℝ)) :
    (densityStructure ρ).energyMeasure u =
      volume.withDensity (fun x => ENNReal.ofReal ((deriv ũ x)^2 * ρ x)) := by
  unfold ErrorStructure.energyMeasure
  refine (withDensity_congr_ae
    ((densityStructure_Γ_representative ρ u hd).fun_comp ENNReal.ofReal)).trans ?_
  change (densityMeasure ρ).withDensity (fun x => ENNReal.ofReal ((deriv ũ x)^2)) = _
  unfold densityMeasure
  rw [← withDensity_mul volume
    (SmoothDensity.contDiff (ρ := ρ)).continuous.measurable.ennreal_ofReal
    ((measurable_deriv ũ).pow_const 2).ennreal_ofReal]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_mul (sq_nonneg _)]
  exact mul_comm _ _

/-- energy image density holds for every element of the closed density domain. -/
theorem densityStructure_hasEID (u : (densityStructure ρ).dom) :
    (densityStructure ρ).HasEID u := by
  obtain ⟨ũ, c, hf, hu, hc, hac, hder, hd⟩ :=
    exists_absolutelyContinuous_representative_dom ρ u
  unfold ErrorStructure.HasEID
  rw [← (densityStructure ρ).energyMeasure_map_eq
    (densityStructure_representative_dom ρ u hu).symm,
    energyMeasure_densityStructure_dom ρ u hd]
  exact Foundations.map_withDensity_sq_deriv_mul_absolutelyContinuous_of_measurable
    hc.measurable (SmoothDensity.contDiff (ρ := ρ)).continuous.measurable

/-- all scalar Lipschitz compositions of closed-domain elements remain in the domain. -/
theorem densityStructure_lipschitz_mem_dom_closed (u : (densityStructure ρ).dom)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (w : Lp ℝ 2 (densityMeasure ρ))
    (hw : w =ᵐ[densityMeasure ρ] fun x => F ((u : Lp ℝ 2 (densityMeasure ρ)) x)) :
    w ∈ (densityStructure ρ).dom :=
  (densityStructure ρ).lipschitz_comp_mem_dom hF u w hw

/-- The Lipschitz chain rule on the entire domain, with the weak derivative. -/
theorem densityStructure_Γ_lipschitz_comp_dom (u : (densityStructure ρ).dom)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (w : (densityStructure ρ).dom)
    (hw : (w : Lp ℝ 2 (densityMeasure ρ)) =ᵐ[densityMeasure ρ]
      fun x => F ((densityStructure ρ).representative u x)) :
    (densityStructure ρ).Γ w w =ᵐ[densityMeasure ρ]
      fun x => (deriv F ((densityStructure ρ).representative u x))^2 * (weakDeriv ρ u x)^2 := by
  filter_upwards [(densityStructure ρ).lipschitz_calculus_diag
    (densityStructure_hasEID ρ u) hF w hw, densityStructure_Γ_diag ρ u] with x hx hg
  rw [hx, hg]

/-- The same chain rule evaluated at the AC representative and its classical derivative. -/
theorem densityStructure_Γ_lipschitz_comp_representative (u : (densityStructure ρ).dom)
    {ũ : ℝ → ℝ} (hu : (u : Lp ℝ 2 (densityMeasure ρ)) =ᵐ[densityMeasure ρ] ũ)
    (hd : deriv ũ =ᵐ[densityMeasure ρ] (weakDeriv ρ u : ℝ → ℝ))
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (w : (densityStructure ρ).dom)
    (hw : (w : Lp ℝ 2 (densityMeasure ρ)) =ᵐ[densityMeasure ρ] fun x => F (ũ x)) :
    (densityStructure ρ).Γ w w =ᵐ[densityMeasure ρ]
      fun x => (deriv F (ũ x))^2 * (deriv ũ x)^2 := by
  have hr := densityStructure_representative_dom ρ u hu
  have hw' := hw.trans (hr.symm.fun_comp F)
  filter_upwards [densityStructure_Γ_lipschitz_comp_dom ρ u hF w hw', hr, hd] with x hx hr hd
  rw [hx, hr, hd]

/-- absolute value has the same diagonal carré du champ on the entire domain. -/
theorem densityStructure_Γ_abs_dom (u : (densityStructure ρ).dom) :
    (densityStructure ρ).Γ
      ⟨|(u : Lp ℝ 2 (densityMeasure ρ))|,
        (densityStructure ρ).abs_mem_dom (densityStructure_hasEID ρ u)⟩
      ⟨|(u : Lp ℝ 2 (densityMeasure ρ))|,
        (densityStructure ρ).abs_mem_dom (densityStructure_hasEID ρ u)⟩ =ᵐ[densityMeasure ρ]
      fun x => (weakDeriv ρ u x)^2 :=
  ((densityStructure ρ).Γ_abs (densityStructure_hasEID ρ u)).trans
    (densityStructure_Γ_diag ρ u)

/-- Closed-domain counterpart of proto-domain EID transport. -/
theorem ProtoErrorStructure.closure_hasEID_transport_dom {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ = ν) (P : ProtoErrorStructure Ω μ) (hP : P.energy.IsClosable)
    (hQ : (P.transport h).energy.IsClosable)
    (he : ∀ u : (P.closure hP).dom, (P.closure hP).HasEID u)
    (u : ((P.transport h).closure hQ).dom) :
    ((P.transport h).closure hQ).HasEID u := by
  subst ν
  exact he u

/-- EID on the whole Ornstein--Uhlenbeck domain. -/
theorem ouStructure_hasEID (u : ouStructure.dom) : ouStructure.HasEID u :=
  ProtoErrorStructure.closure_hasEID_transport_dom ouDensity_measure (densityProto ouDensity)
    (protoForm_isClosable ouDensity) ouProto_isClosable (densityStructure_hasEID ouDensity) u

/-- Transport of the AC description of a closed domain along equality of measures. -/
theorem ProtoErrorStructure.closure_ac_transport {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ = ν) (P : ProtoErrorStructure ℝ μ) (hP : P.energy.IsClosable)
    (hQ : (P.transport h).energy.IsClosable)
    (he : ∀ u : (P.closure hP).dom, ∃ ũ : ℝ → ℝ,
      (u : Lp ℝ 2 μ) =ᵐ[μ] ũ ∧ Continuous ũ ∧
      (∀ a b, AbsolutelyContinuousOnInterval ũ a b) ∧ MemLp (deriv ũ) 2 μ ∧
      (P.closure hP).Γ u u =ᵐ[μ] fun x => (deriv ũ x)^2)
    (u : ((P.transport h).closure hQ).dom) : ∃ ũ : ℝ → ℝ,
      (u : Lp ℝ 2 ν) =ᵐ[ν] ũ ∧ Continuous ũ ∧
      (∀ a b, AbsolutelyContinuousOnInterval ũ a b) ∧ MemLp (deriv ũ) 2 ν ∧
      ((P.transport h).closure hQ).Γ u u =ᵐ[ν] fun x => (deriv ũ x)^2 := by
  subst ν
  exact he u

/-- Every OU domain element has an AC representative with Gaussian L² derivative and Γ=u′². -/
theorem ouStructure_exists_absolutelyContinuous_representative (u : ouStructure.dom) :
    ∃ ũ : ℝ → ℝ, (u : Lp ℝ 2 (gaussianReal 0 1)) =ᵐ[gaussianReal 0 1] ũ ∧
      Continuous ũ ∧ (∀ a b, AbsolutelyContinuousOnInterval ũ a b) ∧
      MemLp (deriv ũ) 2 (gaussianReal 0 1) ∧
      ouStructure.Γ u u =ᵐ[gaussianReal 0 1] fun x => (deriv ũ x)^2 := by
  apply ProtoErrorStructure.closure_ac_transport ouDensity_measure (densityProto ouDensity)
    (protoForm_isClosable ouDensity) ouProto_isClosable ?_ u
  intro v
  obtain ⟨ũ, c, hf, hu, hc, hac, hder, hd⟩ :=
    exists_absolutelyContinuous_representative_dom ouDensity v
  exact ⟨ũ, hu, hc, hac, densityStructure_deriv_memLp ouDensity v hd,
    densityStructure_Γ_representative ouDensity v hd⟩

end ErrorCalculus
