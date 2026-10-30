import ErrorCalculus.Dirichlet.DensityDomainWeakDeriv
import ErrorCalculus.Dirichlet.LipschitzEID
import Mathlib.MeasureTheory.Function.Holder

noncomputable section
open MeasureTheory Filter Topology
set_option linter.unusedSectionVars false
namespace ErrorCalculus
variable (ρ : ℝ → ℝ) [SmoothDensity ρ] [IsProbabilityMeasure (densityMeasure ρ)]

/--
Every closed-domain element has an absolutely continuous primitive representative with the
prescribed derivative.
-/
theorem exists_absolutelyContinuous_representative_dom (u : (densityStructure ρ).dom) :
    ∃ (ũ : ℝ → ℝ) (c : ℝ),
      (∀ x, ũ x = c + ∫ t in (0:ℝ)..x, weakDeriv ρ u t) ∧
      (u : Lp ℝ 2 (densityMeasure ρ)) =ᵐ[densityMeasure ρ] ũ ∧ Continuous ũ ∧
      (∀ a b, AbsolutelyContinuousOnInterval ũ a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt ũ (weakDeriv ρ u x) x) ∧
      deriv ũ =ᵐ[densityMeasure ρ] (weakDeriv ρ u : ℝ → ℝ) := by
  obtain ⟨s, hs, hG⟩ := weakDeriv_spec ρ u
  apply Foundations.exists_absolutelyContinuous_representative_Lp
    (SmoothDensity.contDiff (ρ := ρ)).continuous (SmoothDensity.pos (ρ := ρ))
    (fun n => (s n : Lp ℝ 2 (densityMeasure ρ)))
    (u : Lp ℝ 2 (densityMeasure ρ)) (weakDeriv ρ u)
    (fun n => (rep_isC1Bounded ρ (s n)).1) (fun n => coeFn_rep ρ (s n))
    (fun n => (rep_isC1Bounded ρ (s n)).deriv_memLp (densityMeasure ρ) 2) hs.2
  change Tendsto (fun n => grad ρ (s n)) atTop (𝓝 (weakDeriv ρ u))
  exact hG

/-- The measurable representative used for EID agrees with any representative of the class. -/
theorem densityStructure_representative_dom (u : (densityStructure ρ).dom) {ũ : ℝ → ℝ}
    (hũ : (u : Lp ℝ 2 (densityMeasure ρ)) =ᵐ[densityMeasure ρ] ũ) :
    (densityStructure ρ).representative u =ᵐ[densityMeasure ρ] ũ :=
  ((densityStructure ρ).coeFn_representative u).symm.trans hũ

/-- Hölder's continuous product, including the passage from L² squares to L¹. -/
def densityL2Product : Lp ℝ 2 (densityMeasure ρ) →L[ℝ]
    Lp ℝ 2 (densityMeasure ρ) →L[ℝ] Lp ℝ 1 (densityMeasure ρ) :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (densityMeasure ρ) 2 2 1

theorem coeFn_densityL2Product (f g : Lp ℝ 2 (densityMeasure ρ)) :
    densityL2Product ρ f g =ᵐ[densityMeasure ρ] fun x => f x * g x :=
  (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder f g

/-- The original carré du champ is exactly the L¹ product of gradient classes. -/
theorem gamma₀_eq_densityL2Product (u v : protoDom ρ) :
    gamma₀ ρ u v = densityL2Product ρ (grad ρ u) (grad ρ v) := by
  apply Lp.ext
  filter_upwards [coeFn_gamma₀ ρ u v, coeFn_grad ρ u, coeFn_grad ρ v,
    coeFn_densityL2Product ρ (grad ρ u) (grad ρ v)] with x hx hu hv hp
  rw [hx, hp, hu, hv]

/-- both characterizations have the same L¹ limit, for arbitrary pairs. -/
theorem densityStructure_Γ_eq_product (u v : (densityStructure ρ).dom) :
    (densityStructure ρ).Γ u v = densityL2Product ρ (weakDeriv ρ u) (weakDeriv ρ v) := by
  obtain ⟨s, hs, hG⟩ := weakDeriv_spec ρ u
  obtain ⟨t, ht, hH⟩ := weakDeriv_spec ρ v
  have hΓ := (protoData ρ).closureGamma_characterization (protoForm_isClosable ρ) hs ht
  have hp := ((densityL2Product ρ).continuous₂.tendsto
    (weakDeriv ρ u, weakDeriv ρ v)).comp (hG.prodMk_nhds hH)
  change Tendsto (fun n => gamma₀ ρ (s n) (t n)) atTop
    (𝓝 ((densityStructure ρ).Γ u v)) at hΓ
  simp_rw [gamma₀_eq_densityL2Product] at hΓ
  exact tendsto_nhds_unique hΓ hp

/-- The mixed carré du champ on the entire closed domain. -/
theorem densityStructure_Γ_closure (u v : (densityStructure ρ).dom) :
    (densityStructure ρ).Γ u v =ᵐ[densityMeasure ρ]
      fun x => weakDeriv ρ u x * weakDeriv ρ v x := by
  rw [densityStructure_Γ_eq_product]
  exact coeFn_densityL2Product ρ _ _

/-- Γ[u] is the square of the weak derivative on the entire domain. -/
theorem densityStructure_Γ_diag (u : (densityStructure ρ).dom) :
    (densityStructure ρ).Γ u u =ᵐ[densityMeasure ρ] fun x => (weakDeriv ρ u x)^2 := by
  simpa only [pow_two] using densityStructure_Γ_closure ρ u u

/-- continuity of the inner product identifies the closed bilinear energy. -/
theorem densityStructure_energy_closure (u v : (densityStructure ρ).dom) :
    (densityStructure ρ).energy.E u v =
      (1/2:ℝ) * inner ℝ (weakDeriv ρ u) (weakDeriv ρ v) := by
  obtain ⟨s, hs, hG⟩ := weakDeriv_spec ρ u
  obtain ⟨t, ht, hH⟩ := weakDeriv_spec ρ v
  have he := (protoForm ρ).closure_characterization (protoForm_isClosable ρ)
    hs ht u.property v.property
  calc
    _ = ((protoForm ρ).closure (protoForm_isClosable ρ)).E u v :=
      (protoData ρ).closureGamma_energy (protoForm_isClosable ρ) u v
    _ = _ := by
      apply tendsto_nhds_unique he
      simpa only [protoForm_eq_inner_grad] using (hG.inner (𝕜 := ℝ) hH).const_mul (1/2:ℝ)

/-- The diagonal formula expressed through a representative's derivative. -/
theorem densityStructure_Γ_representative (u : (densityStructure ρ).dom) {ũ : ℝ → ℝ}
    (hd : deriv ũ =ᵐ[densityMeasure ρ] (weakDeriv ρ u : ℝ → ℝ)) :
    (densityStructure ρ).Γ u u =ᵐ[densityMeasure ρ] fun x => (deriv ũ x)^2 := by
  filter_upwards [densityStructure_Γ_diag ρ u, hd] with x hx hd
  rw [hx, hd]

/-- The energy of a domain element is half the integral of the squared derivative. -/
theorem densityStructure_energy_representative (u : (densityStructure ρ).dom) {ũ : ℝ → ℝ}
    (hd : deriv ũ =ᵐ[densityMeasure ρ] (weakDeriv ρ u : ℝ → ℝ)) :
    (densityStructure ρ).energy.E u u =
      (1/2:ℝ) * ∫ x, (deriv ũ x)^2 ∂densityMeasure ρ := by
  rw [densityStructure_energy_closure, real_inner_self_eq_norm_sq, lp_two_norm_sq]
  congr 1
  apply integral_congr_ae
  filter_upwards [hd] with x hx
  rw [hx]

/-- The same energy as a weighted Lebesgue integral, with the weight written explicitly. -/
theorem densityStructure_energy_representative_weighted (u : (densityStructure ρ).dom)
    {ũ : ℝ → ℝ} (hd : deriv ũ =ᵐ[densityMeasure ρ] (weakDeriv ρ u : ℝ → ℝ)) :
    (densityStructure ρ).energy.E u u = (1/2:ℝ) * ∫ x, (deriv ũ x)^2 * ρ x := by
  rw [densityStructure_energy_representative ρ u hd, integral_density]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => mul_comm _ _

/-- D.3(b)(d): the mixed carré du champ through derivatives of AC representatives. -/
theorem densityStructure_Γ_representative_mixed (u v : (densityStructure ρ).dom)
    {ũ vrep : ℝ → ℝ}
    (hu : deriv ũ =ᵐ[densityMeasure ρ] (weakDeriv ρ u : ℝ → ℝ))
    (hv : deriv vrep =ᵐ[densityMeasure ρ] (weakDeriv ρ v : ℝ → ℝ)) :
    (densityStructure ρ).Γ u v =ᵐ[densityMeasure ρ] fun x => deriv ũ x * deriv vrep x := by
  filter_upwards [densityStructure_Γ_closure ρ u v, hu, hv] with x hx hu hv
  rw [hx, hu, hv]

/-- The derivative of the AC representative belongs to weighted L². -/
theorem densityStructure_deriv_memLp (u : (densityStructure ρ).dom) {ũ : ℝ → ℝ}
    (hd : deriv ũ =ᵐ[densityMeasure ρ] (weakDeriv ρ u : ℝ → ℝ)) :
    MemLp (deriv ũ) 2 (densityMeasure ρ) := (Lp.memLp _).ae_eq hd.symm

end ErrorCalculus
