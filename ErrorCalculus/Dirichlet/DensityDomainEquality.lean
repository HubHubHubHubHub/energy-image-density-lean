import ErrorCalculus.Dirichlet.DensityDomainRepresentative
import Foundations.Sobolev1D.Density

noncomputable section
open MeasureTheory Filter Topology
set_option linter.unusedSectionVars false

namespace ErrorCalculus
variable (ρ : ℝ → ℝ) [SmoothDensity ρ] [IsProbabilityMeasure (densityMeasure ρ)]

/-- Convergence in L² of functions and gradients supplies an approaching sequence. -/
theorem approaches_of_tendsto_grad {s : ℕ → protoDom ρ}
    {u G : Lp ℝ 2 (densityMeasure ρ)}
    (hu : Tendsto (fun n => (s n : Lp ℝ 2 (densityMeasure ρ))) atTop (𝓝 u))
    (hG : Tendsto (fun n => grad ρ (s n)) atTop (𝓝 G)) :
    (protoForm ρ).Approaches s u := by
  refine ⟨((protoForm ρ).isCauchy_iff s).mpr ⟨hu.cauchySeq, ?_⟩, hu⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hG.cauchySeq ε hε
  refine ⟨N, fun m hm n hn => lt_of_le_of_lt ?_ (hN m hm n hn)⟩
  rw [dist_eq_norm, ← map_sub]
  have hs : (protoForm ρ).seminorm (s m - s n) ^ 2 =
      (1/2:ℝ) * ‖grad ρ (s m - s n)‖ ^ 2 :=
    (Real.sq_sqrt ((protoForm ρ).nonneg _)).trans (protoForm_eq_grad ρ _)
  have hp : 0 ≤ (protoForm ρ).seminorm (s m - s n) := Real.sqrt_nonneg _
  apply (sq_le_sq₀ hp (norm_nonneg _)).mp
  nlinarith [sq_nonneg ‖grad ρ (s m - s n)‖]

/--
Every locally absolutely continuous L² representative with finite weighted derivative energy admits
compactly supported C¹ proto-domain approximants converging in L² together with their gradients.
-/
theorem exists_C1c_approaches_of_absolutelyContinuous
    (u : Lp ℝ 2 (densityMeasure ρ)) {ũ : ℝ → ℝ}
    (hrep : u =ᵐ[densityMeasure ρ] ũ)
    (hac : ∀ a b, AbsolutelyContinuousOnInterval ũ a b)
    (hd : MemLp (deriv ũ) 2 (densityMeasure ρ)) :
    ∃ s : ℕ → protoDom ρ, (∀ n, HasCompactSupport (rep ρ (s n))) ∧
      (protoForm ρ).Approaches s u ∧
      Tendsto (fun n => grad ρ (s n)) atTop (𝓝 (hd.toLp (deriv ũ))) := by
  have hp : ũ = Foundations.primitiveRepresentative (ũ 0) (hd.toLp (deriv ũ)) := by
    calc
      ũ = Foundations.primitiveRepresentative (ũ 0) (deriv ũ) :=
        Foundations.eq_primitiveRepresentative_of_locallyAC hac
      _ = _ := by
        funext x
        unfold Foundations.primitiveRepresentative Foundations.primitive
        congr 1
        apply intervalIntegral.integral_congr_ae
        filter_upwards [volume_absolutelyContinuous_density.ae_le hd.coeFn_toLp] with t ht
        exact fun _ => ht.symm
  obtain ⟨f, hf, hdf, hC, hc, ht, hdt⟩ :=
    Foundations.exists_C1c_tendsto_H1_Lp
      (SmoothDensity.contDiff (ρ := ρ)).continuous (SmoothDensity.pos (ρ := ρ))
      u (hd.toLp (deriv ũ)) (ũ 0) (hrep.trans (ae_of_all _ (congrFun hp)))
  let hb n := isC1Bounded_of_hasCompactSupport (hC n) (hc n)
  let s n := protoOfFunction ρ (f n) (hb n)
  have he n : (s n : Lp ℝ 2 (densityMeasure ρ)) = (hf n).toLp (f n) := rfl
  have hg n : grad ρ (s n) = (hdf n).toLp (deriv (f n)) := by
    apply Lp.ext
    have hgrad := coeFn_grad ρ (s n)
    have hr : rep ρ (s n) = f n := rep_protoOfFunction ρ (f n) (hb n)
    rw [hr] at hgrad
    exact hgrad.trans (hdf n).coeFn_toLp.symm
  have ht' : Tendsto (fun n => (s n : Lp ℝ 2 (densityMeasure ρ))) atTop (𝓝 u) := by
    change Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 u)
    exact ht
  have hdt' : Tendsto (fun n => grad ρ (s n)) atTop (𝓝 (hd.toLp (deriv ũ))) := by
    rw [show (fun n => grad ρ (s n)) = (fun n => (hdf n).toLp (deriv (f n))) from funext hg]
    exact hdt
  exact ⟨s, fun n => by simpa only [s, rep_protoOfFunction] using hc n,
    approaches_of_tendsto_grad ρ ht' hdt', hdt'⟩

/-- Every locally absolutely continuous L² representative of finite energy is in the domain. -/
theorem mem_dom_of_absolutelyContinuous (u : Lp ℝ 2 (densityMeasure ρ)) {ũ : ℝ → ℝ}
    (hrep : u =ᵐ[densityMeasure ρ] ũ)
    (hac : ∀ a b, AbsolutelyContinuousOnInterval ũ a b)
    (hd : MemLp (deriv ũ) 2 (densityMeasure ρ)) : u ∈ (densityStructure ρ).dom := by
  obtain ⟨s, hc, hs, hG⟩ := exists_C1c_approaches_of_absolutelyContinuous ρ u hrep hac hd
  exact ((protoForm ρ).mem_closureDom_iff u).mpr ⟨s, hs⟩

/-- G.1/G.2: the weak derivative agrees with the derivative of every such representative. -/
theorem weakDeriv_eq_deriv_of_representative (u : (densityStructure ρ).dom) {ũ : ℝ → ℝ}
    (hrep : (u : Lp ℝ 2 (densityMeasure ρ)) =ᵐ[densityMeasure ρ] ũ)
    (hac : ∀ a b, AbsolutelyContinuousOnInterval ũ a b)
    (hd : MemLp (deriv ũ) 2 (densityMeasure ρ)) :
    weakDeriv ρ u =ᵐ[densityMeasure ρ] deriv ũ := by
  obtain ⟨s, hc, hs, hG⟩ := exists_C1c_approaches_of_absolutelyContinuous ρ u hrep hac hd
  have he := tendsto_nhds_unique (tendsto_grad_of_approaches ρ hs) hG
  rw [he]
  exact hd.coeFn_toLp

/-- The domain is exactly the classes with an AC representative and L² derivative. -/
theorem mem_densityStructure_dom_iff (u : Lp ℝ 2 (densityMeasure ρ)) :
    u ∈ (densityStructure ρ).dom ↔ ∃ ũ : ℝ → ℝ, u =ᵐ[densityMeasure ρ] ũ ∧
      (∀ a b, AbsolutelyContinuousOnInterval ũ a b) ∧
      MemLp (deriv ũ) 2 (densityMeasure ρ) := by
  constructor
  · intro hu
    obtain ⟨ũ, c, hf, he, hc, hac, hder, hd⟩ :=
      exists_absolutelyContinuous_representative_dom ρ ⟨u, hu⟩
    exact ⟨ũ, he, hac, densityStructure_deriv_memLp ρ ⟨u, hu⟩ hd⟩
  · rintro ⟨ũ, he, hac, hd⟩
    exact mem_dom_of_absolutelyContinuous ρ u he hac hd

/-- equality with Foundations' weighted H¹ space, defined as a closed graph. -/
theorem mem_densityStructure_dom_iff_memH1Density (u : Lp ℝ 2 (densityMeasure ρ)) :
    u ∈ (densityStructure ρ).dom ↔ Foundations.MemH1Density ρ u :=
  (mem_densityStructure_dom_iff ρ u).trans
    (Foundations.mem_H1_iff_exists_absolutelyContinuous_representative
      (SmoothDensity.contDiff (ρ := ρ)).continuous (SmoothDensity.pos (ρ := ρ)) u).symm

/-- no boundedness is required of a C¹ function or its derivative. -/
theorem mem_dom_of_C1 (g : ℝ → ℝ) (hC : ContDiff ℝ 1 g)
    (hg : MemLp g 2 (densityMeasure ρ)) (hd : MemLp (deriv g) 2 (densityMeasure ρ)) :
    hg.toLp g ∈ (densityStructure ρ).dom :=
  mem_dom_of_absolutelyContinuous ρ _ hg.coeFn_toLp
    (fun _ _ => hC.contDiffOn.absolutelyContinuousOnInterval) hd

/-- Γ for arbitrary C¹ functions of finite weighted H¹ norm. -/
theorem densityStructure_Γ_C1 (g : ℝ → ℝ) (hC : ContDiff ℝ 1 g)
    (hg : MemLp g 2 (densityMeasure ρ)) (hd : MemLp (deriv g) 2 (densityMeasure ρ)) :
    (densityStructure ρ).Γ ⟨hg.toLp g, mem_dom_of_C1 ρ g hC hg hd⟩
      ⟨hg.toLp g, mem_dom_of_C1 ρ g hC hg hd⟩ =ᵐ[densityMeasure ρ]
      fun x => (deriv g x)^2 := by
  apply densityStructure_Γ_representative
  exact (weakDeriv_eq_deriv_of_representative ρ
    ⟨hg.toLp g, mem_dom_of_C1 ρ g hC hg hd⟩ hg.coeFn_toLp
    (fun _ _ => hC.contDiffOn.absolutelyContinuousOnInterval) hd).symm

/-- energy for arbitrary C¹ functions of finite weighted H¹ norm. -/
theorem densityStructure_energy_C1 (g : ℝ → ℝ) (hC : ContDiff ℝ 1 g)
    (hg : MemLp g 2 (densityMeasure ρ)) (hd : MemLp (deriv g) 2 (densityMeasure ρ)) :
    (densityStructure ρ).energy.E ⟨hg.toLp g, mem_dom_of_C1 ρ g hC hg hd⟩
      ⟨hg.toLp g, mem_dom_of_C1 ρ g hC hg hd⟩ =
      (1/2:ℝ) * ∫ x, (deriv g x)^2 ∂densityMeasure ρ := by
  apply densityStructure_energy_representative
  exact (weakDeriv_eq_deriv_of_representative ρ
    ⟨hg.toLp g, mem_dom_of_C1 ρ g hC hg hd⟩ hg.coeFn_toLp
    (fun _ _ => hC.contDiffOn.absolutelyContinuousOnInterval) hd).symm

end ErrorCalculus
