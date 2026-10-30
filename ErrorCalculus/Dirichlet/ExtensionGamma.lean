import ErrorCalculus.Dirichlet.ExtensionGammaBounds
import ErrorCalculus.Dirichlet.Extension
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorData
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorData Ω μ)

/-- Identity from the energy type synonym to the original domain. -/
def energyToDom : S.energy.EnergySpace →ₗ[ℝ] S.dom where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Γ as a bounded bilinear map on the energy seminormed space. -/
def energyGamma : S.energy.EnergySpace →L[ℝ] S.energy.EnergySpace →L[ℝ] Lp ℝ 1 μ :=
  (S.Γ.compl₁₂ S.energyToDom S.energyToDom).mkContinuous₂ 2 (by
    intro u v
    have hu : ‖u‖ = S.energy.seminorm u := norm_eq_sqrt_real_inner u
    have hv : ‖v‖ = S.energy.seminorm v := norm_eq_sqrt_real_inner v
    rw [hu, hv]
    exact S.norm_gamma_le_energy u v)

/-- First extend in the first variable, then flip and extend in the second variable. -/
def completedGamma : S.energy.EnergyHilbert →L[ℝ] S.energy.EnergyHilbert →L[ℝ] Lp ℝ 1 μ :=
  (((S.energyGamma.extend UniformSpace.Completion.toComplL).flip).extend
    UniformSpace.Completion.toComplL).flip

@[simp] theorem completedGamma_coe (u v : S.energy.EnergySpace) :
    S.completedGamma (u : S.energy.EnergyHilbert) (v : S.energy.EnergyHilbert) = S.Γ (S.energy.toEnergy.symm u) (S.energy.toEnergy.symm v) := by
  change S.completedGamma ((UniformSpace.Completion.toComplL : S.energy.EnergySpace →L[ℝ] S.energy.EnergyHilbert) u) ((UniformSpace.Completion.toComplL : S.energy.EnergySpace →L[ℝ] S.energy.EnergyHilbert) v) = _
  simp only [completedGamma, ContinuousLinearMap.flip_apply]
  rw [ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _)]
  simp only [ContinuousLinearMap.flip_apply]
  rw [ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _)]
  rfl

@[simp] theorem completedGamma_j (u v : S.dom) :
    S.completedGamma (S.energy.j u) (S.energy.j v) = S.Γ u v :=
  S.completedGamma_coe u v

/-- convergence in L¹ whenever the energy coordinates converge. -/
theorem gamma_tendsto_of_energy {u v : ℕ → S.dom} {a b : S.energy.EnergyHilbert}
    (hu : Tendsto (fun n => S.energy.j (u n)) atTop (𝓝 a))
    (hv : Tendsto (fun n => S.energy.j (v n)) atTop (𝓝 b)) :
    Tendsto (fun n => S.Γ (u n) (v n)) atTop (𝓝 (S.completedGamma a b)) := by
  have ht := (S.completedGamma.continuous₂.tendsto (a,b)).comp (hu.prodMk_nhds hv)
  change Tendsto (fun n => S.completedGamma (S.energy.j (u n)) (S.energy.j (v n))) atTop (𝓝 (S.completedGamma a b)) at ht
  simp only [S.completedGamma_j] at ht
  exact ht

/-- Every pair of form-Cauchy sequences has an L¹ limit. -/
theorem exists_gamma_limit {u v : ℕ → S.dom}
    (hu : S.energy.IsCauchy u) (hv : S.energy.IsCauchy v) :
    ∃ g : Lp ℝ 1 μ, Tendsto (fun n => S.Γ (u n) (v n)) atTop (𝓝 g) := by
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hu.2
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hv.2
  exact ⟨_, S.gamma_tendsto_of_energy ha hb⟩

/-- Cauchy convergence of the square roots, before closability. -/
theorem cauchySeq_sqrtGamma {u : ℕ → S.dom} (hu : S.energy.IsCauchy u) :
    CauchySeq (fun n => S.sqrtGamma (u n)) := by
  rw [Metric.cauchySeq_iff]
  have hc := (S.energy.isCauchy_iff u).mp hu |>.2
  intro ε hε
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨N, hN⟩ := hc (ε / Real.sqrt 2) (div_pos hε hs)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  apply (S.norm_sqrtGamma_sub_le _ _).trans_lt
  have hmn := (lt_div_iff₀ hs).mp (hN m hm n hn)
  rw [mul_comm] at hmn
  exact hmn

/-- The L² limit of square roots is nonnegative almost everywhere. -/
theorem exists_sqrtGamma_limit {u : ℕ → S.dom} (hu : S.energy.IsCauchy u) :
    ∃ g : Lp ℝ 2 μ, (0 ≤ᵐ[μ] ⇑g) ∧ Tendsto (fun n => S.sqrtGamma (u n)) atTop (𝓝 g) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (S.cauchySeq_sqrtGamma hu)
  refine ⟨g, (Lp.coeFn_nonneg g).mpr (ge_of_tendsto' hg fun n => ?_), hg⟩
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [S.coeFn_sqrtGamma (u n)] with ω hω
  rw [hω]
  exact Real.sqrt_nonneg _

/-- pull back the completed bilinear map along the unique closed energy graph. -/
def closureGamma (h : S.energy.IsClosable) :
    S.energy.closureDom →ₗ[ℝ] S.energy.closureDom →ₗ[ℝ] Lp ℝ 1 μ where
  toFun u := (S.completedGamma (S.energy.closureLift h u)).toLinearMap.comp (S.energy.closureLift h)
  map_add' u v := by ext w : 1; simp
  map_smul' c u := by ext w : 1; simp

/-- characterization by every pair of approaching sequences. -/
theorem closureGamma_characterization (h : S.energy.IsClosable)
    {u v : ℕ → S.dom} {a b : S.energy.closureDom}
    (hu : S.energy.Approaches u a) (hv : S.energy.Approaches v b) :
    Tendsto (fun n => S.Γ (u n) (v n)) atTop (𝓝 (S.closureGamma h a b)) :=
  S.gamma_tendsto_of_energy (S.energy.approaches_tendsto_lift h hu a.property)
    (S.energy.approaches_tendsto_lift h hv b.property)

/-- independence is inherited from closedGraph_unique, hence from closability. -/
theorem closureGamma_independent (h : S.energy.IsClosable)
    {u u' v v' : ℕ → S.dom} {a b : Lp ℝ 2 μ}
    (hu : S.energy.Approaches u a) (hu' : S.energy.Approaches u' a)
    (hv : S.energy.Approaches v b) (hv' : S.energy.Approaches v' b) :
    limUnder atTop (fun n => S.Γ (u n) (v n)) =
      limUnder atTop (fun n => S.Γ (u' n) (v' n)) := by
  have ha := (S.energy.mem_closureDom_iff a).mpr ⟨u, hu⟩
  have hb := (S.energy.mem_closureDom_iff b).mpr ⟨v, hv⟩
  exact (S.closureGamma_characterization h (a := ⟨a,ha⟩) (b := ⟨b,hb⟩) hu hv).limUnder_eq.trans
    (S.closureGamma_characterization h (a := ⟨a,ha⟩) (b := ⟨b,hb⟩) hu' hv').limUnder_eq.symm

theorem closureGamma_symm (h : S.energy.IsClosable) (a b : S.energy.closureDom) :
    S.closureGamma h a b = S.closureGamma h b a := by
  obtain ⟨u, hu⟩ := (S.energy.mem_closureDom_iff a).mp a.property
  obtain ⟨v, hv⟩ := (S.energy.mem_closureDom_iff b).mp b.property
  apply tendsto_nhds_unique (S.closureGamma_characterization h hu hv)
  simpa only [S.Γ_symm] using S.closureGamma_characterization h hv hu

theorem closureGamma_nonneg (h : S.energy.IsClosable) (a : S.energy.closureDom) :
    0 ≤ᵐ[μ] ⇑(S.closureGamma h a a) := by
  obtain ⟨u, hu⟩ := (S.energy.mem_closureDom_iff a).mp a.property
  exact (Lp.coeFn_nonneg _).mpr (ge_of_tendsto' (S.closureGamma_characterization h hu hu)
    fun n => (Lp.coeFn_nonneg _).mp (S.Γ_nonneg (u n)))

@[simp] theorem closureGamma_extends (h : S.energy.IsClosable) (u v : S.dom) :
    S.closureGamma h (S.energy.inclusion u) (S.energy.inclusion v) = S.Γ u v := by
  change S.completedGamma (S.energy.closureLift h _) (S.energy.closureLift h _) = _
  simp

/-- continuity of the L¹ integral identifies the closed energy. -/
theorem closureGamma_energy (h : S.energy.IsClosable) (a b : S.energy.closureDom) :
    (1/2:ℝ) * ∫ ω, S.closureGamma h a b ω ∂μ = (S.energy.closure h).E a b := by
  obtain ⟨u, hu⟩ := (S.energy.mem_closureDom_iff a).mp a.property
  obtain ⟨v, hv⟩ := (S.energy.mem_closureDom_iff b).mp b.property
  have hi := ((continuous_integral (μ := μ) (G := ℝ)).tendsto _).comp
    (S.closureGamma_characterization h hu hv)
  exact tendsto_nhds_unique (hi.const_mul (1/2:ℝ))
    (S.energy.closure_characterization h hu hv a.property b.property)

end ErrorCalculus.ErrorData
