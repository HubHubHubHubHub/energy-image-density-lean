import ErrorCalculus.Dirichlet.LocalityZero

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology
open scoped NNReal Convolution
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- Identify the limiting diagonal after bounded smooth derivative approximation.
Only points carrying nonzero energy density require derivative convergence. -/
theorem gamma_comp_of_deriv_tendsto {F : ℕ → ℝ → ℝ} {L : ℝ≥0}
    (hF : ∀ n, ContDiff ℝ 1 (F n)) (hL : ∀ n, LipschitzWith L (F n))
    (u v : S.dom)
    (hv : Tendsto (fun n => (S.lipschitzComp (hL n) u : Lp ℝ 2 μ)) atTop (𝓝 (v : Lp ℝ 2 μ)))
    {d : Ω → ℝ} (hd : ∀ᵐ ω ∂μ, S.Γ u u ω = 0 ∨
      Tendsto (fun n => deriv (F n) ((u : Lp ℝ 2 μ) ω)) atTop (𝓝 (d ω))) :
    S.Γ v v =ᵐ[μ] fun ω => (d ω)^2 * S.Γ u u ω := by
  have ht := S.tendsto_formSpace_of_cauchySeq
    (S.cauchySeq_comp_of_deriv_tendsto hF hL u hv hd) hv
  have hg := (S.continuous_gamma_formSpace.tendsto
    (S.energy.formToDomain.symm v, S.energy.formToDomain.symm v)).comp (ht.prodMk_nhds ht)
  simp only [Function.comp_def, LinearEquiv.apply_symm_apply] at hg
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  have hc := ae_all_iff.mpr (fun n => S.chain_diagonal (hF n) (hL n) u _
    (S.coeFn_lipschitzComp (hL n) u))
  filter_upwards [hae, hc, hd] with ω hω hc hd
  apply tendsto_nhds_unique hω
  simp_rw [hc]
  rcases hd with hz | hd
  · simp only [hz, mul_zero]; exact tendsto_const_nhds
  · exact ((hd.comp hns.tendsto_atTop).pow 2).mul_const _

/-- The exact finite-exception C¹ hypothesis. The Lipschitz constant also bounds
the derivative everywhere, including Mathlib's convention at exceptional points. -/
structure PiecewiseC1Lipschitz (F : ℝ → ℝ) (A : Finset ℝ) (L : ℝ≥0) : Prop where
  lipschitz : LipschitzWith L F
  differentiable : DifferentiableOn ℝ F (↑A : Set ℝ)ᶜ
  deriv_continuous : ContinuousOn (deriv F) (↑A : Set ℝ)ᶜ

/-- derivative convolution converges at every continuity point of F′. -/
theorem tendsto_deriv_mollifyLipschitz {F : ℝ → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L F) {x : ℝ} (hx : ContinuousAt (deriv F) x) :
    Tendsto (fun n => deriv (mollifyLipschitz F n) x) atTop (𝓝 (deriv F x)) := by
  simp only [mollifyLipschitz, deriv_lipschitzMollify hL]
  exact ContDiffBump.convolution_tendsto_right (φ := lipschitzBump) (μ := volume)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    (Eventually.of_forall fun _ => (measurable_deriv F).aestronglyMeasurable)
    (hx.tendsto.comp tendsto_snd) tendsto_const_nhds

/-- Derivative convergence off the finite exceptional set; locality handles its preimage. -/
theorem ae_deriv_mollify_piecewise {F : ℝ → ℝ} {A : Finset ℝ} {L : ℝ≥0}
    (hF : PiecewiseC1Lipschitz F A L) (u : S.dom) :
    ∀ᵐ ω ∂μ, S.Γ u u ω = 0 ∨ Tendsto
      (fun n => deriv (mollifyLipschitz F n) ((u : Lp ℝ 2 μ) ω)) atTop
      (𝓝 (deriv F ((u : Lp ℝ 2 μ) ω))) := by
  filter_upwards [S.gamma_eq_zero_on_countable u A.countable_toSet] with ω hω
  by_cases hx : (u : Lp ℝ 2 μ) ω ∈ (A : Set ℝ)
  · exact Or.inl (hω hx)
  · apply Or.inr
    apply tendsto_deriv_mollifyLipschitz hF.lipschitz
    exact (hF.deriv_continuous _ hx).continuousAt
      (A.finite_toSet.isClosed.isOpen_compl.mem_nhds hx)

/-- AB.2(c): the regularizations converge strongly for the form norm. -/
theorem tendsto_mollify_piecewise_formSpace {F : ℝ → ℝ} {A : Finset ℝ} {L : ℝ≥0}
    (hF : PiecewiseC1Lipschitz F A L) (u : S.dom) :
    Tendsto (fun n => S.energy.formToDomain.symm
      (S.lipschitzComp (mollifyLipschitz_lipschitz hF.lipschitz n) u)) atTop
      (𝓝 (S.energy.formToDomain.symm (S.lipschitzComp hF.lipschitz u))) :=
  S.tendsto_formSpace_of_cauchySeq
    (S.cauchySeq_comp_of_deriv_tendsto
      (fun n => (mollifyLipschitz_contDiff hF.lipschitz n).of_le (by simp))
      (mollifyLipschitz_lipschitz hF.lipschitz) u
      (S.tendsto_lipschitzComp_mollify_L2 hF.lipschitz u)
      (S.ae_deriv_mollify_piecewise hF u))
    (S.tendsto_lipschitzComp_mollify_L2 hF.lipschitz u)

/-- AB.2(a): chain rule for Lipschitz functions C¹ off a finite set. -/
theorem gamma_lipschitzComp_piecewise {F : ℝ → ℝ} {A : Finset ℝ} {L : ℝ≥0}
    (hF : PiecewiseC1Lipschitz F A L) (u : S.dom) :
    S.Γ (S.lipschitzComp hF.lipschitz u) (S.lipschitzComp hF.lipschitz u) =ᵐ[μ]
      fun ω => (deriv F ((u : Lp ℝ 2 μ) ω))^2 * S.Γ u u ω :=
  S.gamma_comp_of_deriv_tendsto
    (fun n => (mollifyLipschitz_contDiff hF.lipschitz n).of_le (by simp))
    (mollifyLipschitz_lipschitz hF.lipschitz) u _
    (S.tendsto_lipschitzComp_mollify_L2 hF.lipschitz u)
    (S.ae_deriv_mollify_piecewise hF u)

/-- Values chosen for the derivative on the exceptional set have no effect. -/
theorem gamma_lipschitzComp_piecewise_of_eqOn {F d : ℝ → ℝ} {A : Finset ℝ} {L : ℝ≥0}
    (hF : PiecewiseC1Lipschitz F A L) (hd : Set.EqOn d (deriv F) (↑A : Set ℝ)ᶜ)
    (u : S.dom) : S.Γ (S.lipschitzComp hF.lipschitz u) (S.lipschitzComp hF.lipschitz u) =ᵐ[μ]
      fun ω => (d ((u : Lp ℝ 2 μ) ω))^2 * S.Γ u u ω := by
  filter_upwards [S.gamma_lipschitzComp_piecewise hF u,
    S.gamma_eq_zero_on_countable u A.countable_toSet] with ω he hz
  rw [he]
  by_cases hx : (u : Lp ℝ 2 μ) ω ∈ (A : Set ℝ)
  · simp only [hz hx, mul_zero]
  · rw [hd hx]

end ErrorCalculus.ErrorStructure
