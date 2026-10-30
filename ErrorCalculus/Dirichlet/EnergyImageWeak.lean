import ErrorCalculus.Dirichlet.PiecewiseChain
import ErrorCalculus.Dirichlet.FormConvergence

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- The mixed C¹ rule, with the same argument in the second slot. -/
theorem gamma_lipschitzComp_mixed {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) (u : S.dom) :
    S.Γ (S.lipschitzComp hL u) u =ᵐ[μ]
      fun ω => deriv F ((u : Lp ℝ 2 μ) ω) * S.Γ u u ω :=
  S.gamma_lipschitzComp hF hL u u

theorem two_energy_mixed_eq_integral {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) (u : S.dom) :
    2 * S.energy.E (S.lipschitzComp hL u) u =
      ∫ ω, deriv F ((u : Lp ℝ 2 μ) ω) * S.Γ u u ω ∂μ := by
  rw [ErrorData.energy_apply, integral_congr_ae (S.gamma_lipschitzComp_mixed hF hL u)]
  ring

/-- Ambient convergence and bounded energy imply weak convergence in the form space.
No separability and no energy convergence are assumed. -/
theorem weak_tendsto_formSpace_of_tendsto_L2_of_energy_le
    {q : ℕ → S.dom} {v : S.dom} {C : ℝ}
    (ht : Tendsto (fun n => (q n : Lp ℝ 2 μ)) atTop (𝓝 (v : Lp ℝ 2 μ)))
    (he : ∀ n, S.energy.E (q n) (q n) ≤ C) :
    ∀ w : S.energy.FormSpace, Tendsto
      (fun n => inner ℝ (S.energy.formToDomain.symm (q n)) w) atTop
      (𝓝 (inner ℝ (S.energy.formToDomain.symm v) w)) := by
  letI := S.energy_closed.completeSpace_formSpace
  have hC : 0 ≤ C := (S.energy.nonneg (q 0)).trans (he 0)
  have hn := (ht.norm.pow 2).eventually
    (gt_mem_nhds (show ‖(v : Lp ℝ 2 μ)‖^2 < ‖(v : Lp ℝ 2 μ)‖^2 + 1 by linarith))
  have hb : ∀ᶠ n in atTop, ‖S.energy.formToDomain.symm (q n)‖ ≤
      Real.sqrt (‖(v : Lp ℝ 2 μ)‖^2 + 1 + C) := by
    filter_upwards [hn] with n hn
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    rw [S.energy.formSpace_norm_sq]
    change ‖(q n : Lp ℝ 2 μ)‖^2 + S.energy.E (q n) (q n) ≤ _
    linarith [he n]
  apply weak_tendsto_of_bounded_of_clusterPt_unique hb
  intro A _ z hz
  have hh := QuadForm.formInclusion_eq_of_weak_cluster hz inf_le_left ht
  apply S.energy.formToDomain.injective
  exact Subtype.ext hh

/-- A mixed energy is a continuous linear functional on the form Hilbert space. -/
theorem tendsto_energy_mixed_of_weak {q : ℕ → S.dom} {v : S.dom}
    (hw : ∀ w : S.energy.FormSpace, Tendsto
      (fun n => inner ℝ (S.energy.formToDomain.symm (q n)) w) atTop
      (𝓝 (inner ℝ (S.energy.formToDomain.symm v) w))) (u : S.dom) :
    Tendsto (fun n => S.energy.E (q n) u) atTop (𝓝 (S.energy.E v u)) := by
  letI := S.energy_closed.completeSpace_formSpace
  let f : S.energy.FormSpace →L[ℝ] ℝ :=
    (InnerProductSpace.toDualMap ℝ S.energy.EnergyHilbert (S.energy.j u)).comp
      S.energy.formEnergy
  have ht := hw ((InnerProductSpace.toDual ℝ S.energy.FormSpace).symm f)
  have hh (z : S.dom) : inner ℝ (S.energy.formToDomain.symm z)
      ((InnerProductSpace.toDual ℝ S.energy.FormSpace).symm f) = S.energy.E z u := by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    change inner ℝ (S.energy.j u) (S.energy.j z) = _
    rw [S.energy.inner_j, S.energy.symm]
  simpa only [hh] using ht

theorem tendsto_energy_mixed_of_tendsto_L2_of_energy_le
    {q : ℕ → S.dom} {v : S.dom} {C : ℝ}
    (ht : Tendsto (fun n => (q n : Lp ℝ 2 μ)) atTop (𝓝 (v : Lp ℝ 2 μ)))
    (he : ∀ n, S.energy.E (q n) (q n) ≤ C) (u : S.dom) :
    Tendsto (fun n => S.energy.E (q n) u) atTop (𝓝 (S.energy.E v u)) :=
  S.tendsto_energy_mixed_of_weak
    (S.weak_tendsto_formSpace_of_tendsto_L2_of_energy_le ht he) u

end ErrorCalculus.ErrorStructure
