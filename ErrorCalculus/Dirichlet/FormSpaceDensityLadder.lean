import ErrorCalculus.Dirichlet.RightDerivativesZero
import ErrorCalculus.Dirichlet.BoundedDenseStrong
import ErrorCalculus.Dirichlet.LatticeGamma

/-!
# Form Space Density Ladder

## Main results
Form approximation, confined power continuity, and closure of logarithmic Sobolev.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

def betaResolventGenerator (β : ℝ) (hβ : 0 < β) (u : Lp ℝ 2 μ) : S.generatorDom :=
  ⟨β • S.resolvent β hβ u,
    S.energy.betaResolvent_mem_generatorDom S.energy_closed S.dense β hβ u⟩

theorem energy_betaResolvent_le (β : ℝ) (hβ : 0 < β) (u : S.dom) :
    S.energy.E (S.generatorForm (S.betaResolventGenerator β hβ u))
      (S.generatorForm (S.betaResolventGenerator β hβ u)) ≤ S.energy.E u u :=
  (S.energy.energy_beta_resolvent_le_approxForm S.energy_closed β hβ (u : Lp ℝ 2 μ)).trans
    (S.energy.approxForm_le_energy S.energy_closed β hβ u)

/-- Every positive sequence of resolvent parameters tending to infinity gives form convergence. -/
theorem tendsto_betaResolvent_formSpace_seq (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (ht : Tendsto b atTop atTop) (u : S.dom) :
    Tendsto (fun n => S.energy.formToDomain.symm
      (S.generatorForm (S.betaResolventGenerator (b n) (hb n) u))) atTop
      (𝓝 (S.energy.formToDomain.symm u)) :=
  S.energy_closed.tendsto_formSpace_of_energy_le (S.tendsto_betaResolvent b hb ht u)
    (fun n => S.energy_betaResolvent_le (b n) (hb n) u)

/-- Real-parameter convergence; max β 1 only supplies positivity away from infinity. -/
theorem tendsto_betaResolvent_formSpace_atTop (u : S.dom) :
    Tendsto (fun β : ℝ => S.energy.formToDomain.symm (S.generatorForm
      (S.betaResolventGenerator (max β 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) u)))
      atTop (𝓝 (S.energy.formToDomain.symm u)) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro b hb
  exact S.tendsto_betaResolvent_formSpace_seq (fun n => max (b n) 1)
    (fun _ => lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    (tendsto_atTop_mono (fun _ => le_max_left _ _) hb) u

/-- Strong form convergence for every positive resolvent parameter tending to infinity. -/
theorem tendsto_betaResolvent_formSpace {ι : Type*} {l : Filter ι} (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) (ht : Tendsto b l atTop) (u : S.dom) :
    Tendsto (fun i => S.energy.formToDomain.symm
      (S.generatorForm (S.betaResolventGenerator (b i) (hb i) u))) l
      (𝓝 (S.energy.formToDomain.symm u)) := by
  apply ((S.tendsto_betaResolvent_formSpace_atTop u).comp ht).congr'
  filter_upwards [ht (eventually_ge_atTop (1:ℝ))] with i hi
  simp only [Function.comp_def, max_eq_left (show 1 ≤ b i from hi)]

/-- A C² function on a compact interval admits a globally Lipschitz C¹ tangent extension. -/
theorem exists_lipschitzWith_tangentExtension {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x) :
    ContDiff ℝ 1 (tangentExtension F a b) ∧
      ∃ L : ℝ≥0, LipschitzWith L (tangentExtension F a b) := by
  obtain ⟨K,hK⟩ := exists_lipschitzOnWith_deriv hF
  have hc := contDiff_tangentExtension hab hK
  refine ⟨hc, ?_⟩
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).bddAbove_image hK.continuousOn.norm
  refine ⟨⟨max C 0, le_max_right _ _⟩, lipschitzWith_of_contDiff_deriv_bound hc ?_⟩
  intro x
  rw [deriv_tangentExtension hab hK]
  exact (hC ⟨max a (min x b), ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩, rfl⟩).trans
    (le_max_left _ _)

/-- Continuity on confined form elements, proved with a tangent extension, not the corners. -/
theorem continuous_powComp_formSpace {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (r : ℝ) :
    ContinuousOn (fun x : S.energy.FormSpace => S.energy.formToDomain.symm
      (S.powComp hε hεM r (S.energy.formToDomain x)))
      {x | ∀ᵐ ω ∂μ, (S.energy.formInclusion x) ω ∈ Icc ε M} := by
  obtain ⟨hc,L,hL⟩ := exists_lipschitzWith_tangentExtension hεM (rpow_contDiffAt_on hε r)
  obtain ⟨K,hK⟩ := exists_lipschitzOnWith_deriv (rpow_contDiffAt_on (b := M) hε r)
  apply (S.continuous_lipschitzComp_formSpace hc hL).continuousOn.congr
  intro x hx
  apply congrArg S.energy.formToDomain.symm
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [S.coeFn_powComp hε hεM r (S.energy.formToDomain x) hx,
    S.coeFn_lipschitzComp hL (S.energy.formToDomain x), hx] with ω hp ht hb
  rw [hp, ht]
  exact (tangentExtension_eq_on hεM
    (fun y hy => (rpow_contDiffAt_on hε r y hy).differentiableAt (by norm_num)) hK hb).symm

theorem tendsto_powComp_formSpace {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (r : ℝ)
    {u : ℕ → S.dom} {v : S.dom}
    (hu : Tendsto (fun n => S.energy.formToDomain.symm (u n)) atTop
      (𝓝 (S.energy.formToDomain.symm v)))
    (hb : ∀ n, ∀ᵐ ω ∂μ, (u n : Lp ℝ 2 μ) ω ∈ Icc ε M)
    (hv : ∀ᵐ ω ∂μ, (v : Lp ℝ 2 μ) ω ∈ Icc ε M) :
    Tendsto (fun n => S.energy.formToDomain.symm (S.powComp hε hεM r (u n))) atTop
      (𝓝 (S.energy.formToDomain.symm (S.powComp hε hεM r v))) :=
  ((S.continuous_powComp_formSpace hε hεM r) _ hv).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hu, Eventually.of_forall hb⟩)

/-- The pointwise LSI assertion includes finiteness of the entropy integral. -/
def LogSobolevAt (c : ℝ) (u : S.dom) : Prop :=
  Integrable (fun ω => ((u : Lp ℝ 2 μ) ω)^2 * Real.log (((u : Lp ℝ 2 μ) ω)^2)) μ ∧
    entropy μ (fun ω => ((u : Lp ℝ 2 μ) ω)^2) ≤ c * S.energy.E u u

theorem integrable_sq_log_sq_of_bounded (u : Lp ℝ 2 μ) (hu : AEBounded (μ := μ) u) :
    Integrable (fun ω => (u ω)^2 * Real.log ((u ω)^2)) μ := by
  obtain ⟨M,hM⟩ := hu
  have hc : Continuous (fun x : ℝ => x^2 * Real.log (x^2)) :=
    Real.continuous_mul_log.comp (continuous_id.pow 2)
  refine integrable_comp_confined (a := -M) (b := M) hc.continuousOn u ?_
    (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))
  exact hM.mono fun ω hω => abs_le.mp (show |u ω| ≤ M from hω)

omit [IsProbabilityMeasure μ] in
theorem bounded_of_confined {a b : ℝ} (u : Lp ℝ 2 μ)
    (hu : ∀ᵐ ω ∂μ, u ω ∈ Icc a b) : AEBounded (μ := μ) u :=
  ⟨max |a| |b|, hu.mono fun ω hω => by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨(neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans hω.1),
      hω.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩⟩

theorem logSobolev_closed {c : ℝ} {u : ℕ → S.dom} {v : S.dom}
    (hu : Tendsto (fun n => S.energy.formToDomain.symm (u n)) atTop
      (𝓝 (S.energy.formToDomain.symm v))) (h : ∀ n, S.LogSobolevAt c (u n)) :
    S.LogSobolevAt c v := by
  have hl2 : Tendsto (fun n => (u n : Lp ℝ 2 μ)) atTop (𝓝 (v : Lp ℝ 2 μ)) :=
    S.energy.formInclusion.continuous.tendsto _ |>.comp hu
  have he := (S.energy.continuous_energy_formSpace.tendsto
    (S.energy.formToDomain.symm v, S.energy.formToDomain.symm v)).comp (hu.prodMk_nhds hu)
  exact entropy_le_of_tendsto_L2 hl2 (fun n => (h n).1) (fun n => (h n).2) (he.const_mul c)

/-- The generator-domain inequality extends to every confined form element. -/
theorem logSobolev_confined {c : ℝ}
    (h : ∀ (ε M : ℝ) (_hε : 0 < ε) (_hεM : ε ≤ M) (u : S.generatorDom),
      (∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) → S.LogSobolevAt c (S.generatorForm u))
    {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (u : S.dom)
    (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) : S.LogSobolevAt c u := by
  apply S.logSobolev_closed (S.tendsto_betaResolvent_formSpace QuadForm.resolventParameter
    QuadForm.resolventParameter_pos QuadForm.tendsto_resolventParameter u)
  intro n
  exact h ε M hε hεM _ (S.betaResolvent_mem_Icc hεM _ _ u hu)

/-- Removing the positive lower bound uses addition of constants in the form Hilbert space. -/
theorem logSobolev_nonneg_bounded {c : ℝ}
    (h : ∀ (ε M : ℝ), 0 < ε → ε ≤ M → ∀ u : S.dom,
      (∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) → S.LogSobolevAt c u)
    {M : ℝ} (hM : 0 ≤ M) (u : S.dom)
    (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc 0 M) : S.LogSobolevAt c u := by
  let δ : ℕ → ℝ := fun n => (QuadForm.resolventParameter n)⁻¹
  have hδp (n : ℕ) : 0 < δ n := inv_pos.mpr (QuadForm.resolventParameter_pos n)
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_inv_atTop_zero.comp QuadForm.tendsto_resolventParameter
  let uₙ : ℕ → S.dom := fun n => u + δ n • S.const 1
  have ht : Tendsto (fun n => S.energy.formToDomain.symm (uₙ n)) atTop
      (𝓝 (S.energy.formToDomain.symm u)) := by
    simpa only [uₙ, map_add, map_smul, zero_smul, add_zero] using
      (tendsto_const_nhds (x := S.energy.formToDomain.symm u)).add
        (hδ.smul_const (S.energy.formToDomain.symm (S.const 1)))
  apply S.logSobolev_closed ht
  intro n
  apply h (δ n) (M + δ n) (hδp n) (by linarith)
  filter_upwards [hu, Lp.coeFn_add (u : Lp ℝ 2 μ) (δ n • (S.const 1 : Lp ℝ 2 μ)),
    Lp.coeFn_smul (δ n) (S.const 1 : Lp ℝ 2 μ),
    Lp.coeFn_const (p := 2) (μ := μ) (c := (1:ℝ))] with ω hb ha hs hc
  change (↑(u + δ n • S.const 1) : Lp ℝ 2 μ) ω ∈ Icc (δ n) (M+δ n)
  change ((u : Lp ℝ 2 μ) + δ n • (S.const 1 : Lp ℝ 2 μ)) ω ∈ _
  rw [ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul]
  change (u : Lp ℝ 2 μ) ω + δ n * Lp.const 2 μ (1:ℝ) ω ∈ _
  rw [hc]
  simp only [Function.const_apply, mul_one]
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

theorem logSobolev_bounded {c : ℝ}
    (h : ∀ (M : ℝ), 0 ≤ M → ∀ u : S.dom,
      (∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc 0 M) → S.LogSobolevAt c u)
    (u : S.dom) (hu : AEBounded (μ := μ) (u : Lp ℝ 2 μ)) : S.LogSobolevAt c u := by
  obtain ⟨M,hM⟩ := hu
  have hb : ∀ᵐ ω ∂μ, (S.absComp u : Lp ℝ 2 μ) ω ∈ Icc 0 (max M 0) := by
    filter_upwards [S.coeFn_absComp u,hM] with ω ha hb
    rw [ha]
    exact ⟨abs_nonneg _, hb.trans (le_max_left _ _)⟩
  have hh := h (max M 0) (le_max_right _ _) (S.absComp u) hb
  have he : (fun ω => ((S.absComp u : Lp ℝ 2 μ) ω)^2) =ᵐ[μ]
      fun ω => ((u : Lp ℝ 2 μ) ω)^2 := (S.coeFn_absComp u).mono fun ω hω => by
    have hh := congrArg (fun x : ℝ => x^2) hω
    change ((S.absComp u : Lp ℝ 2 μ) ω)^2 = |(u : Lp ℝ 2 μ) ω|^2 at hh
    exact hh.trans (sq_abs _)
  exact ⟨hh.1.congr (he.fun_comp (fun x : ℝ => x * Real.log x)),
    by simpa only [entropy_congr_ae he, S.energy_abs] using hh.2⟩

theorem hasLogSobolev_of_confined {c : ℝ}
    (h : ∀ (ε M : ℝ), 0 < ε → ε ≤ M → ∀ u : S.dom,
      (∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) → S.LogSobolevAt c u) :
    S.HasLogSobolev c := by
  intro u
  apply S.logSobolev_closed (S.tendsto_truncationSeq_formSpace u)
  intro n
  exact S.logSobolev_bounded (fun M hM v hv => S.logSobolev_nonneg_bounded h hM v hv)
    _ (S.bounded_truncationSeq u n)

end ErrorCalculus.ErrorStructure
