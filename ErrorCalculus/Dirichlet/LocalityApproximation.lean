import ErrorCalculus.Dirichlet.ContractionMollify

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- Apply the scalar calculus to F-G, at the same domain element. -/
theorem gamma_lipschitzComp_sub_functions {F G : ℝ → ℝ} {L K : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hL : LipschitzWith L F) (hK : LipschitzWith K G) (u : S.dom) :
    S.Γ (S.lipschitzComp hL u - S.lipschitzComp hK u)
      (S.lipschitzComp hL u - S.lipschitzComp hK u) =ᵐ[μ] fun ω =>
      (deriv F ((u : Lp ℝ 2 μ) ω) - deriv G ((u : Lp ℝ 2 μ) ω))^2 * S.Γ u u ω := by
  have hc : ((S.lipschitzComp hL u - S.lipschitzComp hK u : S.dom) : Lp ℝ 2 μ) =ᵐ[μ]
      fun ω => (F-G) ((u : Lp ℝ 2 μ) ω) := by
    filter_upwards [Lp.coeFn_sub (S.lipschitzComp hL u : Lp ℝ 2 μ)
      (S.lipschitzComp hK u : Lp ℝ 2 μ), S.coeFn_lipschitzComp hL u,
      S.coeFn_lipschitzComp hK u] with ω hs hf hg
    simp only [Submodule.coe_sub, hs, Pi.sub_apply, hf, hg]
  have hd x : deriv (fun x => F x-G x) x = deriv F x - deriv G x :=
    ((hF.differentiable (by norm_num) x).hasDerivAt.sub
      (hG.differentiable (by norm_num) x).hasDerivAt).deriv
  simpa only [hd] using S.chain_diagonal (hF.sub hG) (hL.sub hK) u _ hc

/-- Bounded derivative convergence on the support of Γ makes smooth
compositions Cauchy in the form norm. The two indices tend jointly to infinity. -/
theorem cauchySeq_comp_of_deriv_tendsto {F : ℕ → ℝ → ℝ} {L : ℝ≥0}
    (hF : ∀ n, ContDiff ℝ 1 (F n)) (hL : ∀ n, LipschitzWith L (F n))
    (u : S.dom) {v : Lp ℝ 2 μ}
    (hv : Tendsto (fun n => (S.lipschitzComp (hL n) u : Lp ℝ 2 μ)) atTop (𝓝 v))
    {d : Ω → ℝ} (hd : ∀ᵐ ω ∂μ, S.Γ u u ω = 0 ∨
      Tendsto (fun n => deriv (F n) ((u : Lp ℝ 2 μ) ω)) atTop (𝓝 (d ω))) :
    CauchySeq (fun n => S.energy.formToDomain.symm (S.lipschitzComp (hL n) u)) := by
  have hp1 : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    simpa only [prod_atTop_atTop_eq] using
      (tendsto_fst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) (atTop ×ˢ atTop) atTop)
  have hp2 : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    simpa only [prod_atTop_atTop_eq] using
      (tendsto_snd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) (atTop ×ˢ atTop) atTop)
  let q n := S.lipschitzComp (hL n) u
  have hm n : Continuous (deriv (F n)) := (hF n).continuous_deriv (by norm_num)
  have hb n x : |deriv (F n) x| ≤ L := norm_deriv_le_of_lipschitz (𝕜 := ℝ) (hL n)
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := (atTop : Filter (ℕ × ℕ)))
    (F := fun p ω => (deriv (F p.1) ((u : Lp ℝ 2 μ) ω) -
      deriv (F p.2) ((u : Lp ℝ 2 μ) ω))^2 * S.Γ u u ω)
    (f := fun _ => (0 : ℝ)) (fun ω => 4*(L : ℝ)^2 * ‖S.Γ u u ω‖)
    (Eventually.of_forall fun p => (((hm p.1).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable _)).sub ((hm p.2).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable _))).pow 2 |>.mul (Lp.aestronglyMeasurable _))
    (Eventually.of_forall fun p => ae_of_all _ fun ω => ?_)
    ((L1.integrable_coeFn _).norm.const_mul _) ?_
  · have he : Tendsto (fun p : ℕ × ℕ => S.energy.E (q p.1-q p.2) (q p.1-q p.2))
        atTop (𝓝 0) := by
      have heq (p : ℕ × ℕ) : S.energy.E (q p.1-q p.2) (q p.1-q p.2) =
          (1/2:ℝ) * ∫ ω, (deriv (F p.1) ((u : Lp ℝ 2 μ) ω) -
            deriv (F p.2) ((u : Lp ℝ 2 μ) ω))^2 * S.Γ u u ω ∂μ := by
        rw [ErrorData.energy_apply, integral_congr_ae
          (S.gamma_lipschitzComp_sub_functions (hF _) (hF _) (hL _) (hL _) u)]
      simp_rw [heq]
      simpa using ht.const_mul (1/2:ℝ)
    have ha := ((hv.comp hp1).sub (hv.comp hp2)).norm.pow 2
    have hn := (ha.add he).sqrt
    apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, Real.sqrt_zero] at hn
    change Tendsto (fun p : ℕ × ℕ => Real.sqrt
      (‖((q p.1-q p.2 : S.dom) : Lp ℝ 2 μ)‖^2 +
        S.energy.E (q p.1-q p.2) (q p.1-q p.2))) atTop (𝓝 0) at hn
    simp_rw [← S.energy.formNorm_sq, QuadForm.formNorm, Real.sqrt_sq (norm_nonneg _)] at hn
    simpa only [dist_eq_norm, ← map_sub] using hn
  · rw [norm_mul, Real.norm_eq_abs, abs_pow, sq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have h := (abs_sub (deriv (F p.1) ((u : Lp ℝ 2 μ) ω))
      (deriv (F p.2) ((u : Lp ℝ 2 μ) ω))).trans
      (add_le_add (hb p.1 _) (hb p.2 _))
    nlinarith [sq_abs (deriv (F p.1) ((u : Lp ℝ 2 μ) ω) -
      deriv (F p.2) ((u : Lp ℝ 2 μ) ω)), abs_nonneg (deriv (F p.1)
        ((u : Lp ℝ 2 μ) ω) - deriv (F p.2) ((u : Lp ℝ 2 μ) ω))]
  · filter_upwards [hd] with ω hω
    rcases hω with hz | ht
    · simp only [hz, mul_zero]; exact tendsto_const_nhds
    · simpa using (((ht.comp hp1).sub
        (ht.comp hp2)).pow 2).mul_const (S.Γ u u ω)

/-- Closedness identifies a Cauchy form limit by its ambient L² limit. -/
theorem tendsto_formSpace_of_cauchySeq {q : ℕ → S.dom} {v : S.dom}
    (hc : CauchySeq (fun n => S.energy.formToDomain.symm (q n)))
    (hv : Tendsto (fun n => (q n : Lp ℝ 2 μ)) atTop (𝓝 (v : Lp ℝ 2 μ))) :
    Tendsto (fun n => S.energy.formToDomain.symm (q n)) atTop
      (𝓝 (S.energy.formToDomain.symm v)) := by
  letI := S.energy_closed.completeSpace_formSpace
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hc
  have he : S.energy.formInclusion w = (v : Lp ℝ 2 μ) :=
    tendsto_nhds_unique (S.energy.formInclusion.continuous.tendsto w |>.comp hw) hv
  have hwv : w = S.energy.formToDomain.symm v := by
    apply S.energy.formToDomain.injective
    exact Subtype.ext he
  simpa only [hwv] using hw

end ErrorCalculus.ErrorStructure
