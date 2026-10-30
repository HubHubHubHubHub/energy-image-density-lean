import ErrorCalculus.Dirichlet.TangentExtension
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Integral Rpow Exponent

## Main results
Differentiation in the exponent and joint continuity on confined L² data.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integrable_comp_confined {F : ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn F (Icc a b)) (v : Lp ℝ 2 μ)
    (hv : ∀ᵐ ω ∂μ, v ω ∈ Icc a b)
    (hm : AEStronglyMeasurable (fun ω => F (v ω)) μ) :
    Integrable (fun ω => F (v ω)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).bddAbove_image hF.norm
  exact (integrable_const C).mono' hm (hv.mono fun ω hω => hC ⟨v ω, hω, rfl⟩)

theorem integrable_rpow_confined {ε M : ℝ} (hε : 0 < ε) (v : Lp ℝ 2 μ)
    (hv : ∀ᵐ ω ∂μ, v ω ∈ Icc ε M) (r : ℝ) :
    Integrable (fun ω => (v ω)^r) μ :=
  integrable_comp_confined
    (fun x hx => (Real.continuousAt_rpow_const x r
      (Or.inl (ne_of_gt (hε.trans_le hx.1)))).continuousWithinAt) v hv
    ((Lp.aestronglyMeasurable v).aemeasurable.pow_const r).aestronglyMeasurable

theorem integrable_rpow_log_confined {ε M : ℝ} (hε : 0 < ε) (v : Lp ℝ 2 μ)
    (hv : ∀ᵐ ω ∂μ, v ω ∈ Icc ε M) (r : ℝ) :
    Integrable (fun ω => (v ω)^r * Real.log (v ω)) μ :=
  integrable_comp_confined (fun x hx =>
    ((Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt (hε.trans_le hx.1)))).mul
      (Real.continuousAt_log (ne_of_gt (hε.trans_le hx.1)))).continuousWithinAt) v hv
    (((Lp.aestronglyMeasurable v).aemeasurable.pow_const r).mul
      (Lp.aestronglyMeasurable v).aemeasurable.log).aestronglyMeasurable

theorem contDiffOn_rpow_pair {ε M a b : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ 1 (fun z : ℝ × ℝ => z.1^z.2) (Icc ε M ×ˢ Icc a b) :=
  fun z hz => (Real.contDiffAt_rpow_of_ne z (ne_of_gt (hε.trans_le hz.1.1))).contDiffWithinAt

theorem contDiffOn_rpow_log_pair {ε M a b : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ 1 (fun z : ℝ × ℝ => z.1^z.2 * Real.log z.1)
      (Icc ε M ×ˢ Icc a b) := fun z hz =>
  ((Real.contDiffAt_rpow_of_ne z (ne_of_gt (hε.trans_le hz.1.1))).mul
    (contDiffAt_fst.log (ne_of_gt (hε.trans_le hz.1.1)))).contDiffWithinAt

theorem hasDerivAt_integral_rpow_exponent {ε M : ℝ} (hε : 0 < ε)
    (v : Lp ℝ 2 μ) (hv : ∀ᵐ ω ∂μ, v ω ∈ Icc ε M) (r : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ ω, (v ω)^s ∂μ)
      (∫ ω, (v ω)^r * Real.log (v ω) ∂μ) r := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc ε M ×ˢ Icc (r-1) (r+1))).bddAbove_image
      (contDiffOn_rpow_log_pair hε).continuousOn.norm
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Icc_mem_nhds (by linarith : r-1 < r) (by linarith : r < r+1))
    (Eventually.of_forall fun s =>
      ((Lp.aestronglyMeasurable v).aemeasurable.pow_const s).aestronglyMeasurable)
    (integrable_rpow_confined hε v hv r)
    (integrable_rpow_log_confined hε v hv r).aestronglyMeasurable
    (hv.mono fun ω hω s hs => hC ⟨(v ω,s), ⟨hω,hs⟩, rfl⟩)
    (integrable_const C) ?_).2
  filter_upwards [hv] with ω hω s hs
  have hp := hε.trans_le hω.1
  simp_rw [Real.rpow_def_of_pos hp]
  simpa only [mul_one, id_eq] using! (((hasDerivAt_id s).const_mul (Real.log (v ω))).exp)

/-- The L¹ distance is bounded by the L² distance on a probability space. -/
theorem integral_abs_le_norm_L2 (v : Lp ℝ 2 μ) : (∫ ω, |v ω| ∂μ) ≤ ‖v‖ := by
  let w := ErrorStructure.absLp v
  have he : (∫ ω, |v ω| ∂μ) = inner ℝ (Lp.const 2 μ (1 : ℝ)) w := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ)),
      ErrorStructure.coeFn_absLp v] with ω hc hw
    simpa only [RCLike.inner_apply, conj_trivial, hc, Function.const_apply, mul_one] using hw.symm
  have hn : ‖w‖ = ‖v‖ := by
    change (eLpNorm w 2 μ).toReal = (eLpNorm v 2 μ).toReal
    have ha : (w : Ω → ℝ) =ᵐ[μ] fun ω => |v ω| := ErrorStructure.coeFn_absLp v
    rw [eLpNorm_congr_ae ha]
    simp only [← Real.norm_eq_abs, eLpNorm_norm]
  have hc : ‖Lp.const 2 μ (1 : ℝ)‖ = 1 := by
    convert! Lp.norm_const (μ := μ) (p := 2) (c := (1 : ℝ)) (by norm_num) using 1; simp
  rw [he]
  calc
    _ ≤ ‖Lp.const 2 μ (1 : ℝ)‖ * ‖w‖ := real_inner_le_norm _ _
    _ = ‖v‖ := by rw [hn, hc, one_mul]

theorem integral_pair_sub_le {F : ℝ × ℝ → ℝ} {ε M a b r s : ℝ} {L : ℝ≥0}
    (hL : LipschitzOnWith L F (Icc ε M ×ˢ Icc a b))
    (v w : Lp ℝ 2 μ) (hv : ∀ᵐ ω ∂μ, v ω ∈ Icc ε M)
    (hw : ∀ᵐ ω ∂μ, w ω ∈ Icc ε M) (hr : r ∈ Icc a b) (hs : s ∈ Icc a b)
    (hi : Integrable (fun ω => F (v ω,r)) μ) (hj : Integrable (fun ω => F (w ω,s)) μ) :
    |(∫ ω, F (v ω,r) ∂μ) - ∫ ω, F (w ω,s) ∂μ| ≤
      (L : ℝ) * (‖v-w‖ + |r-s|) := by
  rw [← integral_sub hi hj, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ ω, (L : ℝ) * (|(v-w) ω| + |r-s|) ∂μ := by
      apply norm_integral_le_of_norm_le
        ((((Lp.memLp (v-w)).integrable (by norm_num)).abs.add (integrable_const _)).const_mul _)
      filter_upwards [hv, hw, Lp.coeFn_sub v w] with ω hv hw he
      have h := hL.dist_le_mul (v ω,r) ⟨hv,hr⟩ (w ω,s) ⟨hw,hs⟩
      change ‖F (v ω, r) - F (w ω, s)‖ ≤ (L : ℝ) * (|(v-w) ω| + |r-s|)
      simp only [Prod.dist_eq, Real.dist_eq] at h
      rw [he, Pi.sub_apply, Real.norm_eq_abs]
      exact h.trans (mul_le_mul_of_nonneg_left
        (max_le (le_add_of_nonneg_right (abs_nonneg _))
          (le_add_of_nonneg_left (abs_nonneg _))) L.coe_nonneg)
    _ = (L : ℝ) * ((∫ ω, |(v-w) ω| ∂μ) + |r-s|) := by
      rw [integral_const_mul, integral_add
        (((Lp.memLp (v-w)).integrable (by norm_num)).abs) (integrable_const _)]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by linarith [integral_abs_le_norm_L2 (v-w)]) L.coe_nonneg

theorem integral_rpow_log_sub_le {ε M a b : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ≥0, ∀ (v w : Lp ℝ 2 μ),
      (∀ᵐ ω ∂μ, v ω ∈ Icc ε M) → (∀ᵐ ω ∂μ, w ω ∈ Icc ε M) →
      ∀ r ∈ Icc a b, ∀ s ∈ Icc a b,
        |(∫ ω, (v ω)^r * Real.log (v ω) ∂μ) -
          ∫ ω, (w ω)^s * Real.log (w ω) ∂μ| ≤ (L : ℝ)*(‖v-w‖+|r-s|) := by
  obtain ⟨L,hL⟩ := (contDiffOn_rpow_log_pair (M := M) (a := a) (b := b) hε).exists_lipschitzOnWith
    (by norm_num) ((convex_Icc _ _).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)
  exact ⟨L, fun v w hv hw r hr s hs => integral_pair_sub_le hL v w hv hw hr hs
    (integrable_rpow_log_confined hε v hv r) (integrable_rpow_log_confined hε w hw s)⟩

theorem integral_rpow_sub_le {ε M a b : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ≥0, ∀ (v w : Lp ℝ 2 μ),
      (∀ᵐ ω ∂μ, v ω ∈ Icc ε M) → (∀ᵐ ω ∂μ, w ω ∈ Icc ε M) →
      ∀ r ∈ Icc a b, ∀ s ∈ Icc a b,
        |(∫ ω, (v ω)^r ∂μ) - ∫ ω, (w ω)^s ∂μ| ≤ (L : ℝ)*(‖v-w‖+|r-s|) := by
  obtain ⟨L,hL⟩ := (contDiffOn_rpow_pair (M := M) (a := a) (b := b) hε).exists_lipschitzOnWith
    (by norm_num) ((convex_Icc _ _).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)
  exact ⟨L, fun v w hv hw r hr s hs => integral_pair_sub_le hL v w hv hw hr hs
    (integrable_rpow_confined hε v hv r) (integrable_rpow_confined hε w hw s)⟩

omit [IsProbabilityMeasure μ] in
/-- A local uniform bound gives continuity for arbitrary filters, not only sequences. -/
theorem tendsto_confined_pair_of_bound {F : Lp ℝ 2 μ → ℝ → ℝ} {ε M : ℝ}
    (hb : ∀ a b : ℝ, ∃ L : ℝ≥0, ∀ v w : Lp ℝ 2 μ,
      (∀ᵐ ω ∂μ, v ω ∈ Icc ε M) → (∀ᵐ ω ∂μ, w ω ∈ Icc ε M) →
      ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, |F v r-F w s| ≤ (L : ℝ)*(‖v-w‖+|r-s|))
    {ι : Type*} {l : Filter ι} {v : ι → Lp ℝ 2 μ} {r : ι → ℝ}
    {w : Lp ℝ 2 μ} {s : ℝ} (hv : Tendsto v l (𝓝 w)) (hr : Tendsto r l (𝓝 s))
    (hvc : ∀ᶠ i in l, ∀ᵐ ω ∂μ, v i ω ∈ Icc ε M)
    (hw : ∀ᵐ ω ∂μ, w ω ∈ Icc ε M) : Tendsto (fun i => F (v i) (r i)) l (𝓝 (F w s)) := by
  obtain ⟨L,hL⟩ := hb (s-1) (s+1)
  have he : ∀ᶠ i in l, r i ∈ Icc (s-1) (s+1) :=
    hr.eventually (Icc_mem_nhds (by linarith) (by linarith))
  have ht : Tendsto (fun i => (L : ℝ)*(‖v i-w‖+|r i-s|)) l (𝓝 0) := by
    simpa using ((hv.sub_const w).norm.add
      (hr.sub_const s).abs).const_mul (L : ℝ)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) _ ht
  filter_upwards [hvc,he] with i hi hi'
  exact hL (v i) w hi hw (r i) hi' s ⟨by linarith, by linarith⟩

theorem tendsto_integral_rpow_confined {ε M : ℝ} (hε : 0 < ε)
    {ι : Type*} {l : Filter ι} {v : ι → Lp ℝ 2 μ} {r : ι → ℝ}
    {w : Lp ℝ 2 μ} {s : ℝ} (hv : Tendsto v l (𝓝 w)) (hr : Tendsto r l (𝓝 s))
    (hvc : ∀ᶠ i in l, ∀ᵐ ω ∂μ, v i ω ∈ Icc ε M)
    (hw : ∀ᵐ ω ∂μ, w ω ∈ Icc ε M) :
    Tendsto (fun i => ∫ ω, (v i ω)^(r i) ∂μ) l (𝓝 (∫ ω, (w ω)^s ∂μ)) :=
  tendsto_confined_pair_of_bound (fun _ _ => integral_rpow_sub_le hε) hv hr hvc hw

theorem tendsto_integral_rpow_log_confined {ε M : ℝ} (hε : 0 < ε)
    {ι : Type*} {l : Filter ι} {v : ι → Lp ℝ 2 μ} {r : ι → ℝ}
    {w : Lp ℝ 2 μ} {s : ℝ} (hv : Tendsto v l (𝓝 w)) (hr : Tendsto r l (𝓝 s))
    (hvc : ∀ᶠ i in l, ∀ᵐ ω ∂μ, v i ω ∈ Icc ε M)
    (hw : ∀ᵐ ω ∂μ, w ω ∈ Icc ε M) :
    Tendsto (fun i => ∫ ω, (v i ω)^(r i)*Real.log (v i ω) ∂μ) l
      (𝓝 (∫ ω, (w ω)^s*Real.log (w ω) ∂μ)) :=
  tendsto_confined_pair_of_bound (fun _ _ => integral_rpow_log_sub_le hε) hv hr hvc hw

theorem continuous_integral_rpow_confined {ε M : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun z : Lp ℝ 2 μ × ℝ => ∫ ω, (z.1 ω)^z.2 ∂μ)
      {z | ∀ᵐ ω ∂μ, z.1 ω ∈ Icc ε M} := by
  intro z hz
  exact tendsto_integral_rpow_confined hε continuous_fst.continuousWithinAt
    continuous_snd.continuousWithinAt self_mem_nhdsWithin hz

theorem integral_rpow_pos {ε M : ℝ} (hε : 0 < ε) (v : Lp ℝ 2 μ)
    (hv : ∀ᵐ ω ∂μ, v ω ∈ Icc ε M) (r : ℝ) : 0 < ∫ ω, (v ω)^r ∂μ := by
  have hp : ∀ᵐ ω ∂μ, 0 < (v ω)^r := hv.mono fun ω hω =>
    Real.rpow_pos_of_pos (hε.trans_le hω.1) r
  rw [integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h => h.le)
    (integrable_rpow_confined hε v hv r)]
  have he : μ (Function.support (fun ω => (v ω)^r)) = μ univ := by
    apply measure_congr
    filter_upwards [hp] with ω hω
    apply propext
    change ((v ω)^r ≠ 0) ↔ True
    exact iff_true_intro (ne_of_gt hω)
  rw [he, measure_univ]
  norm_num

theorem integral_rpow_le {ε M r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r)
    (v : Lp ℝ 2 μ) (hv : ∀ᵐ ω ∂μ, v ω ∈ Icc ε M) :
    (∫ ω, (v ω)^r ∂μ) ≤ M^r := by
  calc
    _ ≤ ∫ _ : Ω, M^r ∂μ := integral_mono_ae (integrable_rpow_confined hε v hv r)
      (integrable_const _) (hv.mono fun ω hω => Real.rpow_le_rpow (hε.le.trans hω.1) hω.2 hr)
    _ = _ := by simp

end ErrorCalculus
