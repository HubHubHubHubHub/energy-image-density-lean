import ErrorCalculus.Dirichlet.TangentExtension
import ErrorCalculus.Dirichlet.StroockVaropoulos
import ErrorCalculus.Dirichlet.Entropy

/-!
# Semigroup Dissipation

## Main results
Fixed-power dissipation and the de Bruijn identity.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

theorem hasDerivAt_integral_pow_semigroup {ε M q : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hq : 1 < q) (u : S.generatorDom)
    (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ ω, (S.semigroup s u ω)^q ∂μ)
      (-(4*(q-1)/q) * S.energy.E
        (S.powComp hε hεM (q/2) (S.semigroupFormDom ht.le u))
        (S.powComp hε hεM (q/2) (S.semigroupFormDom ht.le u))) t := by
  have hd := S.hasDerivAt_integral_comp_semigroup_of_Icc hεM (rpow_contDiffAt_on hε q) u hu ht
  have hg := S.semigroup_mem_Icc ht.le u hu
  have hs := S.stroock_varopoulos hε hεM hq (S.semigroupFormDom ht.le u)
    (S.semigroup_mem_generatorDom ht.le u) hg
  have he : (∫ ω, deriv (fun x : ℝ => x^q) (S.semigroup t u ω) *
      S.generator (S.semigroupGeneratorDom ht.le u) ω ∂μ) =
      -q * ∫ ω, (-S.generator (S.semigroupGeneratorDom ht.le u) ω) *
        (S.semigroup t u ω)^(q-1) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hg] with ω hω
    rw [(Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hε.trans_le hω.1)))).deriv]
    ring
  change (∫ ω, (-S.generator (S.semigroupGeneratorDom ht.le u) ω) *
    (S.semigroup t u ω)^(q-1) ∂μ) = _ at hs
  rw [he, hs] at hd
  convert hd using 1
  have hq0 : q ≠ 0 := by linarith
  field_simp

theorem antitone_integral_pow_semigroup {ε M q : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hq : 1 < q) (u : S.generatorDom)
    (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) :
    AntitoneOn (fun s => ∫ ω, (S.semigroup s u ω)^q ∂μ) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (S.continuous_integral_comp_semigroup_of_Icc hεM (rpow_contDiffAt_on hε q) u hu)
  · intro t ht
    exact (S.hasDerivAt_integral_pow_semigroup hε hεM hq u hu
      (by simpa only [interior_Ici, mem_Ioi] using ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(S.hasDerivAt_integral_pow_semigroup hε hεM hq u hu
      (by simpa only [interior_Ici, mem_Ioi] using ht)).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (mul_nonneg (by norm_num)
      (sub_nonneg.mpr hq.le)) (zero_le_one.trans hq.le)))
      (S.energy.nonneg _)

def clippedLog (ε M x : ℝ) : ℝ := Real.log (max ε (min x M))

theorem exists_lipschitzWith_clippedLog {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) :
    ∃ L : ℝ≥0, LipschitzWith L (clippedLog ε M) := by
  have hc : ContDiffOn ℝ 1 Real.log (Icc ε M) := fun x hx =>
    (Real.contDiffAt_log.mpr (ne_of_gt (hε.trans_le hx.1))).contDiffWithinAt
  obtain ⟨L, hL⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  exact ⟨L, lipschitzWith_clipped hεM hL⟩

def logComp {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (v : S.dom) : S.dom :=
  S.lipschitzComp (exists_lipschitzWith_clippedLog hε hεM).choose_spec v

theorem coeFn_logComp {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (v : S.dom)
    (hv : ∀ᵐ ω ∂μ, (v : Lp ℝ 2 μ) ω ∈ Icc ε M) :
    (S.logComp hε hεM v : Lp ℝ 2 μ) =ᵐ[μ] fun ω => Real.log ((v : Lp ℝ 2 μ) ω) := by
  filter_upwards [S.coeFn_lipschitzComp (exists_lipschitzWith_clippedLog hε hεM).choose_spec v,
    hv] with ω hc hω
  simp only [logComp, hc, clippedLog, min_eq_left hω.2, max_eq_right hω.1]

theorem gamma_logComp_mixed {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (v : S.dom)
    (hv : ∀ᵐ ω ∂μ, (v : Lp ℝ 2 μ) ω ∈ Icc ε M) :
    S.Γ (S.logComp hε hεM v) v =ᵐ[μ] fun ω => S.Γ v v ω / (v : Lp ℝ 2 μ) ω := by
  filter_upwards [S.gamma_lipschitzComp_mixed_general
    (exists_lipschitzWith_clippedLog hε hεM).choose_spec v, hv,
    S.gamma_eq_zero_on_const v ε, S.gamma_eq_zero_on_const v M] with ω hc hω hl hr
  change S.Γ (S.logComp hε hεM v) v ω = _ at hc
  rw [hc]
  by_cases he : (v : Lp ℝ 2 μ) ω = ε
  · simp [hl he]
  by_cases hm : (v : Lp ℝ 2 μ) ω = M
  · simp [hr hm]
  have hlo : ε < (v : Lp ℝ 2 μ) ω := lt_of_le_of_ne hω.1 (Ne.symm he)
  have hhi : (v : Lp ℝ 2 μ) ω < M := lt_of_le_of_ne hω.2 hm
  have heq : clippedLog ε M =ᶠ[𝓝 ((v : Lp ℝ 2 μ) ω)] Real.log := by
    filter_upwards [Ioo_mem_nhds hlo hhi] with x hx
    simp [clippedLog, min_eq_left hx.2.le, max_eq_right hx.1.le]
  rw [heq.deriv_eq, Real.deriv_log]
  ring

def fisherInformation (v : S.dom) : ℝ := ∫ ω, S.Γ v v ω / (v : Lp ℝ 2 μ) ω ∂μ

theorem energy_log_mixed {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (v : S.dom)
    (hv : ∀ᵐ ω ∂μ, (v : Lp ℝ 2 μ) ω ∈ Icc ε M) :
    S.energy.E v (S.logComp hε hεM v) = (1/2:ℝ) * S.fisherInformation v := by
  rw [S.energy.symm, ErrorData.energy_apply,
    integral_congr_ae (S.gamma_logComp_mixed hε hεM v hv)]
  rfl

theorem energy_sqrt {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (v : S.dom)
    (hv : ∀ᵐ ω ∂μ, (v : Lp ℝ 2 μ) ω ∈ Icc ε M) :
    S.energy.E (S.powComp hε hεM (1/2) v) (S.powComp hε hεM (1/2) v) =
      (1/8:ℝ) * S.fisherInformation v := by
  have he := S.energy_pow_half hε hεM 1 v hv
  norm_num only [one_pow, one_div, show (1:ℝ)-2 = -1 by norm_num, Real.rpow_neg_one] at he
  convert he using 1
  unfold fisherInformation
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by ring

theorem energy_sqrt_eq_fisher {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (v : S.dom)
    (hv : ∀ᵐ ω ∂μ, (v : Lp ℝ 2 μ) ω ∈ Icc ε M) :
    4 * S.energy.E (S.powComp hε hεM (1/2) v) (S.powComp hε hεM (1/2) v) =
      (1/2:ℝ) * S.fisherInformation v := by
  rw [S.energy_sqrt hε hεM v hv]
  ring

theorem integral_log_mul_generator {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (v : S.dom) (hA : (v : Lp ℝ 2 μ) ∈ S.generatorDom)
    (hv : ∀ᵐ ω ∂μ, (v : Lp ℝ 2 μ) ω ∈ Icc ε M) :
    (∫ ω, Real.log ((v : Lp ℝ 2 μ) ω) * S.generator ⟨v,hA⟩ ω ∂μ) =
      -4 * S.energy.E (S.powComp hε hεM (1/2) v) (S.powComp hε hεM (1/2) v) := by
  have he := S.energy.energy_eq_neg_inner_generator S.energy_closed S.dense ⟨v,hA⟩
    (S.logComp hε hεM v)
  have hi : inner ℝ (S.generator ⟨v,hA⟩) (S.logComp hε hεM v : Lp ℝ 2 μ) =
      ∫ ω, Real.log ((v : Lp ℝ 2 μ) ω) * S.generator ⟨v,hA⟩ ω ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [S.coeFn_logComp hε hεM v hv] with ω hω
    simp only [RCLike.inner_apply, conj_trivial, hω]
  rw [hi] at he
  change S.energy.E v (S.logComp hε hεM v) =
    -(∫ ω, Real.log ((v : Lp ℝ 2 μ) ω) * S.generator ⟨v,hA⟩ ω ∂μ) at he
  have hl := S.energy_log_mixed hε hεM v hv
  have hs := S.energy_sqrt_eq_fisher hε hεM v hv
  linarith

theorem continuous_entropy_comp_semigroup {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (u : Lp ℝ 2 μ) (hu : ∀ᵐ ω ∂μ, u ω ∈ Icc ε M) :
    ContinuousOn (fun s => entropy μ (S.semigroup s u)) (Ici 0) := by
  apply ((S.continuous_integral_comp_semigroup_of_Icc hεM (xlogx_contDiffAt_on hε) u hu).sub
    (continuousOn_const (c := (∫ ω, u ω ∂μ)*Real.log (∫ ω, u ω ∂μ)))).congr
  intro s hs
  simp only [entropy, S.integral_semigroup hs, Pi.sub_apply]

theorem hasDerivAt_entropy_semigroup {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (u : S.generatorDom) (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => entropy μ (S.semigroup s u))
      (-4 * S.energy.E (S.powComp hε hεM (1/2) (S.semigroupFormDom ht.le u))
        (S.powComp hε hεM (1/2) (S.semigroupFormDom ht.le u))) t := by
  have hd := S.hasDerivAt_integral_comp_semigroup_of_Icc hεM (xlogx_contDiffAt_on hε) u hu ht
  let v := S.semigroupFormDom ht.le u
  let A := S.generator (S.semigroupGeneratorDom ht.le u)
  have hv : ∀ᵐ ω ∂μ, (v : Lp ℝ 2 μ) ω ∈ Icc ε M := S.semigroup_mem_Icc ht.le u hu
  have hi : Integrable (fun ω => Real.log ((v : Lp ℝ 2 μ) ω) * A ω) μ := by
    apply ((Lp.memLp (S.logComp hε hεM v : Lp ℝ 2 μ)).integrable_mul (Lp.memLp A)).congr
    filter_upwards [S.coeFn_logComp hε hεM v hv] with ω hω
    simp only [Pi.mul_apply, hω]
  have he : (∫ ω, deriv (fun x : ℝ => x*Real.log x) ((v : Lp ℝ 2 μ) ω) * A ω ∂μ) =
      ∫ ω, Real.log ((v : Lp ℝ 2 μ) ω) * A ω ∂μ := by
    calc
      _ = ∫ ω, Real.log ((v : Lp ℝ 2 μ) ω) * A ω + A ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hv] with ω hω
        rw [(Real.hasDerivAt_mul_log (ne_of_gt (hε.trans_le hω.1))).deriv]
        ring
      _ = _ := by rw [integral_add hi ((Lp.memLp A).integrable (by norm_num)),
                     S.integral_generator_eq_zero, add_zero]
  change HasDerivAt _ (∫ ω, deriv (fun x : ℝ => x*Real.log x) ((v : Lp ℝ 2 μ) ω) * A ω ∂μ) t at hd
  have hl := S.integral_log_mul_generator hε hεM v (S.semigroup_mem_generatorDom ht.le u) hv
  change (∫ ω, Real.log ((v : Lp ℝ 2 μ) ω) * A ω ∂μ) = _ at hl
  rw [he, hl] at hd
  apply (hd.sub_const ((∫ ω, (u : Lp ℝ 2 μ) ω ∂μ)*Real.log (∫ ω, (u : Lp ℝ 2 μ) ω ∂μ))).congr_of_eventuallyEq
  filter_upwards [Ici_mem_nhds ht] with s hs
  simp only [entropy, S.integral_semigroup hs]

theorem antitone_entropy_semigroup {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (u : S.generatorDom) (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) :
    AntitoneOn (fun s => entropy μ (S.semigroup s u)) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) (S.continuous_entropy_comp_semigroup hε hεM u hu)
  · intro t ht
    exact (S.hasDerivAt_entropy_semigroup hε hεM u hu
      (by simpa only [interior_Ici, mem_Ioi] using ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(S.hasDerivAt_entropy_semigroup hε hεM u hu
      (by simpa only [interior_Ici, mem_Ioi] using ht)).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (S.energy.nonneg _)

end ErrorCalculus.ErrorStructure
