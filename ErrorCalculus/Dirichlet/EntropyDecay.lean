import ErrorCalculus.Dirichlet.SemigroupDissipation
import ErrorCalculus.Dirichlet.SemigroupEnergyQuotient
import ErrorCalculus.Dirichlet.OULogSobolev
import ErrorCalculus.Dirichlet.WienerLogSobolev

/-!
# Entropy Decay

## Main results
Logarithmic Sobolev implies exponential entropy decay.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace ErrorCalculus
open QuadForm

/-- Elementary integrating-factor form of Gronwall, with continuity at time zero. -/
theorem antitone_exp_mul_of_deriv_le {g g' : ℝ → ℝ} {k : ℝ}
    (hg : ∀ t > 0, HasDerivAt g (g' t) t) (hc : ContinuousOn g (Ici 0))
    (hle : ∀ t > 0, g' t ≤ -k*g t) :
    AntitoneOn (fun t => Real.exp (k*t)*g t) (Ici 0) := by
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt (fun s => Real.exp (k*s)*g s)
      (Real.exp (k*t)*k*g t + Real.exp (k*t)*g' t) t := by
    convert! (((hasDerivAt_id t).const_mul k).exp).mul (hg t ht) using 1
    simp only [id_eq]
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) ((by fun_prop : Continuous (fun t => Real.exp (k*t))).continuousOn.mul hc)
  · intro t ht
    exact (hd t (by simpa only [interior_Ici, mem_Ioi] using ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    change deriv (fun s => Real.exp (k*s)*g s) t ≤ 0
    rw [(hd t ht').deriv]
    have hh := mul_le_mul_of_nonneg_left (hle t ht') (Real.exp_pos (k*t)).le
    nlinarith

namespace ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

theorem entropy_le_energy_sqrt {ε M c : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hLS : S.HasLogSobolev c) (v : S.dom)
    (hv : ∀ᵐ ω ∂μ, (v : Lp ℝ 2 μ) ω ∈ Icc ε M) :
    entropy μ (v : Lp ℝ 2 μ) ≤
      c * S.energy.E (S.powComp hε hεM (1/2) v) (S.powComp hε hεM (1/2) v) := by
  have he : (fun ω => ((S.powComp hε hεM (1/2) v : Lp ℝ 2 μ) ω)^2) =ᵐ[μ]
      (v : Lp ℝ 2 μ) := by
    filter_upwards [S.coeFn_powComp hε hεM (1/2) v hv, hv] with ω hω hb
    rw [hω, ← Real.sqrt_eq_rpow, Real.sq_sqrt (hε.le.trans hb.1)]
  simpa only [entropy_congr_ae he] using (hLS (S.powComp hε hεM (1/2) v)).2

theorem entropy_semigroup_le_exp_of_generatorDom {ε M c : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hLS : S.HasLogSobolev c) (hc : 0 < c) (u : S.generatorDom)
    (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) {t : ℝ} (ht : 0 ≤ t) :
    entropy μ (S.semigroup t u) ≤ Real.exp (-4*t/c) * entropy μ (u : Lp ℝ 2 μ) := by
  let g := fun s : ℝ => entropy μ (S.semigroup s u)
  have hd (s : ℝ) (hs : 0 < s) := S.hasDerivAt_entropy_semigroup hε hεM u hu hs
  have hle (s : ℝ) (hs : 0 < s) : deriv g s ≤ -(4/c)*g s := by
    rw [(hd s hs).deriv]
    have he := S.entropy_le_energy_sqrt hε hεM hLS (S.semigroupFormDom hs.le u)
      (S.semigroup_mem_Icc hs.le u hu)
    have hdiv : g s / c ≤ S.energy.E
        (S.powComp hε hεM (1/2) (S.semigroupFormDom hs.le u))
        (S.powComp hε hεM (1/2) (S.semigroupFormDom hs.le u)) :=
      (div_le_iff₀ hc).mpr (by rw [mul_comm]; exact he)
    calc
      _ ≤ -4*(g s/c) := mul_le_mul_of_nonpos_left hdiv (by norm_num)
      _ = _ := by ring
  have ha := antitone_exp_mul_of_deriv_le (g := g) (g' := deriv g) (k := 4/c)
    (fun s hs => (hd s hs).differentiableAt.hasDerivAt)
    (S.continuous_entropy_comp_semigroup hε hεM u hu) hle
  have hh := ha (show (0:ℝ) ∈ Ici 0 by simp) ht ht
  have hz : g 0 = entropy μ (u : Lp ℝ 2 μ) := by simp [g, semigroup]
  change Real.exp (4/c*t)*g t ≤ Real.exp (4/c*0)*g 0 at hh
  rw [hz] at hh
  simp only [mul_zero, Real.exp_zero, one_mul] at hh
  calc
    g t = Real.exp (-4*t/c) * (Real.exp (4/c*t)*g t) := by
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le

/-- Markov resolvents preserve every closed interval, by the normal-contraction fixed-point rule. -/
theorem betaResolvent_mem_Icc {a b : ℝ} (hab : a ≤ b) (β : ℝ) (hβ : 0 < β)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ ω ∂μ, f ω ∈ Icc a b) :
    ∀ᵐ ω ∂μ, (β • S.resolvent β hβ f) ω ∈ Icc a b := by
  let v := β • S.resolvent β hβ f
  have hclip : LipschitzWith 1 (fun x : ℝ => max a (min x b)) :=
    (LipschitzWith.id.min_const b).const_max a
  let hm := memLp_deriv_comp hclip v
  let w := hm.toLp _
  have hw : (w : Ω → ℝ) =ᵐ[μ] fun ω => max a (min (v ω) b) := hm.coeFn_toLp
  have he : w = v := S.resolvent_fixed_of_normal_contraction β hβ f hclip
    (hf.mono fun ω hω => by simp only [min_eq_left hω.2, max_eq_right hω.1]) w hw
  rw [he] at hw
  filter_upwards [hw] with ω hω
  change v ω ∈ Icc a b
  rw [hω]
  exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem tendsto_betaResolvent {ι : Type*} {l : Filter ι} (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) (ht : Tendsto b l atTop) (f : Lp ℝ 2 μ) :
    Tendsto (fun i => b i • S.resolvent (b i) (hb i) f) l (𝓝 f) :=
  S.energy.tendsto_beta_resolvent S.energy_closed S.dense b hb ht f

end ErrorStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem continuous_integral_L2 : Continuous (fun u : Lp ℝ 2 μ => ∫ ω, u ω ∂μ) := by
  have he : (fun u : Lp ℝ 2 μ => ∫ ω, u ω ∂μ) =
      fun u => inner ℝ (Lp.const 2 μ (1 : ℝ)) u := by
    funext u
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with ω hω
    simp only [RCLike.inner_apply, conj_trivial, hω, Function.const_apply, mul_one]
  rw [he]
  exact (innerSL ℝ (Lp.const 2 μ (1 : ℝ))).continuous

/-- L² continuity of entropy on a fixed positive bounded interval. -/
theorem continuous_entropy_on_Icc {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) :
    ContinuousOn (fun u : Lp ℝ 2 μ => entropy μ u)
      {u | ∀ᵐ ω ∂μ, u ω ∈ Icc ε M} := by
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_deriv (xlogx_contDiffAt_on (b := M) hε)
  have hd := fun x => ((contDiff_tangentExtension hεM hL).differentiable (by norm_num) x).hasDerivAt
  have hc := (continuous_integralFunctional (μ := μ) hd
    (lipschitzWith_deriv_tangentExtension hεM hL)).sub
    (Real.continuous_mul_log.comp continuous_integral_L2)
  apply hc.continuousOn.congr
  intro u hu
  simp only [entropy, Pi.sub_apply, Function.comp_def, integralFunctional]
  rw [← integral_tangentExtension_comp hεM
    (fun x hx => (xlogx_contDiffAt_on hε x hx).differentiableAt (by norm_num)) hL u hu]

namespace ErrorStructure
variable (S : ErrorStructure Ω μ)

/-- Exponential entropy decay for every confined L² datum, by generator-domain approximation. -/
theorem entropy_semigroup_le_exp {ε M c : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hLS : S.HasLogSobolev c) (hc : 0 < c) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ ω ∂μ, f ω ∈ Icc ε M) {t : ℝ} (ht : 0 ≤ t) :
    entropy μ (S.semigroup t f) ≤ Real.exp (-4*t/c) * entropy μ f := by
  let fₙ : ℕ → S.generatorDom := fun n =>
    ⟨resolventParameter n • S.resolvent (resolventParameter n) (resolventParameter_pos n) f,
      S.energy.betaResolvent_mem_generatorDom S.energy_closed S.dense
        (resolventParameter n) (resolventParameter_pos n) f⟩
  have hb (n : ℕ) : ∀ᵐ ω ∂μ, (fₙ n : Lp ℝ 2 μ) ω ∈ Icc ε M :=
    S.betaResolvent_mem_Icc hεM (resolventParameter n) (resolventParameter_pos n) f hf
  have hconv : Tendsto (fun n => (fₙ n : Lp ℝ 2 μ)) atTop (𝓝 f) :=
    S.tendsto_betaResolvent resolventParameter resolventParameter_pos tendsto_resolventParameter f
  have hconvP := (S.semigroup t).continuous.tendsto f |>.comp hconv
  have hent : Tendsto (fun n => entropy μ (fₙ n : Lp ℝ 2 μ)) atTop (𝓝 (entropy μ f)) :=
    ((continuous_entropy_on_Icc hε hεM) f hf).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hconv, Filter.Eventually.of_forall hb⟩)
  have hentP : Tendsto (fun n => entropy μ (S.semigroup t (fₙ n))) atTop
      (𝓝 (entropy μ (S.semigroup t f))) :=
    ((continuous_entropy_on_Icc hε hεM) _ (S.semigroup_mem_Icc ht f hf)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hconvP,
        Filter.Eventually.of_forall fun n => S.semigroup_mem_Icc ht (fₙ n) (hb n)⟩)
  exact le_of_tendsto_of_tendsto' hentP (hent.const_mul _) fun n =>
    S.entropy_semigroup_le_exp_of_generatorDom hε hεM hLS hc (fₙ n) (hb n) ht

end ErrorStructure

open ProbabilityTheory

theorem ouStructure_entropy_semigroup_le {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (f : Lp ℝ 2 (gaussianReal 0 1))
    (hf : ∀ᵐ ω ∂gaussianReal 0 1, f ω ∈ Icc ε M) {t : ℝ} (ht : 0 ≤ t) :
    entropy (gaussianReal 0 1) (ouStructure.semigroup t f) ≤
      Real.exp (-t) * entropy (gaussianReal 0 1) f := by
  convert ouStructure.entropy_semigroup_le_exp hε hεM ouStructure_hasLogSobolev
    (by norm_num) f hf ht using 1
  congr 2
  ring

theorem wienerStructure_entropy_semigroup_le {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (f : Lp ℝ 2 wienerCoord) (hf : ∀ᵐ ω ∂wienerCoord, f ω ∈ Icc ε M)
    {t : ℝ} (ht : 0 ≤ t) :
    entropy wienerCoord (wienerStructure.semigroup t f) ≤ Real.exp (-t) * entropy wienerCoord f := by
  convert wienerStructure.entropy_semigroup_le_exp hε hεM wienerStructure_hasLogSobolev
    (by norm_num) f hf ht using 1
  congr 2
  ring

theorem wienerPathStructure_entropy_semigroup_le {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (f : Lp ℝ 2 Foundations.wienerMeasure) (hf : ∀ᵐ ω ∂Foundations.wienerMeasure, f ω ∈ Icc ε M)
    {t : ℝ} (ht : 0 ≤ t) :
    entropy Foundations.wienerMeasure (wienerPathStructure.semigroup t f) ≤ Real.exp (-t) * entropy Foundations.wienerMeasure f := by
  convert wienerPathStructure.entropy_semigroup_le_exp hε hεM wienerPathStructure_hasLogSobolev
    (by norm_num) f hf ht using 1
  congr 2
  ring

end ErrorCalculus
