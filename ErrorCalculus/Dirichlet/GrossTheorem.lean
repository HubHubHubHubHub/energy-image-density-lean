import ErrorCalculus.Dirichlet.GrossExponent
import ErrorCalculus.Dirichlet.SemigroupVariableExponent
import ErrorCalculus.Dirichlet.EntropyDecay

/-!
# Gross Theorem

## Main results
Logarithmic Sobolev implies Gross hypercontractivity on confined generator data.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology Set
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem entropy_rpow_eq {ε M : ℝ} (hε : 0 < ε) (v : Lp ℝ 2 μ)
    (hv : ∀ᵐ ω ∂μ, v ω ∈ Icc ε M) (q : ℝ) :
    entropy μ (fun ω => (v ω)^q) =
      q * (∫ ω, (v ω)^q*Real.log (v ω) ∂μ) -
        (∫ ω, (v ω)^q ∂μ)*Real.log (∫ ω, (v ω)^q ∂μ) := by
  unfold entropy
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hv] with ω hω
  rw [Real.log_rpow (hε.trans_le hω.1)]
  ring

namespace ErrorStructure
variable (S : ErrorStructure Ω μ)

theorem entropy_rpow_le_energy {ε M c : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hLS : S.HasLogSobolev c) (v : S.dom)
    (hv : ∀ᵐ ω ∂μ, (v : Lp ℝ 2 μ) ω ∈ Icc ε M) (q : ℝ) :
    entropy μ (fun ω => ((v : Lp ℝ 2 μ) ω)^q) ≤
      c * S.energy.E (S.powComp hε hεM (q/2) v) (S.powComp hε hεM (q/2) v) := by
  have he : (fun ω => ((S.powComp hε hεM (q/2) v : Lp ℝ 2 μ) ω)^2) =ᵐ[μ]
      fun ω => ((v : Lp ℝ 2 μ) ω)^q := by
    filter_upwards [S.coeFn_powComp hε hεM (q/2) v hv, hv] with ω hω hb
    rw [hω, ← Real.rpow_mul_natCast (hε.le.trans hb.1)]
    norm_num
  simpa only [entropy_congr_ae he] using (hLS (S.powComp hε hεM (q/2) v)).2

def grossLogNorm (c p : ℝ) (f : Lp ℝ 2 μ) (t : ℝ) : ℝ :=
  Real.log (∫ ω, (S.semigroup t f ω)^(grossExponent c p t) ∂μ) / grossExponent c p t

theorem hasDerivAt_grossLogNorm {ε M c p : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hp : 1 < p) (u : S.generatorDom)
    (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (S.grossLogNorm c p u)
      ((4*(grossExponent c p t-1)/c *
          entropy μ (fun ω => (S.semigroup t u ω)^(grossExponent c p t)) -
        4*(grossExponent c p t-1) * S.energy.E
          (S.powComp hε hεM (grossExponent c p t/2) (S.semigroupFormDom ht.le u))
          (S.powComp hε hεM (grossExponent c p t/2) (S.semigroupFormDom ht.le u))) /
        ((grossExponent c p t)^2 * ∫ ω, (S.semigroup t u ω)^(grossExponent c p t) ∂μ)) t := by
  have hq := grossExponent_one_lt (c := c) hp t
  have hq0 : grossExponent c p t ≠ 0 := by linarith
  have hv := S.semigroup_mem_Icc ht.le u hu
  have hΛ := integral_rpow_pos hε (S.semigroup t u) hv (grossExponent c p t)
  have hd := S.hasDerivAt_integral_rpow_semigroup_var hε hεM u hu
    (hasDerivAt_grossExponent c p t) hq ht
  have hh := (hd.log (ne_of_gt hΛ)).div (hasDerivAt_grossExponent c p t) hq0
  convert! hh using 1
  rw [entropy_rpow_eq hε (S.semigroup t u) hv]
  field_simp
  ring

theorem deriv_grossLogNorm_nonpos {ε M c p : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hLS : S.HasLogSobolev c) (hc : 0 < c) (hp : 1 < p) (u : S.generatorDom)
    (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) {t : ℝ} (ht : 0 < t) :
    deriv (S.grossLogNorm c p u) t ≤ 0 := by
  rw [(S.hasDerivAt_grossLogNorm hε hεM hp u hu ht).deriv]
  have hq := grossExponent_one_lt (c := c) hp t
  have hv := S.semigroup_mem_Icc ht.le u hu
  have hΛ := integral_rpow_pos hε (S.semigroup t u) hv (grossExponent c p t)
  apply div_nonpos_of_nonpos_of_nonneg _ (mul_nonneg (sq_nonneg _) hΛ.le)
  have he := S.entropy_rpow_le_energy hε hεM hLS (S.semigroupFormDom ht.le u) hv
    (grossExponent c p t)
  have hm := mul_le_mul_of_nonneg_left he
    (show 0 ≤ 4*(grossExponent c p t-1)/c by positivity)
  have hz : 4*(grossExponent c p t-1)/c*c = 4*(grossExponent c p t-1) := by
    field_simp
  rw [← mul_assoc, hz] at hm
  exact sub_nonpos.mpr hm

theorem antitone_grossLogNorm {ε M c p : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hLS : S.HasLogSobolev c) (hc : 0 < c) (hp : 1 < p) (u : S.generatorDom)
    (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) :
    AntitoneOn (S.grossLogNorm c p u) (Ici 0) := by
  have hq (t : ℝ) : grossExponent c p t ≠ 0 := ne_of_gt (lt_trans zero_lt_one (grossExponent_one_lt hp t))
  have hΛ (t : ℝ) (ht : t ∈ Ici 0) :=
    integral_rpow_pos hε (S.semigroup t u) (S.semigroup_mem_Icc ht u hu) (grossExponent c p t)
  have hcont : ContinuousOn (S.grossLogNorm c p u) (Ici 0) :=
    ((S.continuous_integral_rpow_semigroup_var hε u hu (continuous_grossExponent c p).continuousOn).log
      (fun t ht => ne_of_gt (hΛ t ht))).div (continuous_grossExponent c p).continuousOn (fun t _ => hq t)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont
  · intro t ht
    exact (S.hasDerivAt_grossLogNorm hε hεM hp u hu
      (by simpa only [interior_Ici, mem_Ioi] using ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    exact S.deriv_grossLogNorm_nonpos hε hεM hLS hc hp u hu
      (by simpa only [interior_Ici, mem_Ioi] using ht)

theorem integral_rpow_semigroup_le_of_generatorDom {ε M c p : ℝ}
    (hε : 0 < ε) (hεM : ε ≤ M) (hLS : S.HasLogSobolev c) (hc : 0 < c) (hp : 1 < p)
    (u : S.generatorDom) (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, (S.semigroup t u ω)^(grossExponent c p t) ∂μ)^(1/grossExponent c p t) ≤
      (∫ ω, ((u : Lp ℝ 2 μ) ω)^p ∂μ)^(1/p) := by
  have h := (S.antitone_grossLogNorm hε hεM hLS hc hp u hu) (by simp) ht ht
  have hh := Real.exp_le_exp.mpr h
  have hz : S.grossLogNorm c p u 0 = Real.log (∫ ω, ((u : Lp ℝ 2 μ) ω)^p ∂μ)/p := by
    simp [grossLogNorm, semigroup]
  rw [hz] at hh
  simpa only [grossLogNorm, Real.rpow_def_of_pos
    (integral_rpow_pos hε (S.semigroup t u) (S.semigroup_mem_Icc ht u hu) _),
    Real.rpow_def_of_pos (integral_rpow_pos hε (u : Lp ℝ 2 μ) hu p), mul_one_div] using hh

end ErrorStructure
end ErrorCalculus
