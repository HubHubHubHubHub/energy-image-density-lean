import ErrorCalculus.Dirichlet.IntegralRpowExponent
import ErrorCalculus.Dirichlet.SemigroupDissipation
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Semigroup Variable Exponent

## Main results
The mixed chain rule, by splitting slopes and applying the real mean value theorem.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology Set
namespace ErrorCalculus

/-- Mean value theorem with unordered endpoints, including equal endpoints. -/
theorem exists_mean_derivative {F D : ℝ → ℝ} (hF : ∀ r, HasDerivAt F (D r) r)
    (a b : ℝ) : ∃ r ∈ uIcc a b, F b-F a = (b-a)*D r := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr fun r => (hF r).continuousAt
  rcases lt_trichotomy a b with h | h | h
  · obtain ⟨r,hr,he⟩ := exists_hasDerivAt_eq_slope F D h hc.continuousOn (fun r _ => hF r)
    refine ⟨r, Icc_subset_uIcc ⟨hr.1.le,hr.2.le⟩, ?_⟩
    have := (eq_div_iff (sub_ne_zero.mpr h.ne')).mp he
    nlinarith
  · subst b
    exact ⟨a, by simp, by simp⟩
  · obtain ⟨r,hr,he⟩ := exists_hasDerivAt_eq_slope F D h hc.continuousOn (fun r _ => hF r)
    refine ⟨r, ?_, ?_⟩
    · rw [uIcc_comm]; exact Icc_subset_uIcc ⟨hr.1.le,hr.2.le⟩
    · have := (eq_div_iff (sub_ne_zero.mpr h.ne')).mp he
      nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Only continuity of the L² curve and its fixed-exponent integral derivative are needed. -/
theorem hasDerivAt_integral_rpow_var {ε M : ℝ} (hε : 0 < ε)
    (v : ℝ → Lp ℝ 2 μ) (hv : ∀ s, ∀ᵐ ω ∂μ, v s ω ∈ Icc ε M)
    {q : ℝ → ℝ} {q' d t : ℝ} (hq : HasDerivAt q q' t)
    (hc : ContinuousAt v t)
    (hd : HasDerivAt (fun s => ∫ ω, (v s ω)^(q t) ∂μ) d t) :
    HasDerivAt (fun s => ∫ ω, (v s ω)^(q s) ∂μ)
      (q' * (∫ ω, (v t ω)^(q t)*Real.log (v t ω) ∂μ) + d) t := by
  have hm (s : ℝ) := exists_mean_derivative
    (hasDerivAt_integral_rpow_exponent hε (v s) (hv s)) (q t) (q s)
  choose r hr he using hm
  have hrt : Tendsto r (𝓝 t) (𝓝 (q t)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _)
      (Eventually.of_forall fun s => abs_sub_left_of_mem_uIcc (hr s))
    simpa only [sub_self, abs_zero] using (hq.continuousAt.sub_const (q t)).abs
  have hlog := tendsto_integral_rpow_log_confined hε hc hrt
    (Eventually.of_forall hv) (hv t)
  have ht := (hq.tendsto_slope.mul (hlog.mono_left nhdsWithin_le_nhds)).add hd.tendsto_slope
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply ht.congr'
  filter_upwards [] with s
  simp only [slope_fun_def_field]
  have hh := he s
  calc
    _ = ((q s-q t)*(∫ ω, (v s ω)^(r s)*Real.log (v s ω) ∂μ) +
        ((∫ ω, (v s ω)^(q t) ∂μ) - ∫ ω, (v t ω)^(q t) ∂μ))/(s-t) := by ring
    _ = _ := by rw [← hh]; congr 1; ring

namespace ErrorStructure
variable (S : ErrorStructure Ω μ)

theorem hasDerivAt_integral_rpow_semigroup_var {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (u : S.generatorDom) (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M)
    {q : ℝ → ℝ} {q' t : ℝ} (hq : HasDerivAt q q' t) (hq1 : 1 < q t) (ht : 0 < t) :
    HasDerivAt (fun s => ∫ ω, (S.semigroup s u ω)^(q s) ∂μ)
      (q' * (∫ ω, (S.semigroup t u ω)^(q t)*Real.log (S.semigroup t u ω) ∂μ) -
        (4*(q t-1)/(q t)) * S.energy.E
          (S.powComp hε hεM (q t/2) (S.semigroupFormDom ht.le u))
          (S.powComp hε hεM (q t/2) (S.semigroupFormDom ht.le u))) t := by
  let v := fun s : ℝ => S.semigroup (max s 0) u
  have hv (s : ℝ) : ∀ᵐ ω ∂μ, v s ω ∈ Icc ε M :=
    S.semigroup_mem_Icc (le_max_right _ _) u hu
  have he : v =ᶠ[𝓝 t] fun s => S.semigroup s u := by
    filter_upwards [Ici_mem_nhds ht] with s hs
    simp only [v, max_eq_left (show 0 ≤ s from hs)]
  have hc : ContinuousAt v t := (S.hasDerivAt_semigroup u ht).continuousAt.congr he.symm
  have hd := (S.hasDerivAt_integral_pow_semigroup hε hεM hq1 u hu ht).congr_of_eventuallyEq
    (he.fun_comp (fun w : Lp ℝ 2 μ => ∫ ω, (w ω)^(q t) ∂μ))
  have hh := hasDerivAt_integral_rpow_var hε v hv hq hc hd
  have hv_t : v t = S.semigroup t u := he.eq_of_nhds
  rw [hv_t] at hh
  have hh' := hh.congr_of_eventuallyEq (by
    filter_upwards [he] with s hs
    exact congrArg (fun w : Lp ℝ 2 μ => ∫ ω, (w ω)^(q s) ∂μ) hs.symm)
  simpa only [neg_mul, sub_eq_add_neg] using hh'

theorem continuous_integral_rpow_semigroup_var {ε M : ℝ} (hε : 0 < ε)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ ω ∂μ, f ω ∈ Icc ε M)
    {q : ℝ → ℝ} (hq : ContinuousOn q (Ici 0)) :
    ContinuousOn (fun s => ∫ ω, (S.semigroup s f ω)^(q s) ∂μ) (Ici 0) := by
  intro t ht
  exact tendsto_integral_rpow_confined hε
    (S.energy.continuous_semigroup_apply S.energy_closed S.dense f t ht) (hq t ht)
    ((show ∀ᶠ s in 𝓝[Ici 0] t, s ∈ Ici 0 from self_mem_nhdsWithin).mono
      fun s hs => S.semigroup_mem_Icc hs f hf)
    (S.semigroup_mem_Icc ht f hf)

end ErrorStructure
end ErrorCalculus
