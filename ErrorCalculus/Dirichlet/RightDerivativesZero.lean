import ErrorCalculus.Dirichlet.GrossTheorem

/-!
# Right Derivatives Zero

## Main results
Right derivatives at the initial time and comparison of right slopes.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology Set
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- The form-domain representative of a generator-domain element. -/
def generatorForm (u : S.generatorDom) : S.dom :=
  ⟨u, S.energy.formResolvent_dom_le S.energy_closed S.dense u.property⟩

@[simp] theorem semigroupFormDom_zero (u : S.generatorDom) :
    S.semigroupFormDom (t := 0) le_rfl u = S.generatorForm u := by
  apply Subtype.ext
  simp [semigroupFormDom, generatorForm, semigroup]

theorem hasDerivWithinAt_integral_comp_semigroup_of_Icc {F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (u : S.generatorDom) (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc a b)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => ∫ ω, F (S.semigroup s u ω) ∂μ)
      (∫ ω, deriv F (S.semigroup t u ω) *
        S.generator (S.semigroupGeneratorDom ht u) ω ∂μ) (Ici t) t := by
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_deriv hF
  have hd := S.hasDerivWithinAt_integral_comp_semigroup
    (fun x => ((contDiff_tangentExtension hab hL).differentiable (by norm_num) x).hasDerivAt)
    (lipschitzWith_deriv_tangentExtension hab hL) u ht
  have he := deriv_tangentExtension_comp hab hL (S.semigroup t u) (S.semigroup_mem_Icc ht u hu)
  have hv : (∫ ω, deriv (tangentExtension F a b) (S.semigroup t u ω) *
      S.generator (S.semigroupGeneratorDom ht u) ω ∂μ) =
      ∫ ω, deriv F (S.semigroup t u ω) * S.generator (S.semigroupGeneratorDom ht u) ω ∂μ :=
    integral_congr_ae (he.mul (Filter.EventuallyEq.refl _ _))
  rw [hv] at hd
  apply hd.congr_of_eventuallyEq_of_mem _ (by simp)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs : 0 ≤ s := ht.trans hs
  exact (integral_tangentExtension_comp hab (fun x hx => (hF x hx).differentiableAt (by norm_num))
    hL (S.semigroup s u) (S.semigroup_mem_Icc hs u hu)).symm

theorem hasDerivWithinAt_integral_pow_semigroup_Ici {ε M q : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hq : 1 < q) (u : S.generatorDom)
    (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => ∫ ω, (S.semigroup s u ω)^q ∂μ)
      (-(4*(q-1)/q) * S.energy.E
        (S.powComp hε hεM (q/2) (S.semigroupFormDom ht u))
        (S.powComp hε hεM (q/2) (S.semigroupFormDom ht u))) (Ici t) t := by
  have hd := S.hasDerivWithinAt_integral_comp_semigroup_of_Icc hεM (rpow_contDiffAt_on hε q) u hu ht
  have hg := S.semigroup_mem_Icc ht u hu
  have hs := S.stroock_varopoulos hε hεM hq (S.semigroupFormDom ht u)
    (S.semigroup_mem_generatorDom ht u) hg
  have he : (∫ ω, deriv (fun x : ℝ => x^q) (S.semigroup t u ω) *
      S.generator (S.semigroupGeneratorDom ht u) ω ∂μ) =
      -q * ∫ ω, (-S.generator (S.semigroupGeneratorDom ht u) ω) *
        (S.semigroup t u ω)^(q-1) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hg] with ω hω
    rw [(Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hε.trans_le hω.1)))).deriv]
    ring
  change (∫ ω, (-S.generator (S.semigroupGeneratorDom ht u) ω) *
    (S.semigroup t u ω)^(q-1) ∂μ) = _ at hs
  rw [he, hs] at hd
  convert hd using 1
  have hq0 : q ≠ 0 := by linarith
  field_simp

theorem hasDerivWithinAt_entropy_semigroup_Ici {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (u : S.generatorDom) (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => entropy μ (S.semigroup s u))
      (-4 * S.energy.E (S.powComp hε hεM (1/2) (S.semigroupFormDom ht u))
        (S.powComp hε hεM (1/2) (S.semigroupFormDom ht u))) (Ici t) t := by
  have hd := S.hasDerivWithinAt_integral_comp_semigroup_of_Icc hεM (xlogx_contDiffAt_on hε) u hu ht
  let v := S.semigroupFormDom ht u
  let A := S.generator (S.semigroupGeneratorDom ht u)
  have hv : ∀ᵐ ω ∂μ, (v : Lp ℝ 2 μ) ω ∈ Icc ε M := S.semigroup_mem_Icc ht u hu
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
  change HasDerivWithinAt _ (∫ ω, deriv (fun x : ℝ => x*Real.log x) ((v : Lp ℝ 2 μ) ω) * A ω ∂μ) (Ici t) t at hd
  have hl := S.integral_log_mul_generator hε hεM v (S.semigroup_mem_generatorDom ht u) hv
  change (∫ ω, Real.log ((v : Lp ℝ 2 μ) ω) * A ω ∂μ) = _ at hl
  rw [he, hl] at hd
  apply (hd.sub_const ((∫ ω, (u : Lp ℝ 2 μ) ω ∂μ)*Real.log (∫ ω, (u : Lp ℝ 2 μ) ω ∂μ))).congr_of_eventuallyEq_of_mem _ (by simp)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs : 0 ≤ s := ht.trans hs
  simp only [entropy, S.integral_semigroup hs]

theorem hasDerivWithinAt_entropy_semigroup_zero {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (u : S.generatorDom) (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) :
    HasDerivWithinAt (fun s => entropy μ (S.semigroup s u))
      (-4 * S.energy.E (S.powComp hε hεM (1/2) (S.generatorForm u))
        (S.powComp hε hεM (1/2) (S.generatorForm u))) (Ici 0) 0 := by
  simpa only [S.semigroupFormDom_zero] using
    S.hasDerivWithinAt_entropy_semigroup_Ici hε hεM u hu (t := 0) le_rfl

end ErrorCalculus.ErrorStructure
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem hasDerivWithinAt_integral_rpow_var {ε M : ℝ} (hε : 0 < ε)
    (v : ℝ → Lp ℝ 2 μ) (hv : ∀ s, ∀ᵐ ω ∂μ, v s ω ∈ Icc ε M)
    {s : Set ℝ} {q : ℝ → ℝ} {q' d t : ℝ} (hq : HasDerivWithinAt q q' s t)
    (hc : ContinuousWithinAt v s t)
    (hd : HasDerivWithinAt (fun s => ∫ ω, (v s ω)^(q t) ∂μ) d s t) :
    HasDerivWithinAt (fun s => ∫ ω, (v s ω)^(q s) ∂μ)
      (q' * (∫ ω, (v t ω)^(q t)*Real.log (v t ω) ∂μ) + d) s t := by
  have hm (s : ℝ) := exists_mean_derivative
    (hasDerivAt_integral_rpow_exponent hε (v s) (hv s)) (q t) (q s)
  choose r hr he using hm
  have hrt : Tendsto r (𝓝[s] t) (𝓝 (q t)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _)
      (Eventually.of_forall fun s => abs_sub_left_of_mem_uIcc (hr s))
    simpa only [sub_self, abs_zero] using (hq.continuousWithinAt.sub_const (q t)).abs
  have hlog := tendsto_integral_rpow_log_confined hε hc hrt
    (Eventually.of_forall hv) (hv t)
  have ht := ((hasDerivWithinAt_iff_tendsto_slope.mp hq).mul (hlog.mono_left (nhdsWithin_mono _ sdiff_subset))).add (hasDerivWithinAt_iff_tendsto_slope.mp hd)
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
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

theorem hasDerivWithinAt_integral_rpow_semigroup_var_zero {ε M : ℝ}
    (hε : 0 < ε) (hεM : ε ≤ M) (u : S.generatorDom)
    (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M)
    {q : ℝ → ℝ} {q' : ℝ} (hq : HasDerivWithinAt q q' (Ici 0) 0) (hq1 : 1 < q 0) :
    HasDerivWithinAt (fun s => ∫ ω, (S.semigroup s u ω)^(q s) ∂μ)
      (q' * (∫ ω, ((u : Lp ℝ 2 μ) ω)^(q 0)*Real.log ((u : Lp ℝ 2 μ) ω) ∂μ) -
        (4*(q 0-1)/(q 0)) * S.energy.E
          (S.powComp hε hεM (q 0/2) (S.generatorForm u))
          (S.powComp hε hεM (q 0/2) (S.generatorForm u))) (Ici 0) 0 := by
  let v := fun s : ℝ => S.semigroup (max s 0) u
  have hv (s : ℝ) : ∀ᵐ ω ∂μ, v s ω ∈ Icc ε M :=
    S.semigroup_mem_Icc (le_max_right _ _) u hu
  have he (s : ℝ) (hs : s ∈ Ici 0) : v s = S.semigroup s u := by
    simp only [v, max_eq_left (show 0 ≤ s from hs)]
  have hz : v 0 = (u : Lp ℝ 2 μ) := by simp [v, semigroup]
  have hc : ContinuousWithinAt v (Ici 0) 0 :=
    (S.hasDerivWithinAt_semigroup_Ici u (t := 0) le_rfl).continuousWithinAt.congr
      he (he 0 (by simp))
  have hd := (S.hasDerivWithinAt_integral_pow_semigroup_Ici hε hεM hq1 u hu
    (t := 0) le_rfl).congr
      (fun s hs => congrArg (fun w : Lp ℝ 2 μ => ∫ ω, (w ω)^(q 0) ∂μ) (he s hs))
      (congrArg (fun w : Lp ℝ 2 μ => ∫ ω, (w ω)^(q 0) ∂μ) (he 0 (by simp)))
  have hh := hasDerivWithinAt_integral_rpow_var hε v hv hq hc hd
  rw [hz, S.semigroupFormDom_zero] at hh
  have hh' := hh.congr (fun s hs => by rw [he s hs]) (by rw [he 0 (by simp)])
  simpa only [neg_mul, sub_eq_add_neg] using hh'

theorem hasDerivWithinAt_grossLogNorm_zero {ε M c p : ℝ}
    (hε : 0 < ε) (hεM : ε ≤ M) (hp : 1 < p) (u : S.generatorDom)
    (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc ε M) :
    HasDerivWithinAt (S.grossLogNorm c p u)
      ((4*(p-1)/c * entropy μ (fun ω => ((u : Lp ℝ 2 μ) ω)^p) -
        4*(p-1) * S.energy.E (S.powComp hε hεM (p/2) (S.generatorForm u))
          (S.powComp hε hεM (p/2) (S.generatorForm u))) /
        (p^2 * ∫ ω, ((u : Lp ℝ 2 μ) ω)^p ∂μ)) (Ici 0) 0 := by
  have hp0 : p ≠ 0 := by linarith
  have hΛ := integral_rpow_pos hε (u : Lp ℝ 2 μ) hu p
  have hd := S.hasDerivWithinAt_integral_rpow_semigroup_var_zero hε hεM u hu
    (hasDerivAt_grossExponent c p 0).hasDerivWithinAt (by simpa using hp)
  have hh := (hd.log (by simpa [semigroup] using ne_of_gt hΛ)).div
    (hasDerivAt_grossExponent c p 0).hasDerivWithinAt (by simpa using hp0)
  simp only [grossExponent_zero, semigroup, QuadForm.semigroup_zero,
    one_apply_eq_self] at hh
  convert! hh using 1
  rw [entropy_rpow_eq hε (u : Lp ℝ 2 μ) hu]
  field_simp
  ring

omit [IsProbabilityMeasure μ] in
/-- At a contact point, ordered functions have ordered right derivatives. -/
theorem le_of_hasDerivWithinAt_Ici_of_le {g h : ℝ → ℝ} {a b : ℝ}
    (hg : HasDerivWithinAt g a (Ici 0) 0) (hh : HasDerivWithinAt h b (Ici 0) 0)
    (h0 : g 0 = h 0) (hle : ∀ t ≥ 0, g t ≤ h t) : a ≤ b := by
  have hg' := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Ioi 0)).mp hg.Ioi_of_Ici
  have hh' := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Ioi 0)).mp hh.Ioi_of_Ici
  apply le_of_tendsto_of_tendsto hg' hh'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [slope_fun_def_field, sub_zero, h0]
  exact div_le_div_of_nonneg_right (sub_le_sub_right (hle t ht.le) _) ht.le

end ErrorStructure
end ErrorCalculus
