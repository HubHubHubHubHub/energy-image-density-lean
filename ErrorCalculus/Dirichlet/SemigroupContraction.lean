import ErrorCalculus.Dirichlet.SemigroupJensen
import ErrorCalculus.Dirichlet.ProductRule

/-!
# Semigroup Contraction

## Main results
Conservation of mass and Lᵖ contractions.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

theorem semigroup_selfAdjoint {t : ℝ} (ht : 0 ≤ t) :
    IsSelfAdjoint (S.semigroup t) :=
  S.energy.semigroup_selfAdjoint S.energy_closed S.dense ht

theorem semigroup_symm {t : ℝ} (ht : 0 ≤ t) (f g : Lp ℝ 2 μ) :
    inner ℝ (S.semigroup t f) g = inner ℝ f (S.semigroup t g) :=
  S.energy.semigroup_symm S.energy_closed S.dense ht f g

theorem integral_semigroup {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 μ) :
    ∫ ω, S.semigroup t f ω ∂μ = ∫ ω, f ω ∂μ := by
  have h := S.semigroup_symm ht f (Lp.const 2 μ 1)
  rw [S.semigroup_const_one ht] at h
  have hi (g : Lp ℝ 2 μ) : inner ℝ g (Lp.const 2 μ 1) = ∫ ω, g ω ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with ω hc
    simp [RCLike.inner_apply]
  simpa only [hi] using h

theorem semigroup_ae_bound {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 μ)
    {C : ℝ} (hf : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C) :
    ∀ᵐ ω ∂μ, ‖S.semigroup t f ω‖ ≤ C := by
  have h := S.semigroup_mono ht (f := absLp f) (g := Lp.const 2 μ C) (by
    filter_upwards [hf, coeFn_absLp f,
      Lp.coeFn_const (p := 2) (μ := μ) (c := C)] with ω hf ha hc
    simpa only [ha, hc, Function.const_apply, Real.norm_eq_abs] using hf)
  rw [S.semigroup_const ht] at h
  filter_upwards [h, S.semigroup_abs_le ht f,
    Lp.coeFn_const (p := 2) (μ := μ) (c := C)] with ω h ha hc
  simpa only [Real.norm_eq_abs, hc, Function.const_apply] using ha.trans h

theorem aeBounded_semigroup {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 μ)
    (hf : AEBounded (μ := μ) f) : AEBounded (μ := μ) (S.semigroup t f) :=
  ⟨hf.choose, S.semigroup_ae_bound ht f hf.choose_spec⟩

/-- The extended-norm inequality also covers unbounded L² data. -/
theorem eLpNorm_semigroup_top_le {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 μ) :
    eLpNorm (S.semigroup t f) ∞ μ ≤ eLpNorm f ∞ μ := by
  by_cases hf : eLpNorm f ∞ μ = ∞
  · simp [hf]
  have hb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ (eLpNorm f ∞ μ).toReal := by
    filter_upwards [ae_le_eLpNormEssSup (f := (f : Ω → ℝ)) (μ := μ)] with ω h
    exact (ENNReal.toReal_mono hf h).trans_eq (by simp)
  have h := eLpNormEssSup_le_of_ae_bound (S.semigroup_ae_bound ht f hb)
  change eLpNorm (S.semigroup t f) ∞ μ ≤ ENNReal.ofReal (eLpNorm f ∞ μ).toReal at h
  rwa [ENNReal.ofReal_toReal hf] at h

theorem integral_abs_semigroup_le {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 μ) :
    ∫ ω, |S.semigroup t f ω| ∂μ ≤ ∫ ω, |f ω| ∂μ := by
  calc
    _ ≤ ∫ ω, S.semigroup t (absLp f) ω ∂μ :=
      integral_mono_ae ((Lp.memLp _).integrable (by norm_num)).abs
        ((Lp.memLp _).integrable (by norm_num)) (S.semigroup_abs_le ht f)
    _ = ∫ ω, absLp f ω ∂μ := S.integral_semigroup ht _
    _ = _ := integral_congr_ae (coeFn_absLp f)

theorem eLpNorm_semigroup_one_le {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 μ) :
    eLpNorm (S.semigroup t f) 1 μ ≤ eLpNorm f 1 μ := by
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm ((Lp.memLp (S.semigroup t f)).integrable (by norm_num)),
    ← ofReal_integral_norm_eq_lintegral_enorm ((Lp.memLp f).integrable (by norm_num))]
  simp only [Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (S.integral_abs_semigroup_le ht f)

/-- Integration of Jensen for the absolute real power. -/
theorem integral_abs_pow_semigroup_le {t p : ℝ} (ht : 0 ≤ t) (hp : 1 ≤ p)
    (f : Lp ℝ 2 μ) (hf : AEBounded (μ := μ) f) :
    ∫ ω, |S.semigroup t f ω| ^ p ∂μ ≤ ∫ ω, |f ω| ^ p ∂μ := by
  have hc : Continuous (fun x : ℝ => |x| ^ p) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp continuous_abs
  let hpow := memLp_continuous_comp_of_aeBounded hc f hf 2
  have hout := memLp_continuous_comp_of_aeBounded hc (S.semigroup t f)
    (S.aeBounded_semigroup ht f hf) 1
  calc
    _ ≤ ∫ ω, S.semigroup t (hpow.toLp _) ω ∂μ :=
      integral_mono_ae (memLp_one_iff_integrable.mp hout)
        ((Lp.memLp _).integrable (by norm_num)) (S.semigroup_abs_pow_le ht hp f hpow)
    _ = ∫ ω, hpow.toLp _ ω ∂μ := S.integral_semigroup ht _
    _ = _ := integral_congr_ae hpow.coeFn_toLp

/-- Lᵖ contraction for every finite exponent p≥1 on bounded L² data. -/
theorem eLpNorm_semigroup_le {t : ℝ} (ht : 0 ≤ t) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpfin : p ≠ ∞) (f : Lp ℝ 2 μ) (hf : AEBounded (μ := μ) f) :
    eLpNorm (S.semigroup t f) p μ ≤ eLpNorm f p μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpfin hp
  have hfp : MemLp (f : Ω → ℝ) p μ :=
    (hf.memLp_top (Lp.aestronglyMeasurable f)).mono_exponent le_top
  have htp : MemLp (S.semigroup t f : Ω → ℝ) p μ :=
    ((S.aeBounded_semigroup ht f hf).memLp_top (Lp.aestronglyMeasurable _)).mono_exponent le_top
  rw [MemLp.eLpNorm_eq_integral_rpow_norm hp0 hpfin htp,
    MemLp.eLpNorm_eq_integral_rpow_norm hp0 hpfin hfp]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow
  · exact integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  · simpa only [Real.norm_eq_abs] using S.integral_abs_pow_semigroup_le ht hpr f hf
  · positivity

/-- Norm decay needs only the semigroup law and Lᵖ contraction. -/
theorem eLpNorm_semigroup_antitone {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ∞)
    (f : Lp ℝ 2 μ) (hf : AEBounded (μ := μ) f) :
    AntitoneOn (fun t : ℝ => eLpNorm (S.semigroup t f) p μ) (Set.Ici 0) := by
  intro s hs t ht hst
  have hh := S.eLpNorm_semigroup_le (sub_nonneg.mpr hst) hp hpfin
    (S.semigroup s f) (S.aeBounded_semigroup hs f hf)
  have he : S.semigroup (t-s) (S.semigroup s f) = S.semigroup t f := by
    change S.energy.semigroup S.energy_closed S.dense (t-s)
      (S.energy.semigroup S.energy_closed S.dense s f) = _
    rw [← mul_apply_eq_comp, ← S.energy.semigroup_add S.energy_closed S.dense
      (sub_nonneg.mpr hst) hs, sub_add_cancel]
    rfl
  rwa [he] at hh

end ErrorCalculus.ErrorStructure
