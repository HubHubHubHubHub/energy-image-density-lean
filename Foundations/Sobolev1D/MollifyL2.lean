import Foundations.Sobolev1D.Mollify
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
open MeasureTheory Filter Set Function Metric ContinuousLinearMap
open scoped Topology ENNReal ContDiff Convolution Pointwise
namespace Foundations

/-- Jensen for the square, proved by expanding a nonnegative variance. -/
theorem sq_integral_weight_le {φ f : ℝ → ℝ} (hφ : Integrable φ volume)
    (hf : Integrable (fun t => φ t * f t) volume)
    (hf₂ : Integrable (fun t => φ t * (f t)^2) volume)
    (hpos : ∀ t, 0 ≤ φ t) (hmass : ∫ t, φ t = 1) :
    (∫ t, φ t * f t)^2 ≤ ∫ t, φ t * (f t)^2 := by
  let m := ∫ t, φ t * f t
  have he : (∫ t, φ t * (f t-m)^2) = (∫ t, φ t * (f t)^2) - m^2 := by
    calc
      _ = ∫ t, (φ t * (f t)^2 - (2*m)*(φ t*f t)) + m^2*φ t := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by ring)
      _ = _ := by
        have hs : Integrable (fun t => φ t * (f t)^2 - (2*m)*(φ t*f t)) volume :=
          hf₂.sub (hf.const_mul (2*m))
        rw [integral_add hs (hφ.const_mul (m^2)),
          integral_sub hf₂ (hf.const_mul (2*m)), integral_const_mul, integral_const_mul, hmass]
        dsimp [m]
        ring
  have hn : 0 ≤ ∫ t, φ t * (f t-m)^2 := integral_nonneg (fun t => mul_nonneg (hpos t) (sq_nonneg _))
  rw [he] at hn
  dsimp [m] at hn
  linarith

theorem sq_mollify_le {f : ℝ → ℝ} (hf : MemLp f 2 volume) (n : ℕ) (x : ℝ) :
    (mollify f n x)^2 ≤ ((mollifier n).normed volume ⋆[lsmul ℝ ℝ, volume] (fun t => (f t)^2)) x := by
  rw [mollify_eq_left]
  exact sq_integral_weight_le (mollifier n).integrable_normed
    ((mollifier n).hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      (mollifier n).continuous_normed (hf.locallyIntegrable (by norm_num)) x)
    ((mollifier n).hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      (mollifier n).continuous_normed hf.integrable_sq.locallyIntegrable x)
    (mollifier n).nonneg_normed (mollifier n).integral_normed

theorem memLp_mollify {f : ℝ → ℝ} (hf : MemLp f 2 volume) (n : ℕ) :
    MemLp (mollify f n) 2 volume := by
  have hm : AEStronglyMeasurable (mollify f n) volume := (contDiff_mollify (hf.locallyIntegrable (by norm_num)) n).continuous.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  have hi := (mollifier n).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hf.integrable_sq
  apply hi.mono' (hm.pow 2)
  exact Eventually.of_forall (fun x => by
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (mollify f n x))] using sq_mollify_le hf n x)

/-- Young's contraction inequality for these nonnegative normalized kernels in L². -/
theorem norm_mollify_L2_le {f : ℝ → ℝ} (hf : MemLp f 2 volume) (n : ℕ) :
    ‖(memLp_mollify hf n).toLp (mollify f n)‖ ≤ ‖hf.toLp f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_toLp_sq, norm_toLp_sq]
  calc
    _ ≤ ∫ x, ((mollifier n).normed volume ⋆[lsmul ℝ ℝ, volume] (fun t => (f t)^2)) x :=
      integral_mono (memLp_mollify hf n).integrable_sq
        ((mollifier n).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hf.integrable_sq)
        (sq_mollify_le hf n)
    _ = ∫ t, (f t)^2 := by
      rw [integral_convolution (lsmul ℝ ℝ) (mollifier n).integrable_normed hf.integrable_sq,
        (mollifier n).integral_normed]
      simp

theorem mollify_sub {f g : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (n : ℕ) : mollify (f-g) n = mollify f n - mollify g n := by
  ext x
  have hi₁ := ((mollifier n).hasCompactSupport_normed (μ := volume)).convolutionExists_right (μ := volume) (lsmul ℝ ℝ)
    hf (mollifier n).continuous_normed x
  have hi₂ := ((mollifier n).hasCompactSupport_normed (μ := volume)).convolutionExists_right (μ := volume) (lsmul ℝ ℝ)
    hg (mollifier n).continuous_normed x
  simp only [mollify, convolution_def, lsmul_apply, smul_eq_mul, Pi.sub_apply, sub_mul]
  exact integral_sub hi₁ hi₂

theorem norm_mollify_sub_L2_le {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (n : ℕ) :
    ‖(memLp_mollify hf n).toLp (mollify f n) - (memLp_mollify hg n).toLp (mollify g n)‖ ≤
      ‖hf.toLp f - hg.toLp g‖ := by
  have he : (memLp_mollify (hf.sub hg) n).toLp (mollify (f-g) n) =
      (memLp_mollify hf n).toLp (mollify f n) - (memLp_mollify hg n).toLp (mollify g n) := by
    apply Lp.ext
    filter_upwards [(memLp_mollify (hf.sub hg) n).coeFn_toLp,
      Lp.coeFn_sub ((memLp_mollify hf n).toLp _) ((memLp_mollify hg n).toLp _),
      (memLp_mollify hf n).coeFn_toLp, (memLp_mollify hg n).coeFn_toLp] with x hx hx₀ hx₁ hx₂
    rw [hx, hx₀, Pi.sub_apply, hx₁, hx₂, mollify_sub (hf.locallyIntegrable (by norm_num)) (hg.locallyIntegrable (by norm_num))]
    rfl
  rw [← he, ← hf.toLp_sub hg]
  exact norm_mollify_L2_le (hf.sub hg) n

theorem memLp_mollify_compact (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
    {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (n : ℕ) :
    MemLp (mollify f n) 2 μ :=
  (contDiff_mollify hf.locallyIntegrable n).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_mollify hc n)

/-- The continuous compactly supported case, for any locally finite measure. -/
theorem tendsto_L2_mollify_continuous (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
    {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun n => (memLp_mollify_compact μ hf hc n).toLp (mollify f n)) atTop
      (𝓝 ((hf.memLp_of_hasCompactSupport hc : MemLp f 2 μ).toLp f)) := by
  let K := tsupport f + closedBall (0 : ℝ) 1
  have hK : IsCompact K := hc.isCompact.add (isCompact_closedBall _ _)
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hf
  have hM₀ : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  have hb : MemLp (K.indicator (fun _ => M)) 2 μ :=
    memLp_indicator_const 2 hK.measurableSet M (Or.inr hK.measure_lt_top.ne)
  apply tendsto_toLp_dominated μ _ _ hb
  · intro n
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ K
    · simpa only [indicator_of_mem hx] using norm_mollify_le hf.aestronglyMeasurable hM₀ hM n x
    · have hz : mollify f n x = 0 := notMem_support.mp (fun hs => hx (support_mollify_subset f n hs))
      simp only [hz, norm_zero, indicator_of_notMem hx, le_refl]
  · exact Eventually.of_forall (fun x =>
      (tendstoUniformly_mollify (hc.uniformContinuous_of_continuous hf)).tendsto_at x)

/-- Approximation of the identity in L², by compact continuous density and contraction. -/
theorem tendsto_L2_mollify {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun n => (memLp_mollify hf n).toLp (mollify f n)) atTop (𝓝 (hf.toLp f)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g,hgc,hclose,hg,hgLp⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num)
    (ε := ENNReal.ofReal (ε/4)) (by positivity)
  have hfg : ‖hf.toLp f - hgLp.toLp g‖ ≤ ε/4 := by
    rw [← hf.toLp_sub hgLp, Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hclose).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have ht := tendsto_L2_mollify_continuous volume hg hgc
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (ε/2) (half_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hmid : ‖(memLp_mollify hgLp n).toLp (mollify g n) - hgLp.toLp g‖ < ε/2 := by
    simpa only [dist_eq_norm] using hN n hn
  rw [dist_eq_norm]
  have htri := dist_triangle ((memLp_mollify hf n).toLp (mollify f n))
    ((memLp_mollify hgLp n).toLp (mollify g n)) (hf.toLp f)
  have htri₂ := dist_triangle ((memLp_mollify hgLp n).toLp (mollify g n)) (hgLp.toLp g) (hf.toLp f)
  simp only [dist_eq_norm] at htri htri₂
  have h₁ := norm_mollify_sub_L2_le hf hgLp n
  have h₂ : ‖hgLp.toLp g - hf.toLp f‖ ≤ ε/4 := by simpa only [norm_sub_rev] using hfg
  linarith

end Foundations
