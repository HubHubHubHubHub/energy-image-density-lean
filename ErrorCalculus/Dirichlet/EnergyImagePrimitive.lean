import ErrorCalculus.Dirichlet.PiecewiseChain
import Mathlib.MeasureTheory.Measure.Regular

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal Convolution
namespace ErrorCalculus.ErrorStructure

/-- The primitive of the indicator, anchored at zero. -/
def primitiveIndicator (O : Set ℝ) (x : ℝ) : ℝ :=
  ∫ t in 0..x, O.indicator (fun _ => (1 : ℝ)) t

theorem indicator_one_mem_Icc (O : Set ℝ) (x : ℝ) :
    O.indicator (fun _ => (1 : ℝ)) x ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases hx : x ∈ O <;> simp [hx]

theorem locallyIntegrable_indicator_one {O : Set ℝ} (hO : MeasurableSet O) :
    LocallyIntegrable (O.indicator (fun _ => (1 : ℝ))) volume := by
  apply locallyIntegrable_iff.mpr
  intro k hk
  apply IntegrableOn.of_bound hk.measure_lt_top
    ((measurable_const.indicator hO).aestronglyMeasurable) 1
  exact ae_of_all _ fun x => by
    rw [Real.norm_of_nonneg (indicator_one_mem_Icc O x).1]
    exact (indicator_one_mem_Icc O x).2

theorem intervalIntegrable_indicator_one {O : Set ℝ} (hO : MeasurableSet O) (a b : ℝ) :
    IntervalIntegrable (O.indicator (fun _ => (1 : ℝ))) volume a b :=
  intervalIntegrable_iff.mpr ((locallyIntegrable_indicator_one hO).integrableOn_isCompact
    isCompact_uIcc |>.mono_set Set.uIoc_subset_uIcc)

theorem lipschitzWith_one_primitiveIndicator {O : Set ℝ} (hO : MeasurableSet O) :
    LipschitzWith 1 (primitiveIndicator O) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_one, one_mul, primitiveIndicator]
  rw [intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_indicator_one hO 0 x) (intervalIntegrable_indicator_one hO 0 y)]
  simpa only [one_mul, Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := y) (b := x) (C := (1 : ℝ))
      (f := O.indicator (fun _ => (1 : ℝ))) (fun t _ => by
        rw [Real.norm_of_nonneg (indicator_one_mem_Icc O t).1]
        exact (indicator_one_mem_Icc O t).2)

/-- The unsmoothed primitive has derivative one at every point of the open set.
This pointwise fact makes no assertion about the boundary of the open set. -/
theorem hasDerivAt_primitiveIndicator_of_mem_open {O : Set ℝ} (hO : IsOpen O)
    {x : ℝ} (hx : x ∈ O) : HasDerivAt (primitiveIndicator O) 1 x := by
  have hc : ContinuousAt (O.indicator (fun _ => (1 : ℝ))) x := by
    apply (continuousAt_const (y := (1 : ℝ))).congr
    filter_upwards [hO.mem_nhds hx] with y hy
    simp [hy]
  have hd : HasDerivAt (primitiveIndicator O)
      (O.indicator (fun _ => (1 : ℝ)) x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_indicator_one hO.measurableSet 0 x)
      (measurable_const.indicator hO.measurableSet).stronglyMeasurable.stronglyMeasurableAtFilter hc
  simpa only [Set.indicator_of_mem hx] using hd

theorem abs_primitiveIndicator_le {O : Set ℝ} (hO : MeasurableSet O)
    (hfin : volume O ≠ ∞) (x : ℝ) :
    |primitiveIndicator O x| ≤ (volume O).toReal := by
  have hi : Integrable (O.indicator (fun _ => (1 : ℝ))) volume := by
    apply (integrable_indicator_iff hO).mpr
    exact integrableOn_const hfin
  have hn : (fun t => ‖O.indicator (fun _ => (1 : ℝ)) t‖) =
      O.indicator (fun _ => (1 : ℝ)) := by
    funext t
    exact Real.norm_of_nonneg (indicator_one_mem_Icc O t).1
  calc
    |primitiveIndicator O x| ≤ ∫ t, ‖O.indicator (fun _ => (1 : ℝ)) t‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
        (integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ fun _ => norm_nonneg _) hi.norm)
    _ = (volume O).toReal := by
      rw [hn]
      simpa only [Pi.one_def, Measure.real] using integral_indicator_one (μ := volume) hO

/-- Direct smoothing of the indicator; its primitive never evaluates an a.e. derivative at u. -/
def smoothIndicator (O : Set ℝ) (k : ℕ) : ℝ → ℝ :=
  (lipschitzBump k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    O.indicator (fun _ => (1 : ℝ))

def smoothPrimitive (O : Set ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∫ t in 0..x, smoothIndicator O k t

theorem continuous_smoothIndicator {O : Set ℝ} (hO : MeasurableSet O) (k : ℕ) :
    Continuous (smoothIndicator O k) :=
  ((lipschitzBump k).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ((lipschitzBump k).contDiff_normed (n := 1))
    (locallyIntegrable_indicator_one hO)).continuous

theorem smoothIndicator_integrable {O : Set ℝ} (hO : MeasurableSet O) (k : ℕ) (x : ℝ) :
    Integrable (fun t => (lipschitzBump k).normed volume t *
      O.indicator (fun _ => (1 : ℝ)) (x-t)) :=
  (lipschitzBump k).hasCompactSupport_normed.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (lipschitzBump k).continuous_normed
    (locallyIntegrable_indicator_one hO) x

theorem smoothIndicator_mem_Icc {O : Set ℝ} (hO : MeasurableSet O) (k : ℕ) (x : ℝ) :
    smoothIndicator O k x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg fun t => mul_nonneg ((lipschitzBump k).nonneg_normed t)
      (indicator_one_mem_Icc O (x-t)).1
  · change (∫ t, (lipschitzBump k).normed volume t *
      O.indicator (fun _ => (1 : ℝ)) (x-t)) ≤ 1
    apply le_trans ?_ (le_of_eq ((lipschitzBump k).integral_normed (μ := volume)))
    apply integral_mono (smoothIndicator_integrable hO k x) (lipschitzBump k).integrable_normed
    intro t
    exact mul_le_of_le_one_right ((lipschitzBump k).nonneg_normed t)
      (indicator_one_mem_Icc O (x-t)).2

theorem hasDerivAt_smoothPrimitive {O : Set ℝ} (hO : MeasurableSet O) (k : ℕ) (x : ℝ) :
    HasDerivAt (smoothPrimitive O k) (smoothIndicator O k x) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_smoothIndicator hO k).intervalIntegrable _ _)
    (continuous_smoothIndicator hO k).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_smoothIndicator hO k).continuousAt

theorem deriv_smoothPrimitive {O : Set ℝ} (hO : MeasurableSet O) (k : ℕ) (x : ℝ) :
    deriv (smoothPrimitive O k) x = smoothIndicator O k x :=
  (hasDerivAt_smoothPrimitive hO k x).deriv

theorem deriv_smoothPrimitive_mem_Icc {O : Set ℝ} (hO : MeasurableSet O) (k : ℕ) (x : ℝ) :
    deriv (smoothPrimitive O k) x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [deriv_smoothPrimitive hO]
  exact smoothIndicator_mem_Icc hO k x

theorem contDiff_one_smoothPrimitive {O : Set ℝ} (hO : MeasurableSet O) (k : ℕ) :
    ContDiff ℝ 1 (smoothPrimitive O k) := by
  rw [contDiff_one_iff_deriv]
  exact ⟨fun x => (hasDerivAt_smoothPrimitive hO k x).differentiableAt,
    by simpa only [funext (deriv_smoothPrimitive hO k)] using continuous_smoothIndicator hO k⟩

theorem lipschitzWith_one_smoothPrimitive {O : Set ℝ} (hO : MeasurableSet O) (k : ℕ) :
    LipschitzWith 1 (smoothPrimitive O k) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_smoothPrimitive hO k x).differentiableAt)
  intro x
  change ‖deriv (smoothPrimitive O k) x‖ ≤ (1 : ℝ)
  rw [deriv_smoothPrimitive hO, Real.norm_of_nonneg (smoothIndicator_mem_Icc hO k x).1]
  exact (smoothIndicator_mem_Icc hO k x).2

theorem ae_tendsto_smoothIndicator {O : Set ℝ} (hO : MeasurableSet O) :
    ∀ᵐ x ∂volume, Tendsto (fun k => smoothIndicator O k x) atTop
      (𝓝 (O.indicator (fun _ => (1 : ℝ)) x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := lipschitzBump) (K := 2)
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · filter_upwards [] with k
    change (1/2:ℝ)^k ≤ 2 * (1/2:ℝ)^(k+1)
    rw [pow_succ]
    linarith
  · exact locallyIntegrable_indicator_one hO

theorem tendsto_smoothPrimitive {O : Set ℝ} (hO : MeasurableSet O) (x : ℝ) :
    Tendsto (fun k => smoothPrimitive O k x) atTop (𝓝 (primitiveIndicator O x)) := by
  have ht := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.uIoc 0 x)) (F := fun k => smoothIndicator O k)
    (f := O.indicator (fun _ => (1 : ℝ))) (fun _ => (1 : ℝ))
    (fun k => (continuous_smoothIndicator hO k).aestronglyMeasurable)
    (integrableOn_const (by simp [Real.volume_uIoc])) (fun k => ae_of_all _ fun t => by
      rw [Real.norm_of_nonneg (smoothIndicator_mem_Icc hO k t).1]
      exact (smoothIndicator_mem_Icc hO k t).2)
    (ae_restrict_of_ae (ae_tendsto_smoothIndicator hO))
  simp only [smoothPrimitive, primitiveIndicator, intervalIntegral.intervalIntegral_eq_integral_uIoc]
  exact ht.const_smul _

theorem tendsto_deriv_smoothPrimitive_of_mem {O : Set ℝ} (hO : IsOpen O)
    {x : ℝ} (hx : x ∈ O) :
    Tendsto (fun k => deriv (smoothPrimitive O k) x) atTop (𝓝 1) := by
  have hc : ContinuousAt (O.indicator (fun _ => (1 : ℝ))) x := by
    apply (continuousAt_const (y := (1 : ℝ))).congr
    filter_upwards [hO.mem_nhds hx] with y hy
    simp [hy]
  simp_rw [deriv_smoothPrimitive hO.measurableSet]
  have ht := ContDiffBump.convolution_tendsto_right (φ := lipschitzBump) (μ := volume)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    (Eventually.of_forall fun _ => (measurable_const.indicator hO.measurableSet).aestronglyMeasurable)
    (hc.tendsto.comp tendsto_snd) tendsto_const_nhds
  simpa only [smoothIndicator, Set.indicator_of_mem hx] using ht

end ErrorCalculus.ErrorStructure
