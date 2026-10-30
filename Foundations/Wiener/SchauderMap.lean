import Foundations.Wiener.PathSpace

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Classical

namespace Foundations

/-- The uniform limit on the Cauchy set, and the zero path elsewhere. -/
noncomputable def schauderMap (ξ : SchauderIndex → ℝ) : PathSpace :=
  if ξ ∈ schauderGoodSet then limUnder atTop (fun N => schauderPartial N ξ) else 0

theorem tendsto_schauderPartial {ξ : SchauderIndex → ℝ} (hξ : ξ ∈ schauderGoodSet) :
    Tendsto (fun N => schauderPartial N ξ) atTop (𝓝 (schauderMap ξ)) := by
  simpa [schauderMap, hξ] using tendsto_nhds_limUnder ((mem_schauderGoodSet_iff ξ).mp hξ)

theorem schauderMap_eq_zero {ξ : SchauderIndex → ℝ} (hξ : ξ ∉ schauderGoodSet) :
    schauderMap ξ = 0 := by simp [schauderMap, hξ]

theorem measurable_schauderMap : Measurable schauderMap := by
  classical
  apply measurable_of_tendsto_metrizable
    (f := fun N ξ => if ξ ∈ schauderGoodSet then schauderPartial N ξ else 0)
  · intro N
    exact Measurable.ite measurableSet_schauderGoodSet
      (continuous_schauderPartial N).measurable measurable_const
  · apply tendsto_pi_nhds.mpr
    intro ξ
    by_cases hξ : ξ ∈ schauderGoodSet
    · simpa only [if_pos hξ] using tendsto_schauderPartial hξ
    · simp only [if_neg hξ, schauderMap_eq_zero hξ]
      exact tendsto_const_nhds

/-- The Haar–Schauder partial sums converge almost surely as continuous paths. -/
theorem ae_schauderPartial_limit : ∀ᵐ ξ ∂schauderGaussianMeasure,
    ∃ f : PathSpace, Tendsto (fun N => schauderPartial N ξ) atTop (𝓝 f) ∧
      ∀ t : WienerTime, f t = schauderSeriesLimit (fun i ω => ω i) t ξ := by
  have hU := ae_tendstoUniformlyOn_schauder_series
    (fun i => (measurePreserving_eval_infinitePi
      (fun _ : SchauderIndex => gaussianReal 0 1) i).hasLaw)
  filter_upwards [hU, isBrownianOn_schauderSeriesLimit_infinitePi.2] with ξ hU hC
  refine ⟨⟨_, hC.restrict⟩, ?_, fun _ => rfl⟩
  apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
  simp only [schauderPartial_apply]
  convert! tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hU using 1

theorem ae_mem_schauderGoodSet : ∀ᵐ ξ ∂schauderGaussianMeasure, ξ ∈ schauderGoodSet := by
  filter_upwards [ae_schauderPartial_limit] with ξ hξ
  exact (mem_schauderGoodSet_iff ξ).mpr ⟨hξ.choose, hξ.choose_spec.1⟩

theorem schauderGaussianMeasure_schauderGoodSet :
    schauderGaussianMeasure schauderGoodSet = 1 := by
  rw [← measure_univ (μ := schauderGaussianMeasure)]
  apply measure_congr
  filter_upwards [ae_mem_schauderGoodSet] with ξ hξ
  exact propext (iff_of_true hξ (mem_univ ξ))

/-- One null set works for all times in the interval. -/
theorem schauderMap_apply_ae : ∀ᵐ ξ ∂schauderGaussianMeasure, ∀ t : WienerTime,
    schauderMap ξ t = schauderSeriesLimit (fun i ω => ω i) t ξ := by
  filter_upwards [ae_schauderPartial_limit, ae_mem_schauderGoodSet] with ξ hξ hG
  obtain ⟨f, hf, hval⟩ := hξ
  have heq := tendsto_nhds_unique (tendsto_schauderPartial hG) hf
  exact fun t => heq ▸ hval t

/-- Wiener measure on the Borel space of continuous paths. -/
noncomputable def wienerMeasure : Measure PathSpace :=
  schauderGaussianMeasure.map schauderMap

theorem measurePreserving_schauderMap :
    MeasurePreserving schauderMap schauderGaussianMeasure wienerMeasure :=
  ⟨measurable_schauderMap, rfl⟩

instance isProbabilityMeasure_wienerMeasure : IsProbabilityMeasure wienerMeasure :=
  Measure.isProbabilityMeasure_map measurable_schauderMap.aemeasurable

/-- The coordinate process under Wiener measure is Brownian on the unit interval. -/
theorem isBrownianOn_canonical :
    IsBrownianOn (Icc 0 1) canonicalProcess wienerMeasure := by
  refine ⟨?_, Filter.Eventually.of_forall fun ω => (continuous_canonicalPath ω).continuousOn⟩
  intro I hI
  have hm : Measurable (fun ω : PathSpace => I.restrict (canonicalProcess · ω)) :=
    measurable_pi_lambda _ fun t => (continuous_canonicalProcess t).measurable
  refine ⟨hm.aemeasurable, ?_⟩
  rw [wienerMeasure, Measure.map_map hm measurable_schauderMap]
  have heq : (fun ξ => I.restrict (canonicalProcess · (schauderMap ξ))) =ᵐ[schauderGaussianMeasure]
      (fun ξ => I.restrict (schauderSeriesLimit (fun i ω => ω i) · ξ)) := by
    filter_upwards [schauderMap_apply_ae] with ξ hξ
    funext t
    simpa [Finset.restrict, canonicalProcess, min_eq_left (hI t.property).2] using
      hξ ⟨t, hI t.property⟩
  simpa only [Function.comp_def] using
    (Measure.map_congr heq).trans (isBrownianOn_schauderSeriesLimit_infinitePi.1 I hI).map_eq

end Foundations
