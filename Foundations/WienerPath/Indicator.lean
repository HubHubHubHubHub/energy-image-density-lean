import Foundations.WienerPath.Integral

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal
namespace Foundations

def schauderRandomPartial (N : ℕ) (t : WienerTime) : Lp ℝ 2 schauderGaussianMeasure :=
  ∑ i ∈ schauderIndices N, schauderCoefficient i t • schauderGaussianCoordinate i

theorem coe_schauderRandomPartial (N : ℕ) (t : WienerTime) :
    schauderRandomPartial N t =ᵐ[schauderGaussianMeasure] fun x => schauderPartial N x t := by
  have hi (i : SchauderIndex) :
      (schauderCoefficient i t • schauderGaussianCoordinate i : Lp ℝ 2 schauderGaussianMeasure)
        =ᵐ[schauderGaussianMeasure] fun x => x i * schauderCoefficient i t := by
    filter_upwards [Lp.coeFn_smul (schauderCoefficient i t) (schauderGaussianCoordinate i),
      coe_schauderGaussianCoordinate i] with x hx hy
    simp only [hx,Pi.smul_apply,smul_eq_mul,hy,mul_comm]
  filter_upwards [Lp.coeFn_finsetSum (schauderIndices N)
    (fun i => schauderCoefficient i t • schauderGaussianCoordinate i), ae_all_iff.mpr hi] with x hx hi
  change (∑ i ∈ schauderIndices N, _ : Lp ℝ 2 schauderGaussianMeasure) x = _
  rw [hx,schauderPartial_apply]
  simp only [Finset.sum_apply,gaussianSeriesPartial]
  exact Finset.sum_congr rfl (fun i _ => hi i)

theorem tendsto_schauderRandomPartial (t : WienerTime) :
    Tendsto (fun N => schauderRandomPartial N t) atTop
      (𝓝 (wienerIntegralSchauder (haarBasis.repr (haarIndicator t)))) := by
  have h := (hasSum_wienerIntegralSchauder (haarBasis.repr (haarIndicator t))).comp
    tendsto_schauderIndices
  simpa only [Function.comp_def,haarBasis_repr_indicator,schauderRandomPartial] using h

theorem wienerIntegralSchauder_indicator_ae (t : WienerTime) :
    wienerIntegralSchauder (haarBasis.repr (haarIndicator t)) =ᵐ[schauderGaussianMeasure]
      fun x => schauderMap x t := by
  obtain ⟨ns,hns,hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (tendsto_schauderRandomPartial t)).exists_seq_tendsto_ae
  filter_upwards [hae,ae_mem_schauderGoodSet,
    ae_all_iff.mpr (fun n => coe_schauderRandomPartial n t)] with x hx hgood he
  have hp := (((ContinuousMap.evalCLM ℝ t).continuous.tendsto _).comp
    (tendsto_schauderPartial hgood)).comp hns.tendsto_atTop
  exact tendsto_nhds_unique hx (by simpa only [Function.comp_def,he,
    ContinuousMap.evalCLM_apply] using hp)

theorem wienerIntegralPath_indicator_ae (t : WienerTime) :
    wienerIntegralPath (haarIndicator t) =ᵐ[wienerMeasure] canonicalProcess t := by
  filter_upwards [coe_wienerIntegralPath (haarIndicator t),
    measurePreserving_schauderCoordinate.quasiMeasurePreserving.ae
      (wienerIntegralSchauder_indicator_ae t),schauderMap_schauderCoordinate_ae] with ω h1 h2 h3
  rw [h1,h2,h3,canonicalProcess_apply]

theorem memLp_canonicalProcess (t : WienerTime) : MemLp (canonicalProcess t) 2 wienerMeasure :=
  (memLp_congr_ae (wienerIntegralPath_indicator_ae t)).mp (Lp.memLp _)

def canonicalProcessLp (t : WienerTime) : Lp ℝ 2 wienerMeasure :=
  (memLp_canonicalProcess t).toLp (canonicalProcess t)

theorem wienerIntegralPath_indicator (t : WienerTime) :
    wienerIntegralPath (haarIndicator t) = canonicalProcessLp t := by
  apply Lp.ext
  filter_upwards [wienerIntegralPath_indicator_ae t,(memLp_canonicalProcess t).coeFn_toLp] with ω h1 h2
  exact h1.trans h2.symm

end Foundations
