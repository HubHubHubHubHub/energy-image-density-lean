import Foundations.CameronMartin.WienerIntegral
import Foundations.GaussianSeries.Limit
import Mathlib.Probability.Independence.InfinitePi

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace Topology
namespace Foundations

theorem hasLaw_gaussianCoordinateFun (i : ℕ) :
    HasLaw (fun x : ℕ → ℝ => x i) (gaussianReal 0 1) gaussianInf :=
  ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval_infinitePi (fun _ : ℕ => standardGaussian) i).map_eq⟩

theorem iIndepFun_gaussianCoordinateFun :
    iIndepFun (fun i (x : ℕ → ℝ) => x i) gaussianInf :=
  iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (by fun_prop)

theorem charFun_wienerPartial (a : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) :
    charFun (gaussianInf.map (wienerPartial a s)) t =
      Complex.exp (-((cameronMartinEnergy a s * t^2 : ℝ) : ℂ)/2) := by
  rw [Measure.map_congr (coe_wienerPartial a s)]
  rw [show wienerPartialFun a s = (fun x => ∑ i ∈ s, a i * x i) from rfl,
    charFun_gaussian_weighted_sum iIndepFun_gaussianCoordinateFun hasLaw_gaussianCoordinateFun]
  congr 3
  simp [cameronMartinEnergy, mul_pow, Finset.sum_mul]

theorem wienerPartial_map (a : ℕ → ℝ) (s : Finset ℕ) :
    gaussianInf.map (wienerPartial a s) =
      gaussianReal 0 (NNReal.mk (cameronMartinEnergy a s) (cameronMartinEnergy_nonneg a s)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_wienerPartial, charFun_gaussianReal]
  congr 1
  simp only [NNReal.coe_mk,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_zero,mul_zero,zero_mul,zero_sub]
  change -((cameronMartinEnergy a s : ℂ) * (t:ℂ)^2)/2 = -((cameronMartinEnergy a s : ℂ) * (t:ℂ)^2/2)
  ring

theorem wienerIntegral_map (a : CameronMartinSpace) :
    gaussianInf.map (wienerIntegral a) = gaussianReal 0 (NNReal.mk (‖a‖^2) (sq_nonneg _)) := by
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (tendsto_wienerPartial a)).exists_seq_tendsto_ae
  apply Measure.ext_of_charFun
  funext t
  have hlim := tendsto_charFun_map_of_ae_tendsto
    (fun n => (Lp.aestronglyMeasurable (wienerPartial a (Finset.range (ns n)))).aemeasurable) hae t
  simp_rw [charFun_wienerPartial] at hlim
  have hc : Continuous (fun r : ℝ => Complex.exp (-((r*t^2 : ℝ):ℂ)/2)) := by fun_prop
  have hh := hc.continuousAt.tendsto.comp
    ((tendsto_cameronMartinEnergy a).comp hns.tendsto_atTop)
  rw [tendsto_nhds_unique hlim hh, charFun_gaussianReal]
  congr 1
  simp only [NNReal.coe_mk,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_zero,mul_zero,zero_mul,zero_sub]
  change -(((‖a‖:ℝ):ℂ)^2 * (t:ℂ)^2)/2 = -(((‖a‖:ℝ):ℂ)^2 * (t:ℂ)^2/2)
  ring

end Foundations
