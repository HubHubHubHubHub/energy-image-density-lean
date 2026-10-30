import Foundations.Hermite.Exponential
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

noncomputable section
open Filter Topology Set MeasureTheory ProbabilityTheory
namespace Foundations

theorem integrable_mul_character {f : ℝ → ℝ} (hf : Integrable f standardGaussian) (t : ℝ) :
    Integrable (fun x => (f x : ℂ) * Complex.exp ((t*x : ℝ) * Complex.I)) standardGaussian := by
  have hfm := hf.aestronglyMeasurable
  apply hf.norm.mono' (by fun_prop)
  apply ae_of_all
  intro x
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]

/--
Injectivity on real L¹ densities, via the characteristic functions of the positive and negative
parts.
-/
theorem ae_eq_zero_of_integral_mul_character_eq_zero {f : ℝ → ℝ}
    (hf : Integrable f standardGaussian)
    (hz : ∀ t : ℝ, (∫ x, (f x : ℂ) * Complex.exp ((t*x : ℝ) * Complex.I) ∂standardGaussian) = 0) :
    f =ᵐ[standardGaussian] 0 := by
  let fp (x : ℝ) := max (f x) 0
  let fm (x : ℝ) := max (-f x) 0
  have hp : Integrable fp standardGaussian := hf.sup (integrable_const 0)
  have hm : Integrable fm standardGaussian := hf.neg.sup (integrable_const 0)
  have hpm : AEMeasurable (fun x => ENNReal.ofReal (fp x)) standardGaussian :=
    hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hmm : AEMeasurable (fun x => ENNReal.ofReal (fm x)) standardGaussian :=
    hm.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  let μp := standardGaussian.withDensity (fun x => ENNReal.ofReal (fp x))
  let μm := standardGaussian.withDensity (fun x => ENNReal.ofReal (fm x))
  letI : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hp.hasFiniteIntegral
  letI : IsFiniteMeasure μm := isFiniteMeasure_withDensity_ofReal hm.hasFiniteIntegral
  have hpn (x : ℝ) : 0 ≤ fp x := le_max_right _ _
  have hmn (x : ℝ) : 0 ≤ fm x := le_max_right _ _
  have hd (x : ℝ) : fp x - fm x = f x := by
    dsimp [fp, fm]
    rcases le_total 0 (f x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]; simp
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]; simp
  have he : μp = μm := by
    apply Measure.ext_of_charFun
    funext t
    simp only [charFun_apply_real, μp, μm]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hpm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _,
      integral_withDensity_eq_integral_toReal_smul₀ hmm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _]
    simp only [ENNReal.toReal_ofReal (hpn _), ENNReal.toReal_ofReal (hmn _), Complex.real_smul]
    apply sub_eq_zero.mp
    rw [← integral_sub (by simpa only [Complex.ofReal_mul] using integrable_mul_character hp t)
      (by simpa only [Complex.ofReal_mul] using integrable_mul_character hm t)]
    convert hz t using 1
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    rw [← sub_mul, ← Complex.ofReal_sub, hd]
    simp only [Complex.ofReal_mul]
  have he' := (withDensity_eq_iff_of_sigmaFinite hpm hmm).mp he
  filter_upwards [he'] with x hx
  have hx' := congrArg ENNReal.toReal hx
  simp only [ENNReal.toReal_ofReal (hpn _), ENNReal.toReal_ofReal (hmn _)] at hx'
  change f x = 0
  rw [← hd, hx', sub_self]

/-- Vanishing Gaussian polynomial moments force a real L² function to vanish almost everywhere. -/
theorem hermite_complete {f : ℝ → ℝ} (hf : MemLp f 2 standardGaussian)
    (hm : ∀ n : ℕ, ∫ x, f x * x^n ∂standardGaussian = 0) : f =ᵐ[standardGaussian] 0 := by
  apply ae_eq_zero_of_integral_mul_character_eq_zero (hf.integrable (by norm_num))
  intro t
  convert integral_mul_exp_eq_zero_of_moments hf hm ((t:ℂ)*Complex.I) using 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  congr 2
  push_cast
  ring

end Foundations
