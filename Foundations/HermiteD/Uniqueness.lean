import Foundations.HermiteD.Exponential
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

noncomputable section
open Filter Topology Set MeasureTheory ProbabilityTheory
namespace Foundations
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsFiniteMeasure μ]

theorem integrable_mul_dualCharacter {f : E → ℝ} (hf : Integrable f μ) (t : StrongDual ℝ E) :
    Integrable (fun x => (f x : ℂ) * Complex.exp ((t x : ℝ) * Complex.I)) μ := by
  have hfm := hf.aestronglyMeasurable
  apply hf.norm.mono' (by fun_prop)
  apply ae_of_all
  intro x
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]

/--
Injectivity on real L¹ densities, via the characteristic functions of the positive and negative
parts.
-/
theorem ae_eq_zero_of_integral_mul_dualCharacter_eq_zero {f : E → ℝ}
    (hf : Integrable f μ)
    (hz : ∀ t : StrongDual ℝ E, (∫ x, (f x : ℂ) * Complex.exp ((t x : ℝ) * Complex.I) ∂μ) = 0) :
    f =ᵐ[μ] 0 := by
  let fp (x : E) := max (f x) 0
  let fm (x : E) := max (-f x) 0
  have hp : Integrable fp μ := hf.sup (integrable_const 0)
  have hm : Integrable fm μ := hf.neg.sup (integrable_const 0)
  have hpm : AEMeasurable (fun x => ENNReal.ofReal (fp x)) μ :=
    hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hmm : AEMeasurable (fun x => ENNReal.ofReal (fm x)) μ :=
    hm.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  let μp := μ.withDensity (fun x => ENNReal.ofReal (fp x))
  let μm := μ.withDensity (fun x => ENNReal.ofReal (fm x))
  letI : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hp.hasFiniteIntegral
  letI : IsFiniteMeasure μm := isFiniteMeasure_withDensity_ofReal hm.hasFiniteIntegral
  have hpn (x : E) : 0 ≤ fp x := le_max_right _ _
  have hmn (x : E) : 0 ≤ fm x := le_max_right _ _
  have hd (x : E) : fp x - fm x = f x := by
    dsimp [fp, fm]
    rcases le_total 0 (f x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]; simp
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]; simp
  have he : μp = μm := by
    apply Measure.ext_of_charFunDual
    funext t
    simp only [charFunDual_apply, μp, μm]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hpm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _,
      integral_withDensity_eq_integral_toReal_smul₀ hmm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _]
    simp only [ENNReal.toReal_ofReal (hpn _), ENNReal.toReal_ofReal (hmn _), Complex.real_smul]
    apply sub_eq_zero.mp
    rw [← integral_sub (by simpa only [Complex.ofReal_mul] using integrable_mul_dualCharacter hp t)
      (by simpa only [Complex.ofReal_mul] using integrable_mul_dualCharacter hm t)]
    convert hz t using 1
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    rw [← sub_mul, ← Complex.ofReal_sub, hd]
  have he' := (withDensity_eq_iff_of_sigmaFinite hpm hmm).mp he
  filter_upwards [he'] with x hx
  have hx' := congrArg ENNReal.toReal hx
  simp only [ENNReal.toReal_ofReal (hpn _), ENNReal.toReal_ofReal (hmn _)] at hx'
  change f x = 0
  rw [← hd, hx', sub_self]


end Foundations
