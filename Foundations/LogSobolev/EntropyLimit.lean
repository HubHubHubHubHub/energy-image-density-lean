import Foundations.LogSobolev.Gross
import Foundations.Sobolev1D.Density

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations

/-- Fatou with a convergent scalar upper bound, including finiteness of the limit integral. -/
theorem integrable_nonneg_limit_of_integral_bound {μ : Measure ℝ}
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {b : ℕ → ℝ} {B : ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hFn : ∀ n x, 0 ≤ F n x)
    (hf : AEStronglyMeasurable f μ) (hfn : ∀ x, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hb : ∀ n, (∫ x, F n x ∂μ) ≤ b n) (hbt : Tendsto b atTop (𝓝 B)) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ B := by
  have hB : 0 ≤ B := ge_of_tendsto hbt (Eventually.of_forall fun n =>
    (integral_nonneg (hFn n)).trans (hb n))
  have hl : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        exact ht.mono fun x hx => (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ liminf (fun n => ENNReal.ofReal (b n)) atTop := by
        apply liminf_le_liminf (Eventually.of_forall fun n => ?_)
        rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (ae_of_all _ (hFn n))]
        exact ENNReal.ofReal_le_ofReal (hb n)
      _ = _ := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hbt).liminf_eq
  have hi : Integrable f μ := ⟨hf,(hasFiniteIntegral_iff_ofReal (ae_of_all _ hfn)).mpr
    (hl.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hl
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hfn),
    ENNReal.toReal_ofReal (integral_nonneg hfn),ENNReal.toReal_ofReal hB] at hh
  exact hh

def entropyCost (z : ℝ) : ℝ := z*Real.log z-z+1
@[fun_prop] theorem continuous_entropyCost : Continuous entropyCost :=
  (Real.continuous_mul_log.sub continuous_id).add continuous_const

theorem entropyCost_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ entropyCost z := by
  have hh := Real.negMulLog_le_one_sub_self hz
  dsimp [Real.negMulLog,entropyCost] at *
  linarith

theorem integral_entropyCost {f : ℝ → ℝ} (hf : Integrable f standardGaussian)
    (he : Integrable (fun x => f x*Real.log (f x)) standardGaussian) :
    (∫ x, entropyCost (f x) ∂standardGaussian) = entropy standardGaussian f+
      (∫ x, f x ∂standardGaussian)*Real.log (∫ x, f x ∂standardGaussian)-
      (∫ x, f x ∂standardGaussian)+1 := by
  dsimp [entropyCost,entropy]
  have hadd := integral_add (he.sub hf) (integrable_const (1 : ℝ) (μ := standardGaussian))
  simp only [Pi.sub_apply] at hadd
  rw [hadd,integral_sub he hf]
  simp

/-- Lower semicontinuity in the form needed for the graph closure: both entropy finiteness
and Gross's bound survive simultaneous L² convergence of functions and derivatives. -/
theorem logSobolev_of_L2_limit {μ : Measure ℝ} (hμ : μ = standardGaussian)
    {f d : ℕ → ℝ → ℝ} {u g : ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hd : ∀ n, MemLp (d n) 2 μ)
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (ht : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u)))
    (hdt : Tendsto (fun n => (hd n).toLp (d n)) atTop (𝓝 (hg.toLp g)))
    (he : ∀ n, Integrable (fun x => (f n x)^2*Real.log ((f n x)^2)) μ)
    (hb : ∀ n, entropy μ (fun x => (f n x)^2) ≤ 2*∫ x, (d n x)^2 ∂μ) :
    Integrable (fun x => (u x)^2*Real.log ((u x)^2)) μ ∧
      entropy μ (fun x => (u x)^2) ≤ 2*∫ x, (g x)^2 ∂μ := by
  subst μ
  have htm := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mp ht
  obtain ⟨φ,hφ,hφae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ENNReal) ≠ 0)
    (fun n => (hf n).1) hu.1 htm).exists_seq_tendsto_ae
  let m := ∫ x, (u x)^2 ∂standardGaussian
  let mn := fun n => ∫ x, (f (φ n) x)^2 ∂standardGaussian
  let e := ∫ x, (g x)^2 ∂standardGaussian
  let en := fun n => ∫ x, (d (φ n) x)^2 ∂standardGaussian
  have hmt : Tendsto mn atTop (𝓝 m) := (tendsto_energy hf hu ht).comp hφ.tendsto_atTop
  have het : Tendsto en atTop (𝓝 e) := (tendsto_energy hd hg hdt).comp hφ.tendsto_atTop
  have hbnd : ∀ n, (∫ x, entropyCost ((f (φ n) x)^2) ∂standardGaussian) ≤
      2*en n+mn n*Real.log (mn n)-mn n+1 := by
    intro n
    rw [integral_entropyCost (hf (φ n)).integrable_sq (he (φ n))]
    have := hb (φ n)
    dsimp [mn,en]; linarith
  have hbt : Tendsto (fun n => 2*en n+mn n*Real.log (mn n)-mn n+1) atTop
      (𝓝 (2*e+m*Real.log m-m+1)) :=
    (((het.const_mul 2).add (Real.continuous_mul_log.continuousAt.tendsto.comp hmt)).sub hmt).add_const 1
  obtain ⟨hi,hle⟩ := integrable_nonneg_limit_of_integral_bound
    (fun n => ((he (φ n)).sub (hf (φ n)).integrable_sq).add (integrable_const 1))
    (fun n x => entropyCost_nonneg (sq_nonneg (f (φ n) x)))
    (continuous_entropyCost.comp_aestronglyMeasurable (hu.aestronglyMeasurable.pow 2))
    (fun x => entropyCost_nonneg (sq_nonneg (u x)))
    (hφae.mono fun x hx => continuous_entropyCost.continuousAt.tendsto.comp (hx.pow 2)) hbnd hbt
  have hint : Integrable (fun x => (u x)^2*Real.log ((u x)^2)) standardGaussian := by
    have hh := (hi.add hu.integrable_sq).sub (integrable_const 1)
    convert hh using 1
    ext x
    dsimp [entropyCost]
    ring
  refine ⟨hint,?_⟩
  simp only [Pi.pow_apply] at hle
  rw [integral_entropyCost hu.integrable_sq hint] at hle
  dsimp [m,e] at hle
  linarith

end Foundations
