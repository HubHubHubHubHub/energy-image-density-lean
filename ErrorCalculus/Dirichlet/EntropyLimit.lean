import ErrorCalculus.Dirichlet.Entropy
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Fatou with a convergent scalar upper bound, including finiteness of the limit integral. -/
theorem integrable_nonneg_limit_of_integral_bound' {μ : Measure Ω}
    {F : ℕ → Ω → ℝ} {f : Ω → ℝ} {b : ℕ → ℝ} {B : ℝ}
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

/-- The nonnegative entropy cost has the expected integral on a probability space. -/
theorem integral_entropyCost [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (he : Integrable (fun x => f x * Real.log (f x)) μ) :
    (∫ x, Foundations.entropyCost (f x) ∂μ) = entropy μ f +
      (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ) - (∫ x, f x ∂μ) + 1 := by
  dsimp [Foundations.entropyCost, entropy]
  have hadd := integral_add (he.sub hf) (integrable_const (1 : ℝ) (μ := μ))
  simp only [Pi.sub_apply] at hadd
  rw [hadd, integral_sub he hf]
  simp

/-- Entropy lower semicontinuity with converging scalar bounds, including finiteness.
The input and the limit are genuine L² classes on an arbitrary probability space. -/
theorem entropy_le_of_tendsto_L2 [IsProbabilityMeasure μ]
    {g : ℕ → Lp ℝ 2 μ} {u : Lp ℝ 2 μ} {b : ℕ → ℝ} {B : ℝ}
    (ht : Tendsto g atTop (𝓝 u))
    (he : ∀ n, Integrable (fun x => (g n x)^2 * Real.log ((g n x)^2)) μ)
    (hb : ∀ n, entropy μ (fun x => (g n x)^2) ≤ b n)
    (hbt : Tendsto b atTop (𝓝 B)) :
    Integrable (fun x => (u x)^2 * Real.log ((u x)^2)) μ ∧
      entropy μ (fun x => (u x)^2) ≤ B := by
  obtain ⟨φ, hφ, hφae⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  let m := ∫ x, (u x)^2 ∂μ
  let mn := fun n => ∫ x, (g (φ n) x)^2 ∂μ
  have hmt : Tendsto mn atTop (𝓝 m) := by
    simp only [mn, m, ← lp_two_norm_sq]
    exact (ht.norm.pow 2).comp hφ.tendsto_atTop
  have hbnd : ∀ n, (∫ x, Foundations.entropyCost ((g (φ n) x)^2) ∂μ) ≤
      b (φ n) + mn n * Real.log (mn n) - mn n + 1 := by
    intro n
    rw [integral_entropyCost (Lp.memLp (g (φ n))).integrable_sq (he (φ n))]
    have := hb (φ n)
    dsimp [mn]
    linarith
  have hbt' : Tendsto (fun n => b (φ n) + mn n * Real.log (mn n) - mn n + 1)
      atTop (𝓝 (B + m * Real.log m - m + 1)) :=
    (((hbt.comp hφ.tendsto_atTop).add
      (Real.continuous_mul_log.continuousAt.tendsto.comp hmt)).sub hmt).add_const 1
  obtain ⟨hi, hle⟩ := integrable_nonneg_limit_of_integral_bound'
    (fun n => ((he (φ n)).sub (Lp.memLp (g (φ n))).integrable_sq).add (integrable_const 1))
    (fun n x => Foundations.entropyCost_nonneg (sq_nonneg (g (φ n) x)))
    (Foundations.continuous_entropyCost.comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable u).pow 2))
    (fun x => Foundations.entropyCost_nonneg (sq_nonneg (u x)))
    (hφae.mono fun x hx => Foundations.continuous_entropyCost.continuousAt.tendsto.comp
      (hx.pow 2)) hbnd hbt'
  have hint : Integrable (fun x => (u x)^2 * Real.log ((u x)^2)) μ := by
    have hh := (hi.add (Lp.memLp u).integrable_sq).sub (integrable_const 1)
    convert hh using 1
    ext x
    dsimp [Foundations.entropyCost]
    ring
  refine ⟨hint, ?_⟩
  simp only [Pi.pow_apply] at hle
  rw [integral_entropyCost (Lp.memLp u).integrable_sq hint] at hle
  dsimp [m] at hle
  linarith

end ErrorCalculus
