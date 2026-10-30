import Foundations.LogSobolevD.EntropyFlow

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations

theorem tendsto_entropyOf_of_bounded {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {κ : Type*} {l : Filter κ} [l.IsCountablyGenerated]
    {F : κ → X → ℝ} {f : X → ℝ} {C : ℝ}
    (hmeas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ)
    (hbound : ∀ᶠ n in l, ∀ᵐ x ∂μ, ‖F n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) l (𝓝 (f x))) :
    Tendsto (fun n => entropyOf μ (F n)) l (𝓝 (entropyOf μ f)) := by
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-C) C) Real.continuous_mul_log.continuousOn
  have hm := tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    hmeas hbound (integrable_const _) hlim
  have he := tendsto_integral_filter_of_dominated_convergence
    (F := fun n x => F n x*Real.log (F n x)) (f := fun x => f x*Real.log (f x)) (fun _ => D)
    (hmeas.mono fun n hn => Real.continuous_mul_log.comp_aestronglyMeasurable hn)
    (hbound.mono fun n hn => hn.mono fun x hx => hD _ (abs_le.mp hx))
    (integrable_const _)
    (hlim.mono fun x hx => Real.continuous_mul_log.continuousAt.tendsto.comp hx)
  exact he.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hm)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integrable_gradNormSqD {g : (ι → ℝ) → ℝ} (hg : IsC1BoundedD g) :
    Integrable (gradNormSqD g) (gaussianProduct ι) :=
  integrable_finsetSum _ (fun i _ => (hg.memLp_partial i 2).integrable_sq)

theorem fisherD_sq_add_le {g : (ι → ℝ) → ℝ} (hg : IsC1BoundedD g) {ε : ℝ} (hε : 0 < ε) :
    fisherInfoD (fun x => g x*g x+ε) ≤ 4*∫ x, gradNormSqD g x ∂gaussianProduct ι := by
  have hf := (hg.mul hg).add (IsC1BoundedD.const ε)
  have hp : ∀ x, ε ≤ g x*g x+ε := fun x => le_add_of_nonneg_left (mul_self_nonneg _)
  have hder : ∀ i x, partialD (fun x => g x*g x+ε) i x = 2*g x*partialD g i x := by
    intro i x
    rw [partialD_add (hg.mul hg) (IsC1BoundedD.const ε),partialD_mul hg hg,partialD_const]
    ring
  rw [fisherInfoD_eq_sum hf hε hp]
  unfold gradNormSqD
  rw [integral_finsetSum _ (fun i _ => (hg.memLp_partial i 2).integrable_sq),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ∫ x, 4*(partialD g i x)^2 ∂gaussianProduct ι := by
      apply integral_mono ((memLp_fisherCoordD hf hε hp i 1).integrable le_rfl)
        ((hg.memLp_partial i 2).integrable_sq.const_mul 4)
      intro x
      dsimp [fisherCoordD]
      rw [hder,div_le_iff₀ (hε.trans_le (hp x))]
      nlinarith [mul_nonneg hε.le (sq_nonneg (partialD g i x))]
    _ = _ := integral_const_mul _ _

/-- Gross's logarithmic Sobolev inequality, with the standard Gaussian normalization. -/
theorem logSobolev_gaussianD_C2 {g : (ι → ℝ) → ℝ} (hg : IsC2BoundedD g) :
    entropyOf (gaussianProduct ι) (fun x => (g x)^2) ≤
      2*∫ x, gradNormSqD g x ∂(gaussianProduct ι) := by
  let ε := fun n : ℕ => ((n : ℝ)+1)⁻¹
  have hepos : ∀ n, 0 < ε n := fun n => inv_pos.mpr (by positivity)
  have hele : ∀ n, ε n ≤ 1 := fun n => by
    dsimp [ε]; exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have het : Tendsto ε atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hb : ∀ n, entropyOf (gaussianProduct ι) (fun x => g x*g x+ε n) ≤
      2*∫ x, gradNormSqD g x ∂(gaussianProduct ι) := by
    intro n
    have hh := entropyD_le_half_fisher ((hg.mul hg).add (IsC2BoundedD.const (ε n))) (hepos n)
      (fun x => le_add_of_nonneg_left (mul_self_nonneg _))
    have hh' := fisherD_sq_add_le hg.1 (hepos n)
    linarith
  obtain ⟨C,hC⟩ := hg.1.bounded
  have ht : Tendsto (fun n => entropyOf (gaussianProduct ι) (fun x => g x*g x+ε n)) atTop
      (𝓝 (entropyOf (gaussianProduct ι) (fun x => (g x)^2))) := by
    apply tendsto_entropyOf_of_bounded (C := C^2+1)
    · exact Eventually.of_forall fun n => by have hc := hg.1.contDiff.continuous; fun_prop
    · exact Eventually.of_forall fun n => ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg (add_nonneg (mul_self_nonneg _) (hepos n).le)]
        have hh := pow_le_pow_left₀ (norm_nonneg (g x)) (hC x) 2
        rw [Real.norm_eq_abs,sq_abs] at hh
        nlinarith [hele n])
    · exact ae_of_all _ (fun x => by simpa only [add_zero,pow_two] using tendsto_const_nhds.add het)
  exact le_of_tendsto ht (Eventually.of_forall hb)

end Foundations
