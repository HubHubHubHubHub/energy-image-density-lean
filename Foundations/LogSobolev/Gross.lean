import Foundations.LogSobolev.EntropyFlow

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations

theorem tendsto_entropy_of_bounded {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → ℝ → ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hmeas : ∀ᶠ n in l, AEStronglyMeasurable (F n) standardGaussian)
    (hbound : ∀ᶠ n in l, ∀ᵐ x ∂standardGaussian, ‖F n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂standardGaussian, Tendsto (fun n => F n x) l (𝓝 (f x))) :
    Tendsto (fun n => entropy standardGaussian (F n)) l (𝓝 (entropy standardGaussian f)) := by
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

theorem fisher_sq_add_le {g : ℝ → ℝ} (hg : IsC1Bounded g) {ε : ℝ} (hε : 0 < ε) :
    fisherInfo (fun x => g x*g x+ε) ≤ 4*∫ x, (deriv g x)^2 ∂standardGaussian := by
  have hf := (hg.mul hg).add (IsC1Bounded.const ε)
  have hp : ∀ x, ε ≤ g x*g x+ε := fun x => le_add_of_nonneg_left (mul_self_nonneg _)
  have hder : ∀ x, deriv (fun x => g x*g x+ε) x = 2*g x*deriv g x := by
    intro x
    exact (((hg.hasDerivAt x).mul (hg.hasDerivAt x)).add_const ε).deriv.trans (by ring)
  have hid : Integrable (fun x => (deriv g x)^2) standardGaussian := by
    exact (hg.memLp_deriv 2).integrable_sq
  calc
    _ ≤ ∫ x, 4*(deriv g x)^2 ∂standardGaussian := by
      apply integral_mono ((memLp_fisherDensity hf hε hp 1).integrable le_rfl) (hid.const_mul 4)
      intro x
      dsimp [fisherDensity]
      rw [hder,div_le_iff₀ (hε.trans_le (hp x))]
      nlinarith [mul_nonneg hε.le (sq_nonneg (deriv g x))]
    _ = _ := integral_const_mul _ _

/-- Gross's logarithmic Sobolev inequality, with the standard Gaussian normalization. -/
theorem logSobolev_gaussian_C2 {g : ℝ → ℝ} (hg : IsC2Bounded g) :
    entropy standardGaussian (fun x => (g x)^2) ≤
      2*∫ x, (deriv g x)^2 ∂standardGaussian := by
  let ε := fun n : ℕ => ((n : ℝ)+1)⁻¹
  have hepos : ∀ n, 0 < ε n := fun n => inv_pos.mpr (by positivity)
  have hele : ∀ n, ε n ≤ 1 := fun n => by
    dsimp [ε]; exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have het : Tendsto ε atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hb : ∀ n, entropy standardGaussian (fun x => g x*g x+ε n) ≤
      2*∫ x, (deriv g x)^2 ∂standardGaussian := by
    intro n
    have hh := entropy_le_half_fisher ((hg.mul hg).add (IsC2Bounded.const (ε n))) (hepos n)
      (fun x => le_add_of_nonneg_left (mul_self_nonneg _))
    have hh' := fisher_sq_add_le hg.1 (hepos n)
    linarith
  obtain ⟨C,hC⟩ := hg.1.bounded
  have ht : Tendsto (fun n => entropy standardGaussian (fun x => g x*g x+ε n)) atTop
      (𝓝 (entropy standardGaussian (fun x => (g x)^2))) := by
    apply tendsto_entropy_of_bounded (C := C^2+1)
    · exact Eventually.of_forall fun n => by have hc := hg.1.contDiff.continuous; fun_prop
    · exact Eventually.of_forall fun n => ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg (add_nonneg (mul_self_nonneg _) (hepos n).le)]
        have hh := pow_le_pow_left₀ (norm_nonneg (g x)) (hC x) 2
        rw [Real.norm_eq_abs,sq_abs] at hh
        nlinarith [hele n])
    · exact ae_of_all _ (fun x => by simpa only [add_zero,pow_two] using tendsto_const_nhds.add het)
  exact le_of_tendsto ht (Eventually.of_forall hb)

end Foundations
