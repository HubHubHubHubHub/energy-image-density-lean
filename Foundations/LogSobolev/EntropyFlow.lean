import Foundations.LogSobolev.Entropy
import Foundations.LogSobolev.MehlerTime

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations

theorem continuous_mehlerEntropy {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : Continuous (mehlerEntropy f) := by
  obtain ⟨C,hC⟩ := hb
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-C) C) Real.continuous_mul_log.continuousOn
  have hM := continuous_mehlerKernel hf ⟨C,hC⟩
  apply continuous_of_dominated (bound := fun _ => D)
  · intro t
    exact (Real.continuous_mul_log.comp (hM.comp ((continuous_const (y := t)).prodMk continuous_id))).aestronglyMeasurable
  · intro t
    exact ae_of_all _ (fun x => hD _ (abs_le.mp (norm_mehlerKernel_le hC t x)))
  · exact integrable_const D
  · exact ae_of_all _ (fun x => Real.continuous_mul_log.comp (hM.comp (continuous_id.prodMk continuous_const)))

theorem tendsto_mehlerEntropy_atTop {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Tendsto (mehlerEntropy f) atTop
      (𝓝 ((∫ x, f x ∂standardGaussian)*Real.log (∫ x, f x ∂standardGaussian))) := by
  obtain ⟨C,hC⟩ := hb
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-C) C) Real.continuous_mul_log.continuousOn
  have hM := continuous_mehlerKernel hf ⟨C,hC⟩
  have hh := tendsto_integral_filter_of_dominated_convergence
    (μ := standardGaussian) (l := atTop)
    (F := fun t x => mehlerKernel t f x*Real.log (mehlerKernel t f x))
    (f := fun _ => (∫ x, f x ∂standardGaussian)*Real.log (∫ x, f x ∂standardGaussian))
    (bound := fun _ => D)
    (Eventually.of_forall fun t =>
      (Real.continuous_mul_log.comp (hM.comp ((continuous_const (y := t)).prodMk continuous_id))).aestronglyMeasurable)
    (Eventually.of_forall fun t => ae_of_all _ (fun x => hD _ (abs_le.mp (norm_mehlerKernel_le hC t x))))
    (integrable_const _) (ae_of_all _ (fun x =>
      Real.continuous_mul_log.continuousAt.tendsto.comp (tendsto_mehlerKernel_atTop hf ⟨C,hC⟩ x)))
  convert hh using 1 <;> first | rfl | simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem norm_mehler_generator_le {f : ℝ → ℝ} (hf : IsC2Bounded f)
    {D E : ℝ} (hD : ∀ x, ‖deriv f x‖ ≤ D) (hE : ∀ x, ‖deriv (deriv f) x‖ ≤ E)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    ‖deriv (deriv (mehlerKernel t f)) x-x*deriv (mehlerKernel t f) x‖ ≤ E+‖x‖*D := by
  have ha : ‖mehlerCoeffA t‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (mehlerCoeffA_pos t).le]; exact mehlerCoeffA_le_one ht
  have ha2 : ‖(mehlerCoeffA t)^2‖ ≤ 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg (mehlerCoeffA t)]
  rw [deriv2_mehlerKernel hf,deriv_mehlerKernel hf.1]
  apply (norm_sub_le _ _).trans
  simp only [norm_mul]
  apply add_le_add
  · exact (mul_le_mul ha2 (norm_mehlerKernel_le hE t x) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · exact mul_le_mul_of_nonneg_left
      ((mul_le_mul ha (norm_mehlerKernel_le hD t x) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)) (norm_nonneg _)

/-- Entropy dissipation; time zero is handled by continuity in the integrated inequality. -/
theorem hasDerivAt_mehlerEntropy {f : ℝ → ℝ} (hf : IsC2Bounded f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (mehlerEntropy f) (-fisherInfo (mehlerKernel t f)) t := by
  obtain ⟨C,hC⟩ := hf.1.bounded
  obtain ⟨D,hD⟩ := hf.1.deriv_bounded
  obtain ⟨E,hE⟩ := hf.2.deriv_bounded
  let K := 1+‖Real.log ε‖+‖Real.log C‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hp : ∀ s x, ε ≤ mehlerKernel s f x := le_mehlerKernel hf.1.contDiff.continuous hf.1.bounded hpos
  have hlog : ∀ s x, ‖1+Real.log (mehlerKernel s f x)‖ ≤ K := by
    intro s x
    apply (norm_add_le _ _).trans
    simpa only [K,norm_one,add_assoc] using add_le_add (le_rfl : (1 : ℝ) ≤ 1)
      (norm_log_le_of_bounds hε (hp s x) ((le_abs_self _).trans (norm_mehlerKernel_le hC s x)))
  have hy : Integrable (fun x : ℝ => ‖x‖) standardGaussian := by simpa using (integrable_pow_gaussian 1).norm
  have hM := continuous_mehlerKernel hf.1.contDiff.continuous hf.1.bounded
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := standardGaussian)
    (F := fun s x => mehlerKernel s f x*Real.log (mehlerKernel s f x))
    (F' := fun s x => (1+Real.log (mehlerKernel s f x))*
      (deriv (deriv (mehlerKernel s f)) x-x*deriv (mehlerKernel s f) x))
    (bound := fun x => K*(E+‖x‖*D)) (s := Ioi 0) (x₀ := t) (Ioi_mem_nhds ht)
    (Eventually.of_forall fun s =>
      (Real.continuous_mul_log.comp (hM.comp ((continuous_const (y := s)).prodMk continuous_id))).aestronglyMeasurable)
    (integrable_mul_log_of_bounded (isC1Bounded_mehlerKernel hf.1 t).contDiff.continuous
      (isC1Bounded_mehlerKernel hf.1 t).bounded)
    (by
      have hc := (isC2Bounded_mehlerKernel hf t).2.contDiff.continuous_deriv_one
      have hc' := (isC2Bounded_mehlerKernel hf t).1.contDiff.continuous_deriv_one
      have hclog := ((isC2Bounded_mehlerKernel hf t).1.log hε (hp t)).contDiff.continuous
      fun_prop)
    (ae_of_all _ (fun x s hs => by
      rw [norm_mul]
      exact mul_le_mul (hlog s x) (norm_mehler_generator_le hf hD hE hs.le x) (norm_nonneg _) hK))
    (((integrable_const E).add (hy.mul_const D)).const_mul K)
    (ae_of_all _ (fun x s hs => by
      have hd := hasDerivAt_mehlerKernel_time hf hs x
      have hn := (hε.trans_le (hp s x)).ne'
      exact (hd.mul (hd.log hn)).congr_deriv (by field_simp [hn]; ring)))
  convert hh.2 using 1 <;> first | rfl | exact (integral_log_generator (isC2Bounded_mehlerKernel hf t) hε (hp t)).symm

/-- Integrating entropy dissipation and Fisher decay gives the factor one half. -/
theorem entropy_le_half_fisher {f : ℝ → ℝ} (hf : IsC2Bounded f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) :
    entropy standardGaussian f ≤ (1/2 : ℝ)*fisherInfo f := by
  let Ψ := fun t => mehlerEntropy f t-(1/2 : ℝ)*(mehlerCoeffA t)^2*fisherInfo f
  have hdiff : ∀ t > 0, HasDerivAt Ψ
      (-fisherInfo (mehlerKernel t f)+(mehlerCoeffA t)^2*fisherInfo f) t := by
    intro t ht
    exact ((hasDerivAt_mehlerEntropy hf hε hpos ht).sub
      (((hasDerivAt_mehlerCoeffA t).pow 2).const_mul (1/2) |>.mul_const (fisherInfo f))).congr_deriv (by ring)
  have hmono : MonotoneOn Ψ (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (((continuous_mehlerEntropy hf.1.contDiff.continuous hf.1.bounded).sub
        ((continuous_const.mul (continuous_mehlerCoeffA.pow 2)).mul continuous_const)).continuousOn)
    · intro t ht
      exact (hdiff t (by simpa using ht)).hasDerivWithinAt
    · intro t ht
      have h := fisher_mehlerKernel_le hf.1 hε hpos (t := t) (by simpa using le_of_lt (show 0 < t by simpa using ht))
      rw [← mehlerCoeffA_sq] at h
      linarith
  have hlim : Tendsto Ψ atTop (𝓝 ((∫ x, f x ∂standardGaussian)*Real.log (∫ x, f x ∂standardGaussian))) := by
    have hh := (tendsto_mehlerEntropy_atTop hf.1.contDiff.continuous hf.1.bounded).sub
      (((tendsto_mehlerCoeffA_atTop.pow 2).const_mul (1/2)).mul_const (fisherInfo f))
    simpa only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero,zero_mul,sub_zero] using hh
  have hle := ge_of_tendsto hlim (eventually_atTop.2 ⟨0,fun t ht => hmono (by simp only [mem_Ici]; exact le_refl (0 : ℝ)) ht ht⟩)
  dsimp [Ψ,mehlerEntropy,entropy] at *
  simp only [mehlerKernel_zero,mehlerCoeffA,neg_zero,Real.exp_zero,one_pow,mul_one] at hle
  linarith

end Foundations
