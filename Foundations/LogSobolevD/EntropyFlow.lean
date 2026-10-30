import Foundations.LogSobolevD.Entropy

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem continuous_mehlerEntropyD {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : Continuous (mehlerEntropyD f) := by
  obtain ⟨C,hC⟩ := hb
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-C) C) Real.continuous_mul_log.continuousOn
  have hM := continuous_mehlerKernelD hf ⟨C,hC⟩
  apply continuous_of_dominated (bound := fun _ => D)
  · intro t
    exact (Real.continuous_mul_log.comp (hM.comp ((continuous_const (y := t)).prodMk continuous_id))).aestronglyMeasurable
  · intro t
    exact ae_of_all _ (fun x => hD _ (abs_le.mp (norm_mehlerKernelD_le hC t x)))
  · exact integrable_const D
  · exact ae_of_all _ (fun x => Real.continuous_mul_log.comp (hM.comp (continuous_id.prodMk continuous_const)))

theorem tendsto_mehlerEntropyD_atTop {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Tendsto (mehlerEntropyD f) atTop
      (𝓝 ((∫ x, f x ∂gaussianProduct ι)*Real.log (∫ x, f x ∂gaussianProduct ι))) := by
  obtain ⟨C,hC⟩ := hb
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-C) C) Real.continuous_mul_log.continuousOn
  have hM := continuous_mehlerKernelD hf ⟨C,hC⟩
  have hh := tendsto_integral_filter_of_dominated_convergence
    (μ := gaussianProduct ι) (l := atTop)
    (F := fun t x => mehlerKernelD t f x*Real.log (mehlerKernelD t f x))
    (f := fun _ => (∫ x, f x ∂gaussianProduct ι)*Real.log (∫ x, f x ∂gaussianProduct ι))
    (bound := fun _ => D)
    (Eventually.of_forall fun t =>
      (Real.continuous_mul_log.comp (hM.comp ((continuous_const (y := t)).prodMk continuous_id))).aestronglyMeasurable)
    (Eventually.of_forall fun t => ae_of_all _ (fun x => hD _ (abs_le.mp (norm_mehlerKernelD_le hC t x))))
    (integrable_const _) (ae_of_all _ (fun x =>
      Real.continuous_mul_log.continuousAt.tendsto.comp (tendsto_mehlerKernelD_atTop hf ⟨C,hC⟩ x)))
  convert hh using 1 <;> first | rfl | simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

/-- Entropy dissipation; time zero is handled by continuity in the integrated inequality. -/
theorem hasDerivAt_mehlerEntropyD {f : (ι → ℝ) → ℝ} (hf : IsC2BoundedD f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (mehlerEntropyD f) (-fisherInfoD (mehlerKernelD t f)) t := by
  obtain ⟨C,hC⟩ := hf.1.bounded
  choose D hD using hf.1.partial_bounded
  choose E hE using (fun i => (hf.2 i).partial_bounded i)
  let K := 1+‖Real.log ε‖+‖Real.log C‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hp : ∀ s x, ε ≤ mehlerKernelD s f x := le_mehlerKernelD hf.1.contDiff.continuous hf.1.bounded hpos
  have hlog : ∀ s x, ‖1+Real.log (mehlerKernelD s f x)‖ ≤ K := by
    intro s x
    apply (norm_add_le _ _).trans
    simpa only [K,norm_one,add_assoc] using add_le_add (le_rfl : (1 : ℝ) ≤ 1)
      (norm_log_le_of_bounds hε (hp s x) ((le_abs_self _).trans (norm_mehlerKernelD_le hC s x)))

  have hM := continuous_mehlerKernelD hf.1.contDiff.continuous hf.1.bounded
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := gaussianProduct ι)
    (F := fun s x => mehlerKernelD s f x*Real.log (mehlerKernelD s f x))
    (F' := fun s x => (1+Real.log (mehlerKernelD s f x))*
      (ouGeneratorD (mehlerKernelD s f) x))
    (bound := fun x => K*(∑ i, (E i+‖x i‖*D i))) (s := Ioi 0) (x₀ := t) (Ioi_mem_nhds ht)
    (Eventually.of_forall fun s =>
      (Real.continuous_mul_log.comp (hM.comp ((continuous_const (y := s)).prodMk continuous_id))).aestronglyMeasurable)
    (integrable_mul_log_of_boundedD (isC1BoundedD_mehlerKernelD hf.1 t).contDiff.continuous
      (isC1BoundedD_mehlerKernelD hf.1 t).bounded)
    (by
      exact ((((isC2BoundedD_mehlerKernelD hf t).1.log hε (hp t)).contDiff.continuous.const_add 1).mul
        (continuous_ouGeneratorD (isC2BoundedD_mehlerKernelD hf t))).aestronglyMeasurable)
    (ae_of_all _ (fun x s hs => by
      rw [norm_mul]
      exact mul_le_mul (hlog s x) (norm_mehler_generatorD_le hf hD hE hs.le x) (norm_nonneg _) hK))
    ((integrable_finsetSum _ (fun i _ => (integrable_const (E i)).add ((integrable_gaussianD_coord i).norm.mul_const (D i)))).const_mul K)
    (ae_of_all _ (fun x s hs => by
      have hd := hasDerivAt_mehlerKernelD_time hf hs x
      have hn := (hε.trans_le (hp s x)).ne'
      exact (hd.mul (hd.log hn)).congr_deriv (by field_simp [hn]; ring)))
  convert hh.2 using 1 <;> first | rfl | exact (integral_log_generatorD (isC2BoundedD_mehlerKernelD hf t) hε (hp t)).symm

/-- Integrating entropyOf dissipation and Fisher decay gives the factor one half. -/
theorem entropyD_le_half_fisher {f : (ι → ℝ) → ℝ} (hf : IsC2BoundedD f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) :
    entropyOf (gaussianProduct ι) f ≤ (1/2 : ℝ)*fisherInfoD f := by
  let Ψ := fun t => mehlerEntropyD f t-(1/2 : ℝ)*(mehlerCoeffA t)^2*fisherInfoD f
  have hdiff : ∀ t > 0, HasDerivAt Ψ
      (-fisherInfoD (mehlerKernelD t f)+(mehlerCoeffA t)^2*fisherInfoD f) t := by
    intro t ht
    exact ((hasDerivAt_mehlerEntropyD hf hε hpos ht).sub
      (((hasDerivAt_mehlerCoeffA t).pow 2).const_mul (1/2) |>.mul_const (fisherInfoD f))).congr_deriv (by ring)
  have hmono : MonotoneOn Ψ (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (((continuous_mehlerEntropyD hf.1.contDiff.continuous hf.1.bounded).sub
        ((continuous_const.mul (continuous_mehlerCoeffA.pow 2)).mul continuous_const)).continuousOn)
    · intro t ht
      exact (hdiff t (by simpa using ht)).hasDerivWithinAt
    · intro t ht
      have h := fisherD_mehlerKernelD_le hf.1 hε hpos (t := t) (by simpa using le_of_lt (show 0 < t by simpa using ht))
      rw [← mehlerCoeffA_sq] at h
      linarith
  have hlim : Tendsto Ψ atTop (𝓝 ((∫ x, f x ∂gaussianProduct ι)*Real.log (∫ x, f x ∂gaussianProduct ι))) := by
    have hh := (tendsto_mehlerEntropyD_atTop hf.1.contDiff.continuous hf.1.bounded).sub
      (((tendsto_mehlerCoeffA_atTop.pow 2).const_mul (1/2)).mul_const (fisherInfoD f))
    simpa only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero,zero_mul,sub_zero] using hh
  have hle := ge_of_tendsto hlim (eventually_atTop.2 ⟨0,fun t ht => hmono (by simp only [mem_Ici]; exact le_refl (0 : ℝ)) ht ht⟩)
  dsimp [Ψ,mehlerEntropyD,entropyOf] at *
  simp only [mehlerKernelD_zero,mehlerCoeffA,neg_zero,Real.exp_zero,one_pow,mul_one] at hle
  linarith

end Foundations
