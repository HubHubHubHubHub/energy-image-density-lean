import Foundations.LogSobolev.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations

theorem hasDerivAt_mehlerKernel_space {f : ℝ → ℝ} (hf : IsC1Bounded f) (t x : ℝ) :
    HasDerivAt (mehlerKernel t f) (mehlerCoeffA t * mehlerKernel t (deriv f) x) x := by
  obtain ⟨C,hC⟩ := hf.deriv_bounded
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := standardGaussian) (F := fun x y => f (mehlerCoeffA t*x+mehlerCoeffB t*y))
    (F' := fun x y => mehlerCoeffA t * deriv f (mehlerCoeffA t*x+mehlerCoeffB t*y))
    (bound := fun _ => ‖mehlerCoeffA t‖*C) (s := univ) (x₀ := x) (by simp)
    (Eventually.of_forall fun z => (hf.contDiff.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_gaussian_affine hf.contDiff.continuous hf.bounded _ _)
    (by have hc := hf.contDiff.continuous_deriv_one; fun_prop)
    (ae_of_all _ (fun y z _ => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))
    (integrable_const _) (ae_of_all _ (fun y z _ => ?_))
  · convert h.2 using 1 <;> first | rfl | simp only [mehlerKernel, integral_const_mul]
  · simpa only [Function.comp_def,id_eq,mul_one,mul_comm] using (hf.hasDerivAt _).comp z
      (((hasDerivAt_id z).const_mul (mehlerCoeffA t)).add_const (mehlerCoeffB t*y))

theorem deriv_mehlerKernel {f : ℝ → ℝ} (hf : IsC1Bounded f) (t x : ℝ) :
    deriv (mehlerKernel t f) x = mehlerCoeffA t * mehlerKernel t (deriv f) x :=
  (hasDerivAt_mehlerKernel_space hf t x).deriv

theorem isC1Bounded_mehlerKernel {f : ℝ → ℝ} (hf : IsC1Bounded f) (t : ℝ) :
    IsC1Bounded (mehlerKernel t f) := by
  have hd : deriv (mehlerKernel t f) = fun x => mehlerCoeffA t * mehlerKernel t (deriv f) x :=
    funext (deriv_mehlerKernel hf t)
  refine ⟨contDiff_one_iff_deriv.mpr ⟨fun x => (hasDerivAt_mehlerKernel_space hf t x).differentiableAt,?_⟩,?_,?_⟩
  · rw [hd]
    exact continuous_const.mul ((continuous_mehlerKernel hf.contDiff.continuous_deriv_one
      hf.deriv_bounded).comp (continuous_const.prodMk continuous_id))
  · obtain ⟨C,hC⟩ := hf.bounded
    exact ⟨C,fun x => norm_mehlerKernel_le hC t x⟩
  · obtain ⟨C,hC⟩ := hf.deriv_bounded
    refine ⟨‖mehlerCoeffA t‖*C,fun x => ?_⟩
    rw [deriv_mehlerKernel hf,norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_mehlerKernel_le hC t x) (norm_nonneg _)

theorem deriv2_mehlerKernel {f : ℝ → ℝ} (hf : IsC2Bounded f) (t x : ℝ) :
    deriv (deriv (mehlerKernel t f)) x = (mehlerCoeffA t)^2 * mehlerKernel t (deriv (deriv f)) x := by
  have he : deriv (mehlerKernel t f) = fun x => mehlerCoeffA t * mehlerKernel t (deriv f) x :=
    funext (deriv_mehlerKernel hf.1 t)
  rw [he,deriv_const_mul _ (hasDerivAt_mehlerKernel_space hf.2 t x).differentiableAt,
    deriv_mehlerKernel hf.2]
  ring

theorem tendsto_mehlerCoeffA_atTop : Tendsto mehlerCoeffA atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero

theorem tendsto_mehlerCoeffB_atTop : Tendsto mehlerCoeffB atTop (𝓝 1) := by
  have he : mehlerCoeffB = fun t => Real.sqrt (1-(mehlerCoeffA t)^2) := by
    funext t; rw [mehlerCoeffB,mehlerCoeffA_sq]
  rw [he]
  simpa only [Function.comp_def, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_zero, Real.sqrt_one] using Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_mehlerCoeffA_atTop.pow 2))

/-- Pointwise convergence to the Gaussian mean needs only continuity and boundedness. -/
theorem tendsto_mehlerKernel_atTop {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (x : ℝ) :
    Tendsto (fun t => mehlerKernel t f x) atTop (𝓝 (∫ y, f y ∂standardGaussian)) := by
  obtain ⟨C,hC⟩ := hb
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => C)
  · exact Eventually.of_forall fun t => (hf.comp (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => ae_of_all _ (fun y => hC _)
  · exact integrable_const C
  · refine ae_of_all _ (fun y => ?_)
    have ht := (tendsto_mehlerCoeffA_atTop.mul_const x).add (tendsto_mehlerCoeffB_atTop.mul_const y)
    simpa only [Function.comp_def] using (hf.tendsto y).comp (by simpa using ht)

/-- The convergence to the mean also holds in L¹. -/
theorem tendsto_mehlerKernel_L1 {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun t => ∫ x, ‖mehlerKernel t f x-(∫ y, f y ∂standardGaussian)‖ ∂standardGaussian)
      atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := hb
  have hb' : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := ⟨C,hC⟩
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := standardGaussian) (l := atTop) (F := fun t x => ‖mehlerKernel t f x-(∫ y, f y ∂standardGaussian)‖)
    (f := fun _ => (0 : ℝ)) (bound := fun _ => C+‖∫ y, f y ∂standardGaussian‖)
    (Eventually.of_forall fun t => by
      have hc : Continuous (mehlerKernel t f) :=
        (continuous_mehlerKernel hf hb').comp ((continuous_const (y := t)).prodMk continuous_id)
      fun_prop)
    (Eventually.of_forall fun t => ae_of_all _ (fun x => by
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (add_le_add (norm_mehlerKernel_le hC t x) le_rfl)))
    (integrable_const _) (ae_of_all _ (fun x => by
      simpa using ((tendsto_mehlerKernel_atTop hf hb' x).sub (tendsto_const_nhds (x := ∫ y, f y ∂standardGaussian))).norm))
  simpa using h

end Foundations
