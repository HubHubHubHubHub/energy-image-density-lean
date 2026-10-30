import Foundations.LogSobolev.MehlerDeriv
import Foundations.LogSobolev.GaussianIBP

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations

theorem hasDerivAt_mehlerCoeffA (t : ℝ) : HasDerivAt mehlerCoeffA (-mehlerCoeffA t) t := by
  change HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t
  simpa only [id_eq,Pi.neg_apply,mul_neg,mul_one] using (hasDerivAt_id t).neg.exp

theorem monotone_mehlerCoeffB : Monotone mehlerCoeffB := by
  intro s t hst
  apply Real.sqrt_le_sqrt
  apply sub_le_sub_left
  exact Real.exp_le_exp.mpr (by linarith)

theorem hasDerivAt_mehlerCoeffB {t : ℝ} (ht : 0 < t) :
    HasDerivAt mehlerCoeffB ((mehlerCoeffA t)^2/mehlerCoeffB t) t := by
  have hp : 0 < 1-Real.exp (-2*t) := by
    have := Real.exp_lt_one_iff.mpr (show -2*t < 0 by linarith)
    linarith
  have he : HasDerivAt (fun s : ℝ => 1-Real.exp (-2*s)) (2*Real.exp (-2*t)) t := by
    exact ((((hasDerivAt_id t).const_mul (-2)).exp).const_sub 1).congr_deriv (by simp; ring)
  exact (he.sqrt hp.ne').congr_deriv (by rw [mehlerCoeffA_sq]; dsimp [mehlerCoeffB]; ring)

theorem hasDerivAt_mehlerKernel_time_raw {f : ℝ → ℝ} (hf : IsC1Bounded f)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => mehlerKernel s f x)
      (∫ y, deriv f (mehlerCoeffA t*x+mehlerCoeffB t*y) *
        (-mehlerCoeffA t*x+(mehlerCoeffA t)^2/mehlerCoeffB t*y) ∂standardGaussian) t := by
  obtain ⟨C,hC⟩ := hf.deriv_bounded
  have hC0 : 0 ≤ C := (norm_nonneg (deriv f 0)).trans (hC 0)
  have hb0 := mehlerCoeffB_pos (half_pos ht)
  have hy : Integrable (fun y : ℝ => ‖y‖) standardGaussian := by
    simpa using (integrable_pow_gaussian 1).norm
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := standardGaussian)
    (F := fun s y => f (mehlerCoeffA s*x+mehlerCoeffB s*y))
    (F' := fun s y => deriv f (mehlerCoeffA s*x+mehlerCoeffB s*y) *
      (-mehlerCoeffA s*x+(mehlerCoeffA s)^2/mehlerCoeffB s*y))
    (bound := fun y => C*(‖x‖+(1/mehlerCoeffB (t/2))*‖y‖))
    (s := Ioi (t/2)) (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun s => (hf.contDiff.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_gaussian_affine hf.contDiff.continuous hf.bounded _ _)
    (by have hc := hf.contDiff.continuous_deriv_one; fun_prop) ?_
    (((integrable_const ‖x‖).add (hy.const_mul _)).const_mul C) ?_).2
  · refine ae_of_all _ (fun y s hs => ?_)
    have hs0 : 0 < s := (half_pos ht).trans hs
    have ha : ‖mehlerCoeffA s‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (mehlerCoeffA_pos s).le]
      exact mehlerCoeffA_le_one hs0.le
    have hb : ‖(mehlerCoeffA s)^2/mehlerCoeffB s‖ ≤ 1/mehlerCoeffB (t/2) := by
      rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (mehlerCoeffB_nonneg s))]
      apply div_le_div₀ zero_le_one ?_ hb0 (monotone_mehlerCoeffB hs.le)
      have ha' := mehlerCoeffA_le_one hs0.le
      nlinarith [mehlerCoeffA_pos s]
    rw [norm_mul]
    apply mul_le_mul (hC _) ?_ (norm_nonneg _) hC0
    calc
      _ ≤ ‖-mehlerCoeffA s*x‖+‖(mehlerCoeffA s)^2/mehlerCoeffB s*y‖ := norm_add_le _ _
      _ ≤ _ := by
        simp only [norm_mul,norm_neg]
        exact add_le_add (by simpa using mul_le_mul_of_nonneg_right ha (norm_nonneg x))
          (mul_le_mul_of_nonneg_right hb (norm_nonneg y))
  · refine ae_of_all _ (fun y s hs => ?_)
    exact (hf.hasDerivAt _).comp s ((hasDerivAt_mehlerCoeffA s).mul_const x |>.add
      ((hasDerivAt_mehlerCoeffB ((half_pos ht).trans hs)).mul_const y))

/-- The OU equation is an ordinary derivative for strictly positive times. -/
theorem hasDerivAt_mehlerKernel_time {f : ℝ → ℝ} (hf : IsC2Bounded f)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => mehlerKernel s f x)
      (deriv (deriv (mehlerKernel t f)) x-x*deriv (mehlerKernel t f) x) t := by
  apply (hasDerivAt_mehlerKernel_time_raw hf.1 ht x).congr_deriv
  have hi := integrable_gaussian_affine hf.2.contDiff.continuous hf.2.bounded
    (mehlerCoeffA t*x) (mehlerCoeffB t)
  have hiy := integrable_id_mul_bounded (hf.2.affine (mehlerCoeffA t*x) (mehlerCoeffB t)).contDiff.continuous
    (hf.2.affine (mehlerCoeffA t*x) (mehlerCoeffB t)).bounded
  calc
    _ = (-mehlerCoeffA t*x)*mehlerKernel t (deriv f) x +
        ((mehlerCoeffA t)^2/mehlerCoeffB t)*
          (∫ y, y*deriv f (mehlerCoeffA t*x+mehlerCoeffB t*y) ∂standardGaussian) := by
      dsimp only [mehlerKernel]
      rw [← integral_const_mul,← integral_const_mul,← integral_add (hi.const_mul _) (hiy.const_mul _)]
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by ring)
    _ = _ := by
      rw [integral_gaussian_affine_deriv hf.2,deriv2_mehlerKernel hf,deriv_mehlerKernel hf.1]
      change _ = _
      dsimp only [mehlerKernel]
      field_simp [(mehlerCoeffB_pos ht).ne']
      <;> ring

end Foundations
