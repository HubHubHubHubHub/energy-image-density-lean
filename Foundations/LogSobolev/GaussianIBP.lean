import Foundations.LogSobolev.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations

theorem integral_gaussian_density (f : ℝ → ℝ) :
    (∫ x, f x ∂standardGaussian) = ∫ x, f x * gaussianPDFReal 0 1 x := by
  simpa only [standardGaussian,smul_eq_mul,mul_comm] using
    (integral_gaussianReal_eq_integral_smul (f := f) (one_ne_zero : (1 : NNReal) ≠ 0))

theorem integrable_mul_gaussianDensity {f : ℝ → ℝ} (hf : Integrable f standardGaussian) :
    Integrable (fun x => f x * gaussianPDFReal 0 1 x) := by
  rw [standardGaussian,gaussianReal_of_var_ne_zero _ (one_ne_zero : (1 : NNReal) ≠ 0)] at hf
  have h := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (ae_of_all _ (fun x => gaussianPDF_lt_top))).mp hf
  simpa only [toReal_gaussianPDF,smul_eq_mul,mul_comm] using h

theorem integrable_id_mul_bounded {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => x*f x) standardGaussian := by
  obtain ⟨C,hC⟩ := hb
  have hi : Integrable (fun x : ℝ => x) standardGaussian := by simpa using integrable_pow_gaussian 1
  apply (hi.norm.mul_const C).mono' (by fun_prop)
  exact ae_of_all _ (fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg x))

/-- Gaussian integration by parts for C¹_b, with both improper boundary limits proved. -/
theorem integral_deriv_gaussian {f : ℝ → ℝ} (hf : IsC1Bounded f) :
    (∫ x, deriv f x ∂standardGaussian) = ∫ x, x*f x ∂standardGaussian := by
  have hd : ∀ x, HasDerivAt (fun y => f y * gaussianPDFReal 0 1 y)
      ((deriv f x-x*f x)*gaussianPDFReal 0 1 x) x := by
    intro x
    apply ((hf.hasDerivAt x).mul (hasDerivAt_gaussianDensity x)).congr_deriv
    ring
  have hi := integrable_mul_gaussianDensity ((hf.memLp 1).integrable le_rfl)
  have hid := integrable_mul_gaussianDensity (((hf.memLp_deriv 1).integrable le_rfl).sub
    (integrable_id_mul_bounded hf.contDiff.continuous hf.bounded))
  have ht := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (fun x _ => hd x) hid.integrableOn hi.integrableOn
  have hb := tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
    (fun x _ => hd x) hid.integrableOn hi.integrableOn
  have h := integral_of_hasDerivAt_of_tendsto hd hid hb ht
  rw [← integral_gaussian_density,integral_sub ((hf.memLp_deriv 1).integrable le_rfl)
    (integrable_id_mul_bounded hf.contDiff.continuous hf.bounded)] at h
  exact sub_eq_zero.mp (by simpa using h)

theorem IsC1Bounded.affine {f : ℝ → ℝ} (hf : IsC1Bounded f) (a b : ℝ) :
    IsC1Bounded (fun x => f (a+b*x)) := by
  have he : deriv (fun x => f (a+b*x)) = fun x => b*deriv f (a+b*x) := by
    funext x
    simpa only [Function.comp_def,id_eq,mul_one,mul_comm] using ((hf.hasDerivAt _).comp x
      (((hasDerivAt_id x).const_mul b).const_add a)).deriv
  refine ⟨hf.contDiff.comp (by fun_prop),?_,?_⟩
  · obtain ⟨C,hC⟩ := hf.bounded
    exact ⟨C,fun x => hC _⟩
  · obtain ⟨C,hC⟩ := hf.deriv_bounded
    refine ⟨‖b‖*C,fun x => ?_⟩
    rw [he,norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

theorem integral_gaussian_affine_deriv {f : ℝ → ℝ} (hf : IsC1Bounded f) (a b : ℝ) :
    (∫ y, y*f (a+b*y) ∂standardGaussian) = b * ∫ y, deriv f (a+b*y) ∂standardGaussian := by
  rw [← integral_deriv_gaussian (hf.affine a b),← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    simpa only [Function.comp_def,id_eq,mul_one,mul_comm] using
      ((hf.hasDerivAt _).comp y (((hasDerivAt_id y).const_mul b).const_add a)).deriv)

end Foundations
