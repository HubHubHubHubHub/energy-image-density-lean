import Foundations.LogSobolev.MehlerDeriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations

def fisherDensity (f : ℝ → ℝ) (x : ℝ) : ℝ := (deriv f x)^2 / f x
def fisherInfo (f : ℝ → ℝ) : ℝ := ∫ x, fisherDensity f x ∂standardGaussian

theorem continuous_fisherDensity {f : ℝ → ℝ} (hf : IsC1Bounded f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) : Continuous (fisherDensity f) :=
  (hf.contDiff.continuous_deriv_one.pow 2).div hf.contDiff.continuous
    (fun x => ne_of_gt (hε.trans_le (hpos x)))

theorem fisherDensity_bounded {f : ℝ → ℝ} (hf : IsC1Bounded f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) :
    ∃ C : ℝ, ∀ x, ‖fisherDensity f x‖ ≤ C := by
  obtain ⟨C,hC⟩ := hf.deriv_bounded
  have hC0 : 0 ≤ C := (norm_nonneg (deriv f 0)).trans (hC 0)
  refine ⟨C^2/ε,fun x => ?_⟩
  rw [fisherDensity,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (hε.le.trans (hpos x)))]
  apply div_le_div₀ (sq_nonneg C) ?_ hε (hpos x)
  simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg (deriv f x)) (hC x) 2

theorem fisherDensity_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℝ) :
    0 ≤ fisherDensity f x := div_nonneg (sq_nonneg _) (hf x)

theorem memLp_fisherDensity {f : ℝ → ℝ} (hf : IsC1Bounded f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) (p : ENNReal) :
    MemLp (fisherDensity f) p standardGaussian :=
  memLp_gaussian_of_bounded (continuous_fisherDensity hf hε hpos) (fisherDensity_bounded hf hε hpos) p

/-- Weighted Cauchy--Schwarz, by completing the square. -/
theorem sq_integral_div_le_integral_sq_div {u v : ℝ → ℝ}
    (hu : Integrable u standardGaussian) (hv : Integrable v standardGaussian)
    (hqu : Integrable (fun x => (u x)^2/v x) standardGaussian)
    (hvpos : ∀ x, 0 < v x) (hm : 0 < ∫ x, v x ∂standardGaussian) :
    (∫ x, u x ∂standardGaussian)^2 / (∫ x, v x ∂standardGaussian) ≤
      ∫ x, (u x)^2/v x ∂standardGaussian := by
  let c := (∫ x, u x ∂standardGaussian)/(∫ x, v x ∂standardGaussian)
  have he : (∫ x, (u x-c*v x)^2/v x ∂standardGaussian) =
      (∫ x, (u x)^2/v x ∂standardGaussian) -
      2*c*(∫ x, u x ∂standardGaussian) + c^2*(∫ x, v x ∂standardGaussian) := by
    calc
      _ = ∫ x, ((u x)^2/v x-2*c*u x)+c^2*v x ∂standardGaussian := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by field_simp [(hvpos x).ne']; ring)
      _ = _ := by
        have hh := integral_add (hqu.sub (hu.const_mul (2*c))) (hv.const_mul (c^2))
        simp only [Pi.sub_apply] at hh
        rw [hh, integral_sub hqu (hu.const_mul (2*c)),integral_const_mul,integral_const_mul]
  have hn : 0 ≤ ∫ x, (u x-c*v x)^2/v x ∂standardGaussian :=
    integral_nonneg (fun x => div_nonneg (sq_nonneg _) (hvpos x).le)
  rw [he] at hn
  dsimp [c] at hn
  have heq : 2*((∫ x, u x ∂standardGaussian)/(∫ x, v x ∂standardGaussian)) *
      (∫ x, u x ∂standardGaussian) -
      ((∫ x, u x ∂standardGaussian)/(∫ x, v x ∂standardGaussian))^2 *
      (∫ x, v x ∂standardGaussian) =
      (∫ x, u x ∂standardGaussian)^2/(∫ x, v x ∂standardGaussian) := by field_simp [hm.ne']; ring
  linarith

theorem fisherDensity_mehlerKernel_le {f : ℝ → ℝ} (hf : IsC1Bounded f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) (t x : ℝ) :
    fisherDensity (mehlerKernel t f) x ≤
      (mehlerCoeffA t)^2 * mehlerKernel t (fisherDensity f) x := by
  have hc := continuous_fisherDensity hf hε hpos
  have hb := fisherDensity_bounded hf hε hpos
  have h := sq_integral_div_le_integral_sq_div
    (integrable_gaussian_affine hf.contDiff.continuous_deriv_one hf.deriv_bounded _ _)
    (integrable_gaussian_affine hf.contDiff.continuous hf.bounded _ _)
    (integrable_gaussian_affine hc hb _ _)
    (fun y => hε.trans_le (hpos (mehlerCoeffA t*x+mehlerCoeffB t*y)))
    (hε.trans_le (le_mehlerKernel hf.contDiff.continuous hf.bounded hpos t x))
  dsimp [fisherDensity]
  rw [deriv_mehlerKernel hf,mul_pow,mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- The Gaussian Fisher information contracts at the exact rate exp(-2t). -/
theorem fisher_mehlerKernel_le {f : ℝ → ℝ} (hf : IsC1Bounded f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    fisherInfo (mehlerKernel t f) ≤ Real.exp (-2*t)*fisherInfo f := by
  have hM := isC1Bounded_mehlerKernel hf t
  have hl := le_mehlerKernel hf.contDiff.continuous hf.bounded hpos t
  have hF := memLp_fisherDensity hf hε hpos 2
  have hc := continuous_fisherDensity hf hε hpos
  have hb := fisherDensity_bounded hf hε hpos
  have hMK := memLp_gaussian_of_bounded
    ((continuous_mehlerKernel hc hb).comp (continuous_const.prodMk continuous_id))
    (by obtain ⟨C,hC⟩ := hb; exact ⟨C,fun x => norm_mehlerKernel_le hC t x⟩) 1
  calc
    _ ≤ ∫ x, (mehlerCoeffA t)^2 * mehlerKernel t (fisherDensity f) x ∂standardGaussian :=
      integral_mono ((memLp_fisherDensity hM hε hl 1).integrable le_rfl)
        (hMK.integrable le_rfl |>.const_mul _) (fisherDensity_mehlerKernel_le hf hε hpos t)
    _ = _ := by rw [integral_const_mul,integral_mehlerKernel hF ht,mehlerCoeffA_sq]; rfl

end Foundations
