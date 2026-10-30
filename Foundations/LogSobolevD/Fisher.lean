import Foundations.LogSobolevD.Mehler

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations
/-- Weighted Cauchy--Schwarz, by completing the square. -/
theorem sq_integral_div_le_integral_sq_div' {X : Type*} [MeasurableSpace X] {μ : Measure X} {u v : X → ℝ}
    (hu : Integrable u μ) (hv : Integrable v μ)
    (hqu : Integrable (fun x => (u x)^2/v x) μ)
    (hvpos : ∀ x, 0 < v x) (hm : 0 < ∫ x, v x ∂μ) :
    (∫ x, u x ∂μ)^2 / (∫ x, v x ∂μ) ≤
      ∫ x, (u x)^2/v x ∂μ := by
  let c := (∫ x, u x ∂μ)/(∫ x, v x ∂μ)
  have he : (∫ x, (u x-c*v x)^2/v x ∂μ) =
      (∫ x, (u x)^2/v x ∂μ) -
      2*c*(∫ x, u x ∂μ) + c^2*(∫ x, v x ∂μ) := by
    calc
      _ = ∫ x, ((u x)^2/v x-2*c*u x)+c^2*v x ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by field_simp [(hvpos x).ne']; ring)
      _ = _ := by
        have hh := integral_add (hqu.sub (hu.const_mul (2*c))) (hv.const_mul (c^2))
        simp only [Pi.sub_apply] at hh
        rw [hh, integral_sub hqu (hu.const_mul (2*c)),integral_const_mul,integral_const_mul]
  have hn : 0 ≤ ∫ x, (u x-c*v x)^2/v x ∂μ :=
    integral_nonneg (fun x => div_nonneg (sq_nonneg _) (hvpos x).le)
  rw [he] at hn
  dsimp [c] at hn
  have heq : 2*((∫ x, u x ∂μ)/(∫ x, v x ∂μ)) *
      (∫ x, u x ∂μ) -
      ((∫ x, u x ∂μ)/(∫ x, v x ∂μ))^2 *
      (∫ x, v x ∂μ) =
      (∫ x, u x ∂μ)^2/(∫ x, v x ∂μ) := by field_simp [hm.ne']; ring
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fisherCoordD (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ := (partialD f i x)^2/f x

def fisherInfoD (f : (ι → ℝ) → ℝ) : ℝ := ∫ x, gradNormSqD f x/f x ∂gaussianProduct ι

theorem continuous_fisherCoordD {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) (i) : Continuous (fisherCoordD f i) :=
  ((hf.continuous_partial i).pow 2).div hf.contDiff.continuous
    (fun x => ne_of_gt (hε.trans_le (hpos x)))

theorem fisherCoordD_bounded {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) (i) :
    ∃ C : ℝ, ∀ x, ‖fisherCoordD f i x‖ ≤ C := by
  obtain ⟨C,hC⟩ := hf.partial_bounded i
  refine ⟨C^2/ε,fun x => ?_⟩
  rw [fisherCoordD,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (hε.le.trans (hpos x)))]
  apply div_le_div₀ (sq_nonneg C) ?_ hε (hpos x)
  simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg (partialD f i x)) (hC x) 2

theorem memLp_fisherCoordD {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) (i) (p : ENNReal) :
    MemLp (fisherCoordD f i) p (gaussianProduct ι) :=
  memLp_gaussianD_of_bounded (continuous_fisherCoordD hf hε hpos i) (fisherCoordD_bounded hf hε hpos i) p

theorem fisherInfoD_eq_sum {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) :
    fisherInfoD f = ∑ i, ∫ x, fisherCoordD f i x ∂gaussianProduct ι := by
  simp only [fisherInfoD,gradNormSqD,Finset.sum_div]
  exact integral_finsetSum _ (fun i _ => (memLp_fisherCoordD hf hε hpos i 1).integrable le_rfl)

theorem fisherCoordD_mehlerKernelD_le {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) (t : ℝ) (i : ι) (x : ι → ℝ) :
    fisherCoordD (mehlerKernelD t f) i x ≤
      (mehlerCoeffA t)^2 * mehlerKernelD t (fisherCoordD f i) x := by
  have hc := continuous_fisherCoordD hf hε hpos i
  have hb := fisherCoordD_bounded hf hε hpos i
  have h := sq_integral_div_le_integral_sq_div'
    (integrable_gaussianD_affine (hf.continuous_partial i) (hf.partial_bounded i) _ _ x)
    (integrable_gaussianD_affine hf.contDiff.continuous hf.bounded _ _ x)
    (integrable_gaussianD_affine hc hb _ _ x)
    (fun y => hε.trans_le (hpos (fun j => mehlerCoeffA t*x j+mehlerCoeffB t*y j)))
    (hε.trans_le (le_mehlerKernelD hf.contDiff.continuous hf.bounded hpos t x))
  dsimp [fisherCoordD]
  rw [partialD_mehlerKernelD hf,mul_pow,mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- Fisher contraction with a rate independent of the finite dimension. -/
theorem fisherD_mehlerKernelD_le {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    fisherInfoD (mehlerKernelD t f) ≤ Real.exp (-2*t)*fisherInfoD f := by
  have hM := isC1BoundedD_mehlerKernelD hf t
  have hl := le_mehlerKernelD hf.contDiff.continuous hf.bounded hpos t
  rw [fisherInfoD_eq_sum hM hε hl,fisherInfoD_eq_sum hf hε hpos,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hc := continuous_fisherCoordD hf hε hpos i
  have hb := fisherCoordD_bounded hf hε hpos i
  have hMK := memLp_gaussianD_of_bounded
    ((continuous_mehlerKernelD hc hb).comp (continuous_const.prodMk continuous_id))
    (by obtain ⟨C,hC⟩ := hb; exact ⟨C,fun x => norm_mehlerKernelD_le hC t x⟩) 1
  calc
    _ ≤ ∫ x, (mehlerCoeffA t)^2 * mehlerKernelD t (fisherCoordD f i) x ∂gaussianProduct ι :=
      integral_mono ((memLp_fisherCoordD hM hε hl i 1).integrable le_rfl)
        (hMK.integrable le_rfl |>.const_mul _) (fisherCoordD_mehlerKernelD_le hf hε hpos t i)
    _ = _ := by rw [integral_const_mul,integral_mehlerKernelD hc hb ht,mehlerCoeffA_sq]

end Foundations
