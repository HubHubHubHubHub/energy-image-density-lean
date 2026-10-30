import GeometricMeasure.Analysis.HeatKernel
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Heat Hessian

## Main results
Gaussian Hessian and third derivative, dilation, L¹ bounds, translation and tail. Unit directions
and strictly positive time are explicit in the estimates.

Bibliographic context: De Philippis–Rindler, pp. 9–10, (2.9)–(2.12). The heat-kernel and energy
estimates specialize the distributional framework.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped Topology RealInnerProductSpace Convolution ContDiff
namespace GeometricMeasure
variable {d : ℕ}

/--
Explicit Gaussian Hessian, with arbitrary directions. Source: DPR context, transcription pp. 9–10.
Exact scope: parameters, assumptions and conclusion below.
-/
def heatSecondDirectional (d : ℕ) (t : ℝ) (v w x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (⟪v, x⟫ * ⟪w, x⟫ / (4 * t ^ 2) - ⟪v, w⟫ / (2 * t)) * heatKernel d t x

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem heatSecondDirectional_eq_fderiv {t : ℝ} (ht : 0 < t)
    (v w x : EuclideanSpace ℝ (Fin d)) :
    heatSecondDirectional d t v w x = fderiv ℝ (heatDirectional d t v) x w := by
  have hlin := (((innerSL ℝ v).hasFDerivAt (x := x)).mul_const (2 * t)⁻¹).neg
  have h := hlin.mul ((differentiable_heatKernel ht x).hasFDerivAt)
  change HasFDerivAt (heatDirectional d t v) _ x at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply, neg_apply, smul_eq_mul, Pi.neg_apply,
    innerSL_apply_apply, ← heatDirectional_eq_fderiv ht, heatDirectional, heatSecondDirectional]
  field_simp
  ring

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem heatSecondDirectional_symm (d : ℕ) (t : ℝ)
    (v w x : EuclideanSpace ℝ (Fin d)) :
    heatSecondDirectional d t v w x = heatSecondDirectional d t w v x := by
  simp only [heatSecondDirectional, real_inner_comm v w]
  ring

/--
Dilation in multiplicative form, without ambiguous negative powers. Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem heatSecondDirectional_scale {t : ℝ} (ht : 0 < t)
    (v w z : EuclideanSpace ℝ (Fin d)) :
    Real.sqrt t ^ d * t * heatSecondDirectional d t v w (Real.sqrt t • z) =
      heatSecondDirectional d 1 v w z := by
  have hs := Real.sq_sqrt ht.le
  have hk := heatKernel_scale ht z
  unfold heatSecondDirectional
  simp only [inner_smul_right, one_pow, mul_one]
  have he : t * ((Real.sqrt t * ⟪v, z⟫) * (Real.sqrt t * ⟪w, z⟫) /
      (4 * t ^ 2) - ⟪v, w⟫ / (2 * t)) =
      ⟪v, z⟫ * ⟪w, z⟫ / 4 - ⟪v, w⟫ / 2 := by
    field_simp
    rw [hs]
    ring
  calc
    _ = (t * ((Real.sqrt t * ⟪v, z⟫) * (Real.sqrt t * ⟪w, z⟫) /
      (4 * t ^ 2) - ⟪v, w⟫ / (2 * t))) *
        (Real.sqrt t ^ d * heatKernel d t (Real.sqrt t • z)) := by ring
    _ = _ := by rw [he, hk]

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem heatKernel_le_at_positive_time {η t : ℝ} (hη : 0 < η) (ht : η ≤ t)
    (x : EuclideanSpace ℝ (Fin d)) :
    heatKernel d t x ≤ ((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹ := by
  have ht0 := hη.trans_le ht
  have hden : (4 * Real.pi * η) ^ ((d : ℝ) / 2) ≤
      (4 * Real.pi * t) ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [Real.pi_pos]) (by positivity)
  have hinv : ((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹ ≤
      ((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹ :=
    (inv_le_inv₀ (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (by positivity) _)).2 hden
  simp only [heatKernel, if_pos ht0]
  have he : Real.exp (-(4*t)⁻¹ * ‖x‖^2) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _))
  exact (mul_le_of_le_one_right (by positivity) he).trans hinv

/--
The inequality r² ≤ 2(e^r + e^{-r}), without Gaussian moments. Source: DPR context, transcription
pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem sq_le_two_mul_exp_add_exp_neg (r : ℝ) :
    r ^ 2 ≤ 2 * (Real.exp r + Real.exp (-r)) := by
  rcases le_total 0 r with hr | hr
  · have h1 := Real.quadratic_le_exp_of_nonneg hr
    have h2 := Real.exp_pos (-r)
    nlinarith
  · have h1 := Real.quadratic_le_exp_of_nonneg (neg_nonneg.mpr hr)
    have h2 := Real.exp_pos r
    nlinarith

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
private theorem heatTilt_eq_mul {t : ℝ} (ht : 0 < t) (c : ℝ) (v x : EuclideanSpace ℝ (Fin d)) :
    heatTilt d t c v x = heatKernel d t x * Real.exp (c * ⟪v, x⟫) := by
  simp only [heatTilt, heatKernel, if_pos ht, Real.exp_add]
  ring

/--
Integrable pointwise majorant of the Gaussian Hessian, for unit directions. Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem norm_heatSecondDirectional_le {t : ℝ} (ht : 0 < t)
    {v w : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖heatSecondDirectional d t v w x‖ ≤
      (4 * t)⁻¹ * (heatTilt d t (Real.sqrt t)⁻¹ v x + heatTilt d t (-(Real.sqrt t)⁻¹) v x +
        heatTilt d t (Real.sqrt t)⁻¹ w x + heatTilt d t (-(Real.sqrt t)⁻¹) w x) +
      (2 * t)⁻¹ * heatKernel d t x := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hK := heatKernel_nonneg d t x
  have hvw : |⟪v, w⟫| ≤ 1 := by
    have h := abs_real_inner_le_norm v w
    rw [hv, hw, one_mul] at h
    exact h
  rw [heatTilt_eq_mul ht, heatTilt_eq_mul ht, heatTilt_eq_mul ht, heatTilt_eq_mul ht]
  set p := ⟪v, x⟫ with hp_def
  set q := ⟪w, x⟫ with hq_def
  set s := Real.sqrt t with hs_def
  have hp := sq_le_two_mul_exp_add_exp_neg (s⁻¹ * p)
  have hq := sq_le_two_mul_exp_add_exp_neg (s⁻¹ * q)
  have hp' : p ^ 2 ≤ 2 * t * (Real.exp (s⁻¹ * p) + Real.exp (-(s⁻¹ * p))) := by
    have he : (s⁻¹ * p) ^ 2 = p ^ 2 / t := by
      rw [mul_pow, inv_pow, hs2]; ring
    rw [he, div_le_iff₀ ht] at hp
    linarith
  have hq' : q ^ 2 ≤ 2 * t * (Real.exp (s⁻¹ * q) + Real.exp (-(s⁻¹ * q))) := by
    have he : (s⁻¹ * q) ^ 2 = q ^ 2 / t := by
      rw [mul_pow, inv_pow, hs2]; ring
    rw [he, div_le_iff₀ ht] at hq
    linarith
  have hpq : |p * q| ≤ (p ^ 2 + q ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|p| - |q|), sq_abs p, sq_abs q]
  have hfirst : |p * q / (4 * t ^ 2)| ≤ (4 * t)⁻¹ *
      (Real.exp (s⁻¹ * p) + Real.exp (-s⁻¹ * p) + Real.exp (s⁻¹ * q) + Real.exp (-s⁻¹ * q)) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * t ^ 2), div_le_iff₀ (by positivity)]
    have e1 : -s⁻¹ * p = -(s⁻¹ * p) := by ring
    have e2 : -s⁻¹ * q = -(s⁻¹ * q) := by ring
    rw [e1, e2]
    have h4 : (4 * t)⁻¹ * (4 * t ^ 2) = t := by field_simp
    set S := Real.exp (s⁻¹ * p) + Real.exp (-(s⁻¹ * p)) +
      Real.exp (s⁻¹ * q) + Real.exp (-(s⁻¹ * q)) with hS
    calc |p * q| ≤ (p ^ 2 + q ^ 2) / 2 := hpq
      _ ≤ t * S := by rw [hS]; linarith
      _ = (4 * t)⁻¹ * S * (4 * t ^ 2) := by
        rw [show (4 * t)⁻¹ * S * (4 * t ^ 2) = S * ((4 * t)⁻¹ * (4 * t ^ 2)) by ring, h4]
        ring
  have hsecond : |⟪v, w⟫ / (2 * t)| ≤ (2 * t)⁻¹ := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * t), div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) hvw
  unfold heatSecondDirectional
  rw [norm_mul, Real.norm_of_nonneg hK, Real.norm_eq_abs]
  calc |p * q / (4 * t ^ 2) - ⟪v, w⟫ / (2 * t)| * heatKernel d t x ≤
      (|p * q / (4 * t ^ 2)| + |⟪v, w⟫ / (2 * t)|) * heatKernel d t x :=
        mul_le_mul_of_nonneg_right (abs_sub _ _) hK
    _ ≤ ((4 * t)⁻¹ * (Real.exp (s⁻¹ * p) + Real.exp (-s⁻¹ * p) + Real.exp (s⁻¹ * q) +
          Real.exp (-s⁻¹ * q)) + (2 * t)⁻¹) * heatKernel d t x :=
        mul_le_mul_of_nonneg_right (add_le_add hfirst hsecond) hK
    _ = _ := by ring

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem measurable_heatSecondDirectional (v w : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      heatSecondDirectional d p.1 v w p.2) := by
  unfold heatSecondDirectional
  exact (by fun_prop : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
    ⟪v, p.2⟫ * ⟪w, p.2⟫ / (4 * p.1 ^ 2) - ⟪v, w⟫ / (2 * p.1))).mul (measurable_heatKernel d)

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integrable_heatSecondDirectional {t : ℝ} (ht : 0 < t)
    {v w : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    Integrable (heatSecondDirectional d t v w) := by
  have i1 := integrable_heatTilt ht (Real.sqrt t)⁻¹ v
  have i2 := integrable_heatTilt ht (-(Real.sqrt t)⁻¹) v
  have i3 := integrable_heatTilt ht (Real.sqrt t)⁻¹ w
  have i4 := integrable_heatTilt ht (-(Real.sqrt t)⁻¹) w
  have hI : Integrable (fun x => (4 * t)⁻¹ * (heatTilt d t (Real.sqrt t)⁻¹ v x +
      heatTilt d t (-(Real.sqrt t)⁻¹) v x + heatTilt d t (Real.sqrt t)⁻¹ w x +
      heatTilt d t (-(Real.sqrt t)⁻¹) w x) + (2 * t)⁻¹ * heatKernel d t x) :=
    ((((i1.add i2).add i3).add i4).const_mul _).add ((integrable_heatKernel d t).const_mul _)
  have hm : AEStronglyMeasurable (heatSecondDirectional d t v w) volume :=
    ((measurable_heatSecondDirectional v w).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact hI.mono' hm (ae_of_all _ (norm_heatSecondDirectional_le ht hv hw))

/--
For t > 0 and unit directions, the Gaussian Hessian has L¹ norm at most (e + 1/2)/t, without the
Gamma function. Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions
and conclusion below.
-/
theorem integral_norm_heatSecondDirectional_le {t : ℝ} (ht : 0 < t)
    {v w : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    (∫ x, ‖heatSecondDirectional d t v w x‖) ≤ (Real.exp 1 + 1 / 2) / t := by
  have hs2 : t * ((Real.sqrt t)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt ht.le, mul_inv_cancel₀ ht.ne']
  have i1 := integrable_heatTilt ht (Real.sqrt t)⁻¹ v
  have i2 := integrable_heatTilt ht (-(Real.sqrt t)⁻¹) v
  have i3 := integrable_heatTilt ht (Real.sqrt t)⁻¹ w
  have i4 := integrable_heatTilt ht (-(Real.sqrt t)⁻¹) w
  have hA : Integrable (fun x => (4 * t)⁻¹ * (heatTilt d t (Real.sqrt t)⁻¹ v x +
      heatTilt d t (-(Real.sqrt t)⁻¹) v x + heatTilt d t (Real.sqrt t)⁻¹ w x +
      heatTilt d t (-(Real.sqrt t)⁻¹) w x)) :=
    (((i1.add i2).add i3).add i4).const_mul _
  have hB : Integrable (fun x => (2 * t)⁻¹ * heatKernel d t x) :=
    (integrable_heatKernel d t).const_mul _
  have hS : (∫ x, (heatTilt d t (Real.sqrt t)⁻¹ v x +
      heatTilt d t (-(Real.sqrt t)⁻¹) v x + heatTilt d t (Real.sqrt t)⁻¹ w x +
      heatTilt d t (-(Real.sqrt t)⁻¹) w x)) = 4 * Real.exp 1 := by
    have j12 : Integrable (fun x => heatTilt d t (Real.sqrt t)⁻¹ v x +
        heatTilt d t (-(Real.sqrt t)⁻¹) v x) := i1.add i2
    have j123 : Integrable (fun x => heatTilt d t (Real.sqrt t)⁻¹ v x +
        heatTilt d t (-(Real.sqrt t)⁻¹) v x + heatTilt d t (Real.sqrt t)⁻¹ w x) := j12.add i3
    rw [integral_add j123 i4, integral_add j12 i3, integral_add i1 i2, integral_heatTilt ht, integral_heatTilt ht, integral_heatTilt ht,
      integral_heatTilt ht]
    simp only [neg_sq, hv, hw, one_pow, mul_one, hs2]
    ring
  calc (∫ x, ‖heatSecondDirectional d t v w x‖) ≤
      ∫ x, ((4 * t)⁻¹ * (heatTilt d t (Real.sqrt t)⁻¹ v x + heatTilt d t (-(Real.sqrt t)⁻¹) v x +
        heatTilt d t (Real.sqrt t)⁻¹ w x + heatTilt d t (-(Real.sqrt t)⁻¹) w x) +
      (2 * t)⁻¹ * heatKernel d t x) :=
        integral_mono (integrable_heatSecondDirectional ht hv hw).norm (hA.add hB)
          (norm_heatSecondDirectional_le ht hv hw)
    _ = (4 * t)⁻¹ * (4 * Real.exp 1) + (2 * t)⁻¹ := by
      rw [integral_add hA hB, integral_const_mul, integral_const_mul,
        integral_heatKernel d ht, hS, mul_one]
    _ = (Real.exp 1 + 1 / 2) / t := by field_simp

/--
Uniform bound on the Gaussian Hessian at times t ≥ η > 0, for unit directions. Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem norm_heatSecondDirectional_le_sup {η t : ℝ} (hη : 0 < η) (ht : η ≤ t)
    {v w : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖heatSecondDirectional d t v w x‖ ≤
      3 / (2 * η) * ((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹ := by
  have ht0 : 0 < t := hη.trans_le ht
  have hK := heatKernel_nonneg d t x
  have hKle := heatKernel_le_at_positive_time hη ht x
  have hvw : |⟪v, w⟫| ≤ 1 := by
    have h := abs_real_inner_le_norm v w
    rw [hv, hw, one_mul] at h
    exact h
  have hpq : |⟪v, x⟫ * ⟪w, x⟫| ≤ ‖x‖ ^ 2 := by
    rw [abs_mul]
    have h1 := abs_real_inner_le_norm v x
    have h2 := abs_real_inner_le_norm w x
    rw [hv, one_mul] at h1
    rw [hw, one_mul] at h2
    nlinarith [abs_nonneg ⟪v, x⟫, abs_nonneg ⟪w, x⟫]
  -- s e^{-s} ≤ 1 with s = ‖x‖²/(4t)
  have hdecay : ‖x‖ ^ 2 / (4 * t) * heatKernel d t x ≤ ((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹ := by
    simp only [heatKernel, if_pos ht0]
    set s := ‖x‖ ^ 2 / (4 * t)
    have hes : -(4 * t)⁻¹ * ‖x‖ ^ 2 = -s := by simp only [s]; ring
    rw [hes]
    have h1 : s * Real.exp (-s) ≤ 1 := by
      have := Real.add_one_le_exp s
      have hpos := Real.exp_pos (-s)
      have : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
      nlinarith
    have hc : 0 ≤ ((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹ := by positivity
    calc s * (((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹ * Real.exp (-s)) =
        ((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹ * (s * Real.exp (-s)) := by ring
      _ ≤ ((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 hc
      _ = _ := mul_one _
  have hct : ((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹ ≤ ((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹ := by
    have hden : (4 * Real.pi * η) ^ ((d : ℝ) / 2) ≤ (4 * Real.pi * t) ^ ((d : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith [Real.pi_pos]) (by positivity)
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (by positivity) _)).2 hden
  have hC : 0 ≤ ((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹ := by positivity
  unfold heatSecondDirectional
  rw [norm_mul, Real.norm_of_nonneg hK, Real.norm_eq_abs]
  have hab : |⟪v, x⟫ * ⟪w, x⟫ / (4 * t ^ 2) - ⟪v, w⟫ / (2 * t)| ≤
      ‖x‖ ^ 2 / (4 * t) * t⁻¹ + (2 * t)⁻¹ := by
    calc _ ≤ |⟪v, x⟫ * ⟪w, x⟫ / (4 * t ^ 2)| + |⟪v, w⟫ / (2 * t)| := abs_sub _ _
      _ ≤ _ := by
        apply add_le_add
        · rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * t ^ 2)]
          have he : ‖x‖ ^ 2 / (4 * t) * t⁻¹ = ‖x‖ ^ 2 / (4 * t ^ 2) := by field_simp
          rw [he]
          exact div_le_div_of_nonneg_right hpq (by positivity)
        · rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * t), div_eq_mul_inv]
          exact mul_le_of_le_one_left (by positivity) hvw
  have hti : t⁻¹ ≤ η⁻¹ := (inv_le_inv₀ ht0 hη).2 ht
  have hti2 : (2 * t)⁻¹ ≤ (2 * η)⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).2 (by linarith)
  calc |⟪v, x⟫ * ⟪w, x⟫ / (4 * t ^ 2) - ⟪v, w⟫ / (2 * t)| * heatKernel d t x ≤
      (‖x‖ ^ 2 / (4 * t) * t⁻¹ + (2 * t)⁻¹) * heatKernel d t x :=
        mul_le_mul_of_nonneg_right hab hK
    _ = t⁻¹ * (‖x‖ ^ 2 / (4 * t) * heatKernel d t x) + (2 * t)⁻¹ * heatKernel d t x := by ring
    _ ≤ η⁻¹ * ((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹ +
        (2 * η)⁻¹ * ((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹ := by
      apply add_le_add
      · exact mul_le_mul hti (hdecay.trans hct) (by positivity) (by positivity)
      · exact mul_le_mul hti2 hKle hK (by positivity)
    _ = _ := by field_simp; ring


/--
Directional derivative (in u) of the Gaussian Hessian ∂v∂w H_t. Source: DPR context, transcription
pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
def heatThirdDirectional (d : ℕ) (t : ℝ) (v w u x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ((⟪v, u⟫ * ⟪w, x⟫ + ⟪v, x⟫ * ⟪w, u⟫) / (4 * t ^ 2) -
    ⟪u, x⟫ / (2 * t) * (⟪v, x⟫ * ⟪w, x⟫ / (4 * t ^ 2) - ⟪v, w⟫ / (2 * t))) *
    heatKernel d t x

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem hasFDerivAt_heatSecondDirectional {t : ℝ} (ht : 0 < t)
    (v w x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (heatSecondDirectional d t v w)
      (fderiv ℝ (heatSecondDirectional d t v w) x) x := by
  have hP := ((((innerSL ℝ v).hasFDerivAt (x := x)).mul
    ((innerSL ℝ w).hasFDerivAt (x := x))).mul_const (4 * t ^ 2)⁻¹).sub_const
    (⟪v, w⟫ / (2 * t))
  have h := hP.mul ((differentiable_heatKernel ht x).hasFDerivAt)
  change HasFDerivAt (heatSecondDirectional d t v w) _ x at h
  exact h.differentiableAt.hasFDerivAt

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem heatThirdDirectional_eq_fderiv {t : ℝ} (ht : 0 < t)
    (v w u x : EuclideanSpace ℝ (Fin d)) :
    heatThirdDirectional d t v w u x = fderiv ℝ (heatSecondDirectional d t v w) x u := by
  have hP := ((((innerSL ℝ v).hasFDerivAt (x := x)).mul
    ((innerSL ℝ w).hasFDerivAt (x := x))).mul_const (4 * t ^ 2)⁻¹).sub_const
    (⟪v, w⟫ / (2 * t))
  have h := hP.mul ((differentiable_heatKernel ht x).hasFDerivAt)
  change HasFDerivAt (heatSecondDirectional d t v w) _ x at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, Pi.mul_apply,
    innerSL_apply_apply, ← heatDirectional_eq_fderiv ht, heatDirectional,
    heatThirdDirectional]
  ring

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem heatThirdDirectional_smul (t : ℝ) (v w e x : EuclideanSpace ℝ (Fin d)) (c : ℝ) :
    heatThirdDirectional d t v w (c • e) x = c * heatThirdDirectional d t v w e x := by
  simp only [heatThirdDirectional, real_inner_smul_left, real_inner_smul_right]
  ring

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem continuous_heatThirdDirectional {t : ℝ} (ht : 0 < t)
    (v w u : EuclideanSpace ℝ (Fin d)) : Continuous (heatThirdDirectional d t v w u) := by
  have hi (z : EuclideanSpace ℝ (Fin d)) :
      Continuous (fun x : EuclideanSpace ℝ (Fin d) => ⟪z, x⟫) :=
    continuous_const.inner continuous_id
  have hK : Continuous (heatKernel d t) := (differentiable_heatKernel ht).continuous
  unfold heatThirdDirectional
  exact (((((continuous_const.mul (hi w)).add ((hi v).mul continuous_const)).mul
    continuous_const).sub (((hi u).mul continuous_const).mul
    ((((hi v).mul (hi w)).mul continuous_const).sub continuous_const)))).mul hK

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem abs_cube_le_exp_add_exp_neg (r : ℝ) :
    |r| ^ 3 ≤ 6 * (Real.exp r + Real.exp (-r)) := by
  have h := Real.pow_div_factorial_le_exp |r| (abs_nonneg r) 3
  have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf, div_le_iff₀ (by norm_num)] at h
  have hp := Real.exp_pos r
  have hm := Real.exp_pos (-r)
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr] at h ⊢
    nlinarith
  · rw [abs_of_nonpos hr] at h ⊢
    nlinarith

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
private theorem three_mul_abs_le (a b c : ℝ) :
    |a * b * c| ≤ (|a| ^ 3 + |b| ^ 3 + |c| ^ 3) / 3 := by
  rw [abs_mul, abs_mul]
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have hc := abs_nonneg c
  nlinarith [mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (|a| - |b|)),
    mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (|b| - |c|)),
    mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (|c| - |a|))]

/--
Pointwise majorant of the third derivative at t > 0, for unit directions. Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem norm_heatThirdDirectional_le {t : ℝ} (ht : 0 < t)
    {v w u : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖heatThirdDirectional d t v w u x‖ ≤
      (2 * t * Real.sqrt t)⁻¹ *
        (heatTilt d t (Real.sqrt t)⁻¹ v x + heatTilt d t (-(Real.sqrt t)⁻¹) v x +
         heatTilt d t (Real.sqrt t)⁻¹ w x + heatTilt d t (-(Real.sqrt t)⁻¹) w x +
         heatTilt d t (Real.sqrt t)⁻¹ u x + heatTilt d t (-(Real.sqrt t)⁻¹) u x) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hK := heatKernel_nonneg d t x
  have h1 (y z : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) : |⟪y, z⟫| ≤ 1 := by
    have h := abs_real_inner_le_norm y z
    rw [hy, hz, one_mul] at h
    exact h
  rw [heatTilt_eq_mul ht, heatTilt_eq_mul ht, heatTilt_eq_mul ht, heatTilt_eq_mul ht,
    heatTilt_eq_mul ht, heatTilt_eq_mul ht]
  set s := Real.sqrt t with hs_def
  set α := s⁻¹ * ⟪v, x⟫ with hα
  set β := s⁻¹ * ⟪w, x⟫ with hβ
  set γ := s⁻¹ * ⟪u, x⟫ with hγ
  have hpv : ⟪v, x⟫ = s * α := by rw [hα, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  have hpw : ⟪w, x⟫ = s * β := by rw [hβ, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  have hpu : ⟪u, x⟫ = s * γ := by rw [hγ, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  have hform : heatThirdDirectional d t v w u x = (4 * t * s)⁻¹ *
      (⟪v, u⟫ * β + α * ⟪w, u⟫ - γ * α * β / 2 + γ * ⟪v, w⟫) * heatKernel d t x := by
    unfold heatThirdDirectional
    rw [hpv, hpw, hpu, ← hs2]
    field_simp
    ring
  have Eα := abs_le_exp_add_exp_neg α
  have Eβ := abs_le_exp_add_exp_neg β
  have Eγ := abs_le_exp_add_exp_neg γ
  have Cα := abs_cube_le_exp_add_exp_neg α
  have Cβ := abs_cube_le_exp_add_exp_neg β
  have Cγ := abs_cube_le_exp_add_exp_neg γ
  have hprod := three_mul_abs_le γ α β
  have hvu := h1 v u hv hu
  have hwu := h1 w u hw hu
  have hvw := h1 v w hv hw
  have hbr : |⟪v, u⟫ * β + α * ⟪w, u⟫ - γ * α * β / 2 + γ * ⟪v, w⟫| ≤
      2 * ((Real.exp α + Real.exp (-α)) + (Real.exp β + Real.exp (-β)) +
        (Real.exp γ + Real.exp (-γ))) := by
    have t1 : |⟪v, u⟫ * β| ≤ |β| := by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hvu
    have t2 : |α * ⟪w, u⟫| ≤ |α| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hwu
    have t4 : |γ * ⟪v, w⟫| ≤ |γ| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hvw
    have t3 : |γ * α * β / 2| = |γ * α * β| / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have tri : |⟪v, u⟫ * β + α * ⟪w, u⟫ - γ * α * β / 2 + γ * ⟪v, w⟫| ≤
        |⟪v, u⟫ * β| + |α * ⟪w, u⟫| + |γ * α * β / 2| + |γ * ⟪v, w⟫| := by
      calc _ ≤ |⟪v, u⟫ * β + α * ⟪w, u⟫ - γ * α * β / 2| + |γ * ⟪v, w⟫| := abs_add_le _ _
        _ ≤ (|⟪v, u⟫ * β + α * ⟪w, u⟫| + |γ * α * β / 2|) + |γ * ⟪v, w⟫| := by
            gcongr; exact abs_sub _ _
        _ ≤ _ := by gcongr; exact abs_add_le _ _
    rw [t3] at tri
    have hep1 := Real.exp_pos α
    have hep2 := Real.exp_pos (-α)
    linarith
  have hc : 0 < (4 * t * s)⁻¹ := by positivity
  rw [hform, norm_mul, norm_mul, Real.norm_of_nonneg hK, Real.norm_of_nonneg hc.le,
    Real.norm_eq_abs]
  have e1 : -s⁻¹ * ⟪v, x⟫ = -α := by rw [hα]; ring
  have e2 : -s⁻¹ * ⟪w, x⟫ = -β := by rw [hβ]; ring
  have e3 : -s⁻¹ * ⟪u, x⟫ = -γ := by rw [hγ]; ring
  rw [e1, e2, e3]
  calc (4 * t * s)⁻¹ * |⟪v, u⟫ * β + α * ⟪w, u⟫ - γ * α * β / 2 + γ * ⟪v, w⟫| *
        heatKernel d t x ≤
      (4 * t * s)⁻¹ * (2 * ((Real.exp α + Real.exp (-α)) + (Real.exp β + Real.exp (-β)) +
        (Real.exp γ + Real.exp (-γ)))) * heatKernel d t x := by gcongr
    _ = _ := by field_simp; ring

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integrable_heatThirdDirectional {t : ℝ} (ht : 0 < t)
    {v w u : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) :
    Integrable (heatThirdDirectional d t v w u) := by
  have i1 := integrable_heatTilt ht (Real.sqrt t)⁻¹ v
  have i2 := integrable_heatTilt ht (-(Real.sqrt t)⁻¹) v
  have i3 := integrable_heatTilt ht (Real.sqrt t)⁻¹ w
  have i4 := integrable_heatTilt ht (-(Real.sqrt t)⁻¹) w
  have i5 := integrable_heatTilt ht (Real.sqrt t)⁻¹ u
  have i6 := integrable_heatTilt ht (-(Real.sqrt t)⁻¹) u
  have hI : Integrable (fun x => (2 * t * Real.sqrt t)⁻¹ *
      (heatTilt d t (Real.sqrt t)⁻¹ v x + heatTilt d t (-(Real.sqrt t)⁻¹) v x +
       heatTilt d t (Real.sqrt t)⁻¹ w x + heatTilt d t (-(Real.sqrt t)⁻¹) w x +
       heatTilt d t (Real.sqrt t)⁻¹ u x + heatTilt d t (-(Real.sqrt t)⁻¹) u x)) :=
    (((((i1.add i2).add i3).add i4).add i5).add i6).const_mul _
  exact hI.mono' (continuous_heatThirdDirectional ht v w u).aestronglyMeasurable
    (ae_of_all _ (norm_heatThirdDirectional_le ht hv hw hu))

/--
For t > 0 and unit directions, the third derivative has L¹ norm at most 3e/(t√t). Source: DPR
context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem integral_norm_heatThirdDirectional_le {t : ℝ} (ht : 0 < t)
    {v w u : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) :
    (∫ x, ‖heatThirdDirectional d t v w u x‖) ≤ 3 * Real.exp 1 / (t * Real.sqrt t) := by
  have hs2 : t * ((Real.sqrt t)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt ht.le, mul_inv_cancel₀ ht.ne']
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have i1 := integrable_heatTilt ht (Real.sqrt t)⁻¹ v
  have i2 := integrable_heatTilt ht (-(Real.sqrt t)⁻¹) v
  have i3 := integrable_heatTilt ht (Real.sqrt t)⁻¹ w
  have i4 := integrable_heatTilt ht (-(Real.sqrt t)⁻¹) w
  have i5 := integrable_heatTilt ht (Real.sqrt t)⁻¹ u
  have i6 := integrable_heatTilt ht (-(Real.sqrt t)⁻¹) u
  have j2 : Integrable (fun x => heatTilt d t (Real.sqrt t)⁻¹ v x +
      heatTilt d t (-(Real.sqrt t)⁻¹) v x) := i1.add i2
  have j3 : Integrable (fun x => heatTilt d t (Real.sqrt t)⁻¹ v x +
      heatTilt d t (-(Real.sqrt t)⁻¹) v x + heatTilt d t (Real.sqrt t)⁻¹ w x) := j2.add i3
  have j4 : Integrable (fun x => heatTilt d t (Real.sqrt t)⁻¹ v x +
      heatTilt d t (-(Real.sqrt t)⁻¹) v x + heatTilt d t (Real.sqrt t)⁻¹ w x +
      heatTilt d t (-(Real.sqrt t)⁻¹) w x) := j3.add i4
  have j5 : Integrable (fun x => heatTilt d t (Real.sqrt t)⁻¹ v x +
      heatTilt d t (-(Real.sqrt t)⁻¹) v x + heatTilt d t (Real.sqrt t)⁻¹ w x +
      heatTilt d t (-(Real.sqrt t)⁻¹) w x + heatTilt d t (Real.sqrt t)⁻¹ u x) := j4.add i5
  have j6 : Integrable (fun x => heatTilt d t (Real.sqrt t)⁻¹ v x +
      heatTilt d t (-(Real.sqrt t)⁻¹) v x + heatTilt d t (Real.sqrt t)⁻¹ w x +
      heatTilt d t (-(Real.sqrt t)⁻¹) w x + heatTilt d t (Real.sqrt t)⁻¹ u x +
      heatTilt d t (-(Real.sqrt t)⁻¹) u x) := j5.add i6
  have hS : (∫ x, (heatTilt d t (Real.sqrt t)⁻¹ v x +
      heatTilt d t (-(Real.sqrt t)⁻¹) v x + heatTilt d t (Real.sqrt t)⁻¹ w x +
      heatTilt d t (-(Real.sqrt t)⁻¹) w x + heatTilt d t (Real.sqrt t)⁻¹ u x +
      heatTilt d t (-(Real.sqrt t)⁻¹) u x)) = 6 * Real.exp 1 := by
    rw [integral_add j5 i6, integral_add j4 i5, integral_add j3 i4, integral_add j2 i3,
      integral_add i1 i2]
    simp only [integral_heatTilt ht, neg_sq, hv, hw, hu, one_pow, mul_one, hs2]
    ring
  calc (∫ x, ‖heatThirdDirectional d t v w u x‖) ≤
      ∫ x, (2 * t * Real.sqrt t)⁻¹ *
        (heatTilt d t (Real.sqrt t)⁻¹ v x + heatTilt d t (-(Real.sqrt t)⁻¹) v x +
         heatTilt d t (Real.sqrt t)⁻¹ w x + heatTilt d t (-(Real.sqrt t)⁻¹) w x +
         heatTilt d t (Real.sqrt t)⁻¹ u x + heatTilt d t (-(Real.sqrt t)⁻¹) u x) :=
        integral_mono (integrable_heatThirdDirectional ht hv hw hu).norm (j6.const_mul _)
          (norm_heatThirdDirectional_le ht hv hw hu)
    _ = (2 * t * Real.sqrt t)⁻¹ * (6 * Real.exp 1) := by rw [integral_const_mul, hS]
    _ = 3 * Real.exp 1 / (t * Real.sqrt t) := by field_simp; ring


/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem heatSecond_sub_eq_integral {t : ℝ} (ht : 0 < t)
    (v w x h : EuclideanSpace ℝ (Fin d)) :
    heatSecondDirectional d t v w (x - h) - heatSecondDirectional d t v w x =
      ∫ σ in (0 : ℝ)..1, -heatThirdDirectional d t v w h (x - σ • h) := by
  have hderiv : ∀ σ ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun σ : ℝ => heatSecondDirectional d t v w (x - σ • h))
      (-heatThirdDirectional d t v w h (x - σ • h)) σ := by
    intro σ _
    have hγ : HasDerivAt (fun σ : ℝ => x - σ • h) (-((1 : ℝ) • h)) σ :=
      ((hasDerivAt_id σ).smul_const h).const_sub x
    have hc := (hasFDerivAt_heatSecondDirectional ht v w (x - σ • h)).comp_hasDerivAt σ hγ
    exact hc.congr_deriv (by rw [one_smul, map_neg, ← heatThirdDirectional_eq_fderiv ht])
  have hcont : Continuous (fun σ : ℝ => -heatThirdDirectional d t v w h (x - σ • h)) :=
    ((continuous_heatThirdDirectional ht v w h).comp
      (continuous_const.sub (continuous_id.smul continuous_const))).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
  simp only [one_smul, zero_smul, sub_zero]

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem norm_heatSecond_sub_le {t : ℝ} (ht : 0 < t)
    (v w x h : EuclideanSpace ℝ (Fin d)) :
    ‖heatSecondDirectional d t v w (x - h) - heatSecondDirectional d t v w x‖ ≤
      ∫ σ in Ioc (0 : ℝ) 1, ‖heatThirdDirectional d t v w h (x - σ • h)‖ := by
  rw [heatSecond_sub_eq_integral ht, ← intervalIntegral.integral_of_le zero_le_one]
  calc _ ≤ ∫ σ in (0 : ℝ)..1, ‖-heatThirdDirectional d t v w h (x - σ • h)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ = _ := by simp only [norm_neg]

/--
L¹ translation estimate for the Gaussian Hessian at t > 0, for unit directions: ‖h‖·3e/(t√t).
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integral_norm_heatSecond_translate_le {t : ℝ} (ht : 0 < t)
    {v w : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h : EuclideanSpace ℝ (Fin d)) :
    (∫ x, ‖heatSecondDirectional d t v w (x - h) - heatSecondDirectional d t v w x‖) ≤
      ‖h‖ * (3 * Real.exp 1 / (t * Real.sqrt t)) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have hn : 0 < ‖h‖ := norm_pos_iff.2 hh
  set e := ‖h‖⁻¹ • h with he
  have hen : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hhe : h = ‖h‖ • e := by
    rw [he, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hTe := integrable_heatThirdDirectional ht hv hw hen
  have hTh : Integrable (heatThirdDirectional d t v w h) := by
    have : heatThirdDirectional d t v w h = fun x => ‖h‖ * heatThirdDirectional d t v w e x := by
      funext x; rw [hhe, heatThirdDirectional_smul, ← hhe]
    rw [this]; exact hTe.const_mul _
  have hTh1 : (∫ x, ‖heatThirdDirectional d t v w h x‖) =
      ‖h‖ * ∫ x, ‖heatThirdDirectional d t v w e x‖ := by
    rw [← integral_const_mul]
    congr 1; funext x
    rw [hhe, heatThirdDirectional_smul, ← hhe, norm_mul, Real.norm_of_nonneg hn.le]
  set G : ℝ × EuclideanSpace ℝ (Fin d) → ℝ :=
    fun p => ‖heatThirdDirectional d t v w h (p.2 - p.1 • h)‖ with hG
  have hGc : Continuous G :=
    ((continuous_heatThirdDirectional ht v w h).comp
      (continuous_snd.sub (continuous_fst.smul continuous_const))).norm
  have hGi : Integrable G ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
    apply (integrable_prod_iff hGc.aestronglyMeasurable).2
    constructor
    · exact ae_of_all _ (fun σ => (hTh.comp_sub_right (σ • h)).norm)
    · have hc : (fun σ : ℝ => ∫ x, ‖G (σ, x)‖) =
          fun _ => ∫ x, ‖heatThirdDirectional d t v w h x‖ := by
        funext σ
        simp only [hG, norm_norm]
        exact integral_sub_right_eq_self (fun x => ‖heatThirdDirectional d t v w h x‖) (σ • h)
      rw [hc]
      exact integrable_const _
  have hpt : ∀ x, ‖heatSecondDirectional d t v w (x - h) - heatSecondDirectional d t v w x‖ ≤
      ∫ σ in Ioc (0 : ℝ) 1, G (σ, x) := fun x => norm_heatSecond_sub_le ht v w x h
  calc (∫ x, ‖heatSecondDirectional d t v w (x - h) - heatSecondDirectional d t v w x‖) ≤
      ∫ x, ∫ σ in Ioc (0 : ℝ) 1, G (σ, x) :=
        integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
          hGi.integral_prod_right (ae_of_all _ hpt)
    _ = ∫ σ in Ioc (0 : ℝ) 1, ∫ x, G (σ, x) :=
        (integral_integral_swap (f := fun σ x => G (σ, x)) hGi).symm
    _ = ∫ σ in Ioc (0 : ℝ) 1, ∫ x, ‖heatThirdDirectional d t v w h x‖ := by
        congr 1; funext σ
        exact integral_sub_right_eq_self (fun x => ‖heatThirdDirectional d t v w h x‖) (σ • h)
    _ = ∫ x, ‖heatThirdDirectional d t v w h x‖ := by simp
    _ ≤ ‖h‖ * (3 * Real.exp 1 / (t * Real.sqrt t)) := by
        rw [hTh1]
        exact mul_le_mul_of_nonneg_left
          (integral_norm_heatThirdDirectional_le ht hv hw hen) hn.le


/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem norm_heatSecondDirectional_le_radial {t : ℝ} (ht : 0 < t)
    {v w : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖heatSecondDirectional d t v w x‖ ≤
      (‖x‖ ^ 2 / (4 * t ^ 2) + (2 * t)⁻¹) * heatKernel d t x := by
  have hK := heatKernel_nonneg d t x
  have hvw : |⟪v, w⟫| ≤ 1 := by
    have h := abs_real_inner_le_norm v w
    rw [hv, hw, one_mul] at h
    exact h
  have hpq : |⟪v, x⟫ * ⟪w, x⟫| ≤ ‖x‖ ^ 2 := by
    rw [abs_mul]
    have h1 := abs_real_inner_le_norm v x
    have h2 := abs_real_inner_le_norm w x
    rw [hv, one_mul] at h1
    rw [hw, one_mul] at h2
    nlinarith [abs_nonneg ⟪v, x⟫, abs_nonneg ⟪w, x⟫]
  unfold heatSecondDirectional
  rw [norm_mul, Real.norm_of_nonneg hK, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ hK
  calc _ ≤ |⟪v, x⟫ * ⟪w, x⟫ / (4 * t ^ 2)| + |⟪v, w⟫ / (2 * t)| := abs_sub _ _
    _ ≤ _ := by
      apply add_le_add
      · rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * t ^ 2)]
        exact div_le_div_of_nonneg_right hpq (by positivity)
      · rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * t), div_eq_mul_inv]
        exact mul_le_of_le_one_left (by positivity) hvw

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem heatKernel_four_mul {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)) :
    ((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹ * Real.exp (-(16 * t)⁻¹ * ‖x‖ ^ 2) =
      (4 : ℝ) ^ ((d : ℝ) / 2) * heatKernel d (4 * t) x := by
  simp only [heatKernel, if_pos (by positivity : (0:ℝ) < 4 * t)]
  have h1 : (4 * Real.pi * (4 * t)) ^ ((d : ℝ) / 2) =
      (4 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * t) ^ ((d : ℝ) / 2) := by
    rw [show 4 * Real.pi * (4 * t) = 4 * (4 * Real.pi * t) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  have h2 : (4 * (4 * t))⁻¹ = (16 * t)⁻¹ := by ring
  rw [h1, h2, mul_inv]
  have hp : (0:ℝ) < (4:ℝ) ^ ((d : ℝ) / 2) := by positivity
  field_simp

/--
For t > 0, unit directions and 0 ≤ r ≤ ‖x‖, the Hessian norm is at most (9/2)·4^{d/2}·e^{-r²/(8t)}/t
times the heat kernel at time 4t. Source: DPR context, transcription pp. 9–10. Exact scope:
parameters, assumptions and conclusion below.
-/
theorem norm_heatSecondDirectional_le_tail {t : ℝ} (ht : 0 < t)
    {v w : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) {x : EuclideanSpace ℝ (Fin d)} (hx : r ≤ ‖x‖) :
    ‖heatSecondDirectional d t v w x‖ ≤
      9 / 2 * (4 : ℝ) ^ ((d : ℝ) / 2) * (t⁻¹ * Real.exp (-(r ^ 2 / (8 * t)))) *
        heatKernel d (4 * t) x := by
  set σ := ‖x‖ ^ 2 / (16 * t) with hσ
  have hσ0 : 0 ≤ σ := by positivity
  set c := ((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hE : Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2) =
      Real.exp (-σ) * Real.exp (-σ) * Real.exp (-(2 * σ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hσ]
    field_simp
    ring
  have k1 : σ * Real.exp (-σ) ≤ 1 := by
    have h1 := Real.add_one_le_exp σ
    have h2 := Real.exp_pos (-σ)
    have h3 : Real.exp σ * Real.exp (-σ) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have k2 : Real.exp (-σ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have k3 : Real.exp (-(2 * σ)) ≤ Real.exp (-(r ^ 2 / (8 * t))) := by
    apply Real.exp_le_exp.mpr
    have hr2 : r ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hr hx 2
    have : r ^ 2 / (8 * t) ≤ 2 * σ := by
      rw [hσ, div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
    linarith
  have hA : 4 * (σ * Real.exp (-σ)) + 1 / 2 * Real.exp (-σ) ≤ 9 / 2 := by linarith
  have hti : 0 ≤ t⁻¹ := by positivity
  have he1 := Real.exp_pos (-σ)
  have he2 := Real.exp_pos (-(2 * σ))
  have hEσ : Real.exp (-σ) = Real.exp (-(16 * t)⁻¹ * ‖x‖ ^ 2) := by
    congr 1; rw [hσ]; ring
  calc ‖heatSecondDirectional d t v w x‖ ≤
      (‖x‖ ^ 2 / (4 * t ^ 2) + (2 * t)⁻¹) * heatKernel d t x :=
        norm_heatSecondDirectional_le_radial ht hv hw x
    _ = (t⁻¹ * c) * (4 * (σ * Real.exp (-σ)) + 1 / 2 * Real.exp (-σ)) *
          Real.exp (-(2 * σ)) * Real.exp (-σ) := by
        simp only [heatKernel, if_pos ht]
        rw [hE, hσ, hc]
        field_simp
        ring
    _ ≤ (t⁻¹ * c) * (9 / 2) * Real.exp (-(r ^ 2 / (8 * t))) * Real.exp (-σ) := by
        gcongr
    _ = 9 / 2 * (4 : ℝ) ^ ((d : ℝ) / 2) * (t⁻¹ * Real.exp (-(r ^ 2 / (8 * t)))) *
          heatKernel d (4 * t) x := by
        have h4 := heatKernel_four_mul ht x
        rw [hEσ, hc]
        linear_combination (9 / 2 * (t⁻¹ * Real.exp (-(r ^ 2 / (8 * t))))) * h4

/--
For t > 0 and unit directions, the integral of the Hessian translation difference outside the ball
of radius 2‖h‖ is at most 9·4^{d/2}·e^{-‖h‖²/(8t)}/t. Source: DPR context, transcription pp. 9–10.
Exact scope: parameters, assumptions and conclusion below.
-/
theorem integral_norm_heatSecond_outer_le {t : ℝ} (ht : 0 < t)
    {v w : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h : EuclideanSpace ℝ (Fin d)) :
    (∫ x in {x : EuclideanSpace ℝ (Fin d) | 2 * ‖h‖ < ‖x‖},
      ‖heatSecondDirectional d t v w (x - h) - heatSecondDirectional d t v w x‖) ≤
      9 * (4 : ℝ) ^ ((d : ℝ) / 2) * (t⁻¹ * Real.exp (-(‖h‖ ^ 2 / (8 * t)))) := by
  set C := 9 / 2 * (4 : ℝ) ^ ((d : ℝ) / 2) * (t⁻¹ * Real.exp (-(‖h‖ ^ 2 / (8 * t)))) with hC
  have hC0 : 0 ≤ C := by positivity
  have hS := integrable_heatSecondDirectional ht hv hw
  have hD : Integrable (fun x =>
      ‖heatSecondDirectional d t v w (x - h) - heatSecondDirectional d t v w x‖) :=
    ((hS.comp_sub_right h).sub hS).norm
  have hH4 := integrable_heatKernel d (4 * t)
  have hB : Integrable (fun x => C * (heatKernel d (4 * t) (x - h) + heatKernel d (4 * t) x)) :=
    ((hH4.comp_sub_right h).add hH4).const_mul C
  have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin d) | 2 * ‖h‖ < ‖x‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hpt : ∀ x ∈ {x : EuclideanSpace ℝ (Fin d) | 2 * ‖h‖ < ‖x‖},
      ‖heatSecondDirectional d t v w (x - h) - heatSecondDirectional d t v w x‖ ≤
        C * (heatKernel d (4 * t) (x - h) + heatKernel d (4 * t) x) := by
    intro x hx
    simp only [mem_setOf_eq] at hx
    have hn := norm_nonneg h
    have h1 : ‖h‖ ≤ ‖x - h‖ := by
      have := norm_sub_norm_le x h
      linarith
    have h2 : ‖h‖ ≤ ‖x‖ := by linarith
    calc _ ≤ ‖heatSecondDirectional d t v w (x - h)‖ + ‖heatSecondDirectional d t v w x‖ :=
          norm_sub_le _ _
      _ ≤ C * heatKernel d (4 * t) (x - h) + C * heatKernel d (4 * t) x :=
          add_le_add (norm_heatSecondDirectional_le_tail ht hv hw hn h1)
            (norm_heatSecondDirectional_le_tail ht hv hw hn h2)
      _ = _ := by ring
  calc _ ≤ ∫ x in {x : EuclideanSpace ℝ (Fin d) | 2 * ‖h‖ < ‖x‖},
        C * (heatKernel d (4 * t) (x - h) + heatKernel d (4 * t) x) :=
        setIntegral_mono_on hD.integrableOn hB.integrableOn hmeas hpt
    _ ≤ ∫ x, C * (heatKernel d (4 * t) (x - h) + heatKernel d (4 * t) x) :=
        setIntegral_le_integral hB (ae_of_all _ (fun x => mul_nonneg hC0
          (add_nonneg (heatKernel_nonneg _ _ _) (heatKernel_nonneg _ _ _))))
    _ = C * 2 := by
        rw [integral_const_mul, integral_add (hH4.comp_sub_right h) hH4,
          integral_sub_right_eq_self (fun x => heatKernel d (4 * t) x) h,
          integral_heatKernel d (by positivity)]
        ring
    _ = _ := by rw [hC]; ring


end GeometricMeasure
