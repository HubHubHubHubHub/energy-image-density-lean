import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convolution

/-!
# Heat Kernel

## Main results
Normalized heat kernel, spatial derivative, dilation and Young L¹. The bound for a unit direction at
t > 0 is e/√t; no semigroup property is asserted.

Bibliographic context: De Philippis–Rindler, p. 9, (2.9)–(2.10). The heat-kernel argument is a
specialization. The Annals page reference, pp. 1027–1028, is unverified against that edition.
-/


noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped Topology RealInnerProductSpace Convolution
namespace GeometricMeasure
variable {d : ℕ}

/--
Gaussian kernel, extended by zero to nonpositive times. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def heatKernel (d : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if 0 < t then ((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹ *
    Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2) else 0

/--
nonnegativity also holds on the chosen extension. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem heatKernel_nonneg (d : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ heatKernel d t x := by
  unfold heatKernel
  split_ifs with ht
  · positivity
  · exact le_rfl

/--
positive value at strictly positive time. Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem heatKernel_pos (d : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin d)) : 0 < heatKernel d t x := by
  simp only [heatKernel, if_pos ht]
  positivity

/--
joint measurability, including at t = 0. Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem measurable_heatKernel (d : ℕ) :
    Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => heatKernel d p.1 p.2) := by
  unfold heatKernel
  apply Measurable.ite (measurableSet_lt measurable_const measurable_fst)
  · fun_prop
  · fun_prop

/--
integrability of the real Gaussian factor. Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem integrable_gaussian_norm (d : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin d)) (b := (b : ℂ)) (by simpa using hb) 0 0).re
  convert h using 1
  ext x
  simp only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, RCLike.re_to_complex, Complex.exp_ofReal_re]

/-- Every time slice is integrable. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem integrable_heatKernel (d : ℕ) (t : ℝ) : Integrable (heatKernel d t) := by
  change Integrable (fun x => heatKernel d t x)
  by_cases ht : 0 < t
  · simpa only [heatKernel, if_pos ht] using
      (integrable_gaussian_norm d (by positivity : 0 < (4 * t)⁻¹)).const_mul
        (((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹)
  · simp [heatKernel, ht]

/--
mass one of the heat kernel at strictly positive time. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integral_heatKernel (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ x, heatKernel d t x) = 1 := by
  simp only [heatKernel, if_pos ht, integral_const_mul]
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
  have he : Real.pi / (4 * t)⁻¹ = 4 * Real.pi * t := by simp only [div_inv_eq_mul]; ring
  rw [he]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _))

/--
The L¹ norm of H_t is one at strictly positive time. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integral_norm_heatKernel (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ x, ‖heatKernel d t x‖) = 1 := by
  simpa only [Real.norm_of_nonneg (heatKernel_nonneg d t _)] using integral_heatKernel d ht

/--
integrability of a Gaussian with a linear term. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integrable_gaussian_tilt {b : ℝ} (hb : 0 < b) (c : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x => Real.exp (-b * ‖x‖ ^ 2 + c * ⟪v, x⟫)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := (b : ℂ)) (by simpa using hb) (c : ℂ) v).re
  convert h using 1
  ext x
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
    ← Complex.ofReal_add, RCLike.re_to_complex, Complex.exp_ofReal_re]

/--
integral of the tilted Gaussian (completion of the square). Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integral_gaussian_tilt {b : ℝ} (hb : 0 < b) (c : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) :
    (∫ x, Real.exp (-b * ‖x‖ ^ 2 + c * ⟪v, x⟫)) =
      (Real.pi / b) ^ ((d : ℝ) / 2) * Real.exp (c ^ 2 * ‖v‖ ^ 2 / (4 * b)) := by
  rw [← Complex.ofReal_inj]
  convert GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (b := (b : ℂ)) (by simpa using hb) (c : ℂ) v using 1
  · change Complex.ofRealLI (∫ x, Real.exp (-b * ‖x‖ ^ 2 + c * ⟪v, x⟫)) = _
    rw [← Complex.ofRealLI.integral_comp_comm]
    congr 1
    ext x
    simp [Complex.ofRealLI, Complex.ofReal_exp]
  · rw [Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_cpow (by positivity)]
    simp

/--
heat kernel with a linear exponential factor. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def heatTilt (d : ℕ) (t c : ℝ) (v x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹ *
    Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2 + c * ⟪v, x⟫)

/--
spatial integrability of the tilted majorant at positive time. Source: DPR p. 9 (context),
heat-kernel representation.
-/
theorem integrable_heatTilt {t : ℝ} (ht : 0 < t) (c : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : Integrable (heatTilt d t c v) :=
  (integrable_gaussian_tilt (by positivity : 0 < (4*t)⁻¹) c v).const_mul _

/--
mass of the tilted majorant at positive time. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integral_heatTilt {t : ℝ} (ht : 0 < t) (c : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) :
    (∫ x, heatTilt d t c v x) = Real.exp (t * c ^ 2 * ‖v‖ ^ 2) := by
  unfold heatTilt
  rw [integral_const_mul, integral_gaussian_tilt (by positivity)]
  have he : Real.pi / (4 * t)⁻¹ = 4 * Real.pi * t := by
    simp only [div_inv_eq_mul]; ring
  rw [he, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)), one_mul]
  congr 1
  field_simp

/--
explicit directional derivative of the heat kernel. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def heatDirectional (d : ℕ) (t : ℝ) (v x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -(⟪v, x⟫ / (2 * t)) * heatKernel d t x

/--
At positive time, the explicit derivative equals the Fréchet derivative evaluated at v. Source: DPR
p. 9 (context), heat-kernel representation.
-/
theorem heatDirectional_eq_fderiv {t : ℝ} (ht : 0 < t)
    (v x : EuclideanSpace ℝ (Fin d)) :
    heatDirectional d t v x = fderiv ℝ (heatKernel d t) x v := by
  have h := (((hasFDerivAt_id x).norm_sq.const_mul (-(4*t)⁻¹)).exp).const_mul
    (((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹)
  have hh : (fun y : EuclideanSpace ℝ (Fin d) =>
      ((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹ * Real.exp (-(4*t)⁻¹ * ‖y‖^2)) =
      heatKernel d t := by ext y; simp [heatKernel, ht]
  simp only [id_eq] at h
  rw [hh] at h
  rw [h.fderiv]
  simp [heatDirectional, heatKernel, ht, real_inner_comm, div_eq_mul_inv]
  ring

/--
elementary bound on the linear factor. Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem abs_le_exp_add_exp_neg (r : ℝ) : |r| ≤ Real.exp r + Real.exp (-r) := by
  have h := Real.add_one_le_exp r
  have hn := Real.add_one_le_exp (-r)
  have hp := Real.exp_pos r
  have hm := Real.exp_pos (-r)
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr]; linarith
  · rw [abs_of_nonpos hr]; linarith

/--
At positive time, an integrable majorant of the derivative, uniform after rescaling. Source: DPR p.
9 (context), heat-kernel representation.
-/
theorem norm_heatDirectional_le {t : ℝ} (ht : 0 < t)
    (v x : EuclideanSpace ℝ (Fin d)) :
    ‖heatDirectional d t v x‖ ≤ (2 * Real.sqrt t)⁻¹ *
      (heatTilt d t (Real.sqrt t)⁻¹ v x + heatTilt d t (-(Real.sqrt t)⁻¹) v x) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs2 := Real.sq_sqrt ht.le
  have hab := abs_le_exp_add_exp_neg ((Real.sqrt t)⁻¹ * ⟪v, x⟫)
  have hK := heatKernel_nonneg d t x
  have hfactor : ‖heatDirectional d t v x‖ =
      ((2 * Real.sqrt t)⁻¹ * heatKernel d t x) *
        |(Real.sqrt t)⁻¹ * ⟪v, x⟫| := by
    simp only [heatDirectional, norm_mul, norm_neg, Real.norm_eq_abs, abs_div,
      abs_of_nonneg hK, abs_mul, abs_of_pos ht, abs_of_pos (inv_pos.2 hs)]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    field_simp
    rw [hs2]
    ring
  rw [hfactor]
  calc
    _ ≤ ((2 * Real.sqrt t)⁻¹ * heatKernel d t x) *
        (Real.exp ((Real.sqrt t)⁻¹ * ⟪v, x⟫) +
          Real.exp (-((Real.sqrt t)⁻¹ * ⟪v, x⟫))) :=
      mul_le_mul_of_nonneg_left hab (by positivity)
    _ = _ := by
      simp only [heatTilt, heatKernel, if_pos ht, Real.exp_add, neg_mul]
      ring

/--
integrability of the heat derivative at positive time. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integrable_heatDirectional {t : ℝ} (ht : 0 < t)
    (v : EuclideanSpace ℝ (Fin d)) : Integrable (heatDirectional d t v) := by
  apply (((integrable_heatTilt ht (Real.sqrt t)⁻¹ v).add
    (integrable_heatTilt ht (-(Real.sqrt t)⁻¹) v)).const_mul (2 * Real.sqrt t)⁻¹).mono'
  · unfold heatDirectional
    exact ((by fun_prop : Continuous (fun x => -(⟪v, x⟫ / (2*t)))).aestronglyMeasurable.mul
      (integrable_heatKernel d t).aestronglyMeasurable)
  · exact ae_of_all _ (norm_heatDirectional_le ht v)

/--
L¹ bound e/√t for a unit direction and t > 0; the nonoptimal constant e is dimension-independent.
Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem integral_norm_heatDirectional_le {t : ℝ} (ht : 0 < t)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    (∫ x, ‖heatDirectional d t v x‖) ≤ Real.exp 1 / Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have he : t * ((Real.sqrt t)⁻¹)^2 = 1 := by
    rw [inv_pow, Real.sq_sqrt ht.le, mul_inv_cancel₀ ht.ne']
  calc
    _ ≤ ∫ x, (2 * Real.sqrt t)⁻¹ *
        (heatTilt d t (Real.sqrt t)⁻¹ v x + heatTilt d t (-(Real.sqrt t)⁻¹) v x) :=
      integral_mono (integrable_heatDirectional ht v).norm
        (((integrable_heatTilt ht _ v).add (integrable_heatTilt ht _ v)).const_mul _)
        (norm_heatDirectional_le ht v)
    _ = _ := by
      rw [integral_const_mul, integral_add (integrable_heatTilt ht _ v)
        (integrable_heatTilt ht _ v), integral_heatTilt ht, integral_heatTilt ht]
      simp only [neg_sq, hv, one_pow, mul_one, he]
      field_simp
      ring

/-- evenness of the heat kernel. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem heatKernel_neg (d : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    heatKernel d t (-x) = heatKernel d t x := by simp [heatKernel]

/-- oddness of the heat derivative. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem heatDirectional_neg (t : ℝ) (v x : EuclideanSpace ℝ (Fin d)) :
    heatDirectional d t v (-x) = - heatDirectional d t v x := by
  simp [heatDirectional, heatKernel_neg]
  ring

/-- Every heat derivative has zero mass. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem integral_heatDirectional (t : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    (∫ x, heatDirectional d t v x) = 0 := by
  have h := integral_neg_eq_self (heatDirectional d t v) volume
  simp only [heatDirectional_neg, integral_neg] at h
  linarith

/--
spatial differentiability of the kernel for t > 0. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem differentiable_heatKernel {t : ℝ} (ht : 0 < t) :
    Differentiable ℝ (heatKernel d t) := by
  change Differentiable ℝ (fun x : EuclideanSpace ℝ (Fin d) => heatKernel d t x)
  simp only [heatKernel, if_pos ht]
  intro x
  have h := (((hasFDerivAt_id x).norm_sq.const_mul (-(4*t)⁻¹)).exp).const_mul
    (((4 * Real.pi * t) ^ ((d : ℝ) / 2))⁻¹)
  simpa only [id_eq] using h.differentiableAt

/--
scalar convolution with the Mathlib convention. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def scalarConvolution (K u : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ := K ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u

/-- integral expression for convolution. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem scalarConvolution_apply (K u : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    scalarConvolution K u x = ∫ y, K y * u (x - y) := rfl

/--
integrability of the convolution of two L¹ functions. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integrable_scalarConvolution {K u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hK : Integrable K) (hu : Integrable u) : Integrable (scalarConvolution K u) :=
  hK.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hu

/--
Fubini computes the mass of the convolution. Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem integral_scalarConvolution {K u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hK : Integrable K) (hu : Integrable u) :
    (∫ x, scalarConvolution K u x) = (∫ x, K x) * ∫ x, u x :=
  integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hK hu

/--
nonnegativity of convolution for nonnegative factors. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem scalarConvolution_nonneg {K u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hK : ∀ x, 0 ≤ K x) (hu : ∀ x, 0 ≤ u x) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ scalarConvolution K u x :=
  integral_nonneg (fun y => mul_nonneg (hK y) (hu (x - y)))

/--
Young's L¹ norm bound, with constant one. Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem integral_norm_scalarConvolution_le {K u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hK : Integrable K) (hu : Integrable u) :
    (∫ x, ‖scalarConvolution K u x‖) ≤ (∫ x, ‖K x‖) * ∫ x, ‖u x‖ := by
  calc
    (∫ x, ‖scalarConvolution K u x‖) ≤
        ∫ x, scalarConvolution (fun y => ‖K y‖) (fun y => ‖u y‖) x := by
      apply integral_mono (integrable_scalarConvolution hK hu).norm
        (integrable_scalarConvolution hK.norm hu.norm)
      intro x
      simpa only [scalarConvolution_apply, norm_mul] using
        (norm_integral_le_integral_norm (fun y => K y * u (x - y)))
    _ = _ := integral_scalarConvolution hK.norm hu.norm

/--
pointwise rescaling of the heat kernel. Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem heatKernel_scale {t : ℝ} (ht : 0 < t) (z : EuclideanSpace ℝ (Fin d)) :
    Real.sqrt t ^ d * heatKernel d t (Real.sqrt t • z) = heatKernel d 1 z := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  simp only [heatKernel, if_pos ht, if_pos one_pos, norm_smul, Real.norm_of_nonneg hs.le,
    mul_pow, Real.sq_sqrt ht.le]
  have h1 : -(4 * t)⁻¹ * (t * ‖z‖ ^ 2) = -(4 * 1)⁻¹ * ‖z‖ ^ 2 := by
    field_simp
  have h2 : (4 * Real.pi * t) ^ ((d : ℝ) / 2) =
      (4 * Real.pi * 1) ^ ((d : ℝ) / 2) * Real.sqrt t ^ d := by
    rw [mul_one, Real.mul_rpow (by positivity) ht.le, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 2
    ring
  rw [h1, h2, mul_inv]
  have hp : Real.sqrt t ^ d ≠ 0 := pow_ne_zero _ hs.ne'
  field_simp

/--
convolution by H_t expressed using the dilated profile H_1. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem heatConvolution_eq_scaled {t : ℝ} (ht : 0 < t)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    scalarConvolution (heatKernel d t) u x =
      ∫ z, heatKernel d 1 z * u (x - Real.sqrt t • z) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure (EuclideanSpace ℝ (Fin d)))
    (fun y => heatKernel d t y * u (x - y)) (Real.sqrt t) (hR := hs.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at h
  rw [scalarConvolution_apply]
  have hp : Real.sqrt t ^ d ≠ 0 := pow_ne_zero _ hs.ne'
  calc
    (∫ y, heatKernel d t y * u (x - y)) =
        Real.sqrt t ^ d * ∫ z, heatKernel d t (Real.sqrt t • z) * u (x - Real.sqrt t • z) := by
      rw [h, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]
    _ = ∫ z, heatKernel d 1 z * u (x - Real.sqrt t • z) := by
      rw [← integral_const_mul]
      congr 1
      ext z
      rw [← heatKernel_scale ht z]
      ring

end GeometricMeasure
