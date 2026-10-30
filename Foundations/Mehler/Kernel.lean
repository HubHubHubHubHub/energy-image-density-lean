import Foundations.Mehler.Gaussian
import Foundations.Sections.Corollaries

noncomputable section
open Filter Topology Set MeasureTheory ProbabilityTheory Polynomial
open scoped InnerProductSpace
namespace Foundations

def gaussianMean : Lp ℝ 2 standardGaussian →L[ℝ] ℝ := innerSL ℝ (hermiteLp 0)

theorem gaussianMean_apply (f : Lp ℝ 2 standardGaussian) :
    gaussianMean f = ∫ x, f x ∂standardGaussian := by
  change ⟪hermiteLp 0, f⟫_ℝ = _
  rw [real_inner_comm]
  simpa [hermiteLp] using inner_polynomialLp f (hermitePolynomial 0)

theorem norm_gaussianMean : ‖gaussianMean‖ = 1 := by
  rw [gaussianMean, innerSL_apply_norm]
  simpa [hermiteNormalized] using orthonormal_hermiteNormalized.norm_eq_one 0

theorem sq_integral_gaussian_le {f : ℝ → ℝ} (hf : MemLp f 2 standardGaussian) :
    (∫ x, f x ∂standardGaussian)^2 ≤ ∫ x, f x^2 ∂standardGaussian := by
  have h := gaussianMean.le_opNorm (hf.toLp f)
  rw [norm_gaussianMean, one_mul, gaussianMean_apply,
    integral_congr_ae hf.coeFn_toLp] at h
  rw [← norm_toLp_sq standardGaussian hf]
  simpa only [Real.norm_eq_abs, sq_abs] using
    (pow_le_pow_left₀ (norm_nonneg (∫ x, f x ∂standardGaussian)) h 2)


theorem sq_mehlerKernel_le (t x : ℝ) {f : ℝ → ℝ}
    (hf : MemLp (fun y => f (mehlerCoeffA t*x+mehlerCoeffB t*y)) 2 standardGaussian) :
    (mehlerKernel t f x)^2 ≤ mehlerKernel t (fun z => f z^2) x :=
  sq_integral_gaussian_le hf

def gaussianAverage : Lp ℝ 2 (standardGaussian.prod standardGaussian) →L[ℝ]
    Lp ℝ 2 standardGaussian :=
  (gaussianMean.compLpL 2 standardGaussian).comp
    (sectionLpₗᵢ standardGaussian standardGaussian).toContinuousLinearMap

theorem norm_gaussianAverage_apply_le (F : Lp ℝ 2 (standardGaussian.prod standardGaussian)) :
    ‖gaussianAverage F‖ ≤ ‖F‖ := by
  exact (gaussianMean.norm_compLp_le (sectionLpₗᵢ standardGaussian standardGaussian F)).trans_eq
    (by rw [norm_gaussianMean, one_mul, LinearIsometry.norm_map])

theorem coe_gaussianAverage (F : Lp ℝ 2 (standardGaussian.prod standardGaussian)) :
    gaussianAverage F =ᵐ[standardGaussian] fun x => ∫ y, F (y,x) ∂standardGaussian := by
  filter_upwards [gaussianMean.coeFn_compLpL (sectionLpₗᵢ standardGaussian standardGaussian F),
    coeFn_sectionLpₗᵢ standardGaussian standardGaussian F,
    coeFn_sectionLp standardGaussian (Lp.memLp F)] with x h1 h2 h3
  change (gaussianMean.compLpL 2 standardGaussian (sectionLpₗᵢ standardGaussian standardGaussian F)) x = _
  rw [h1, h2, gaussianMean_apply]
  exact integral_congr_ae h3

/-- Mehler's integral operator on equivalence classes. Only nonnegative times are used. -/
def mehler (t : ℝ) : Lp ℝ 2 standardGaussian →L[ℝ] Lp ℝ 2 standardGaussian :=
  if ht : 0 ≤ t then gaussianAverage.comp
    (Lp.compMeasurePreservingₗᵢ ℝ (mehlerMix t) (measurePreserving_mehlerMix ht)).toContinuousLinearMap
  else 0

theorem mehler_apply_of_nonneg {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 standardGaussian) :
    mehler t f = gaussianAverage (Lp.compMeasurePreserving (mehlerMix t)
      (measurePreserving_mehlerMix ht) f) := by
  rw [mehler, dif_pos ht]
  rfl

theorem norm_mehler_apply_le {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 standardGaussian) :
    ‖mehler t f‖ ≤ ‖f‖ := by
  rw [mehler_apply_of_nonneg ht]
  exact (norm_gaussianAverage_apply_le _).trans_eq (Lp.norm_compMeasurePreserving _ _)

theorem norm_mehler_le_one {t : ℝ} (ht : 0 ≤ t) : ‖mehler t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using norm_mehler_apply_le ht f

theorem coe_mehler {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 standardGaussian) :
    mehler t f =ᵐ[standardGaussian] mehlerKernel t f := by
  rw [mehler_apply_of_nonneg ht]
  have h := Lp.coeFn_compMeasurePreserving f (measurePreserving_mehlerMix ht)
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq h
  filter_upwards [coe_gaussianAverage (Lp.compMeasurePreserving (mehlerMix t)
    (measurePreserving_mehlerMix ht) f), Measure.ae_ae_of_ae_prod hs] with x hx hy
  exact hx.trans (integral_congr_ae hy)

theorem mehlerKernel_congr_ae {t : ℝ} (ht : 0 ≤ t) {f g : ℝ → ℝ}
    (h : f =ᵐ[standardGaussian] g) :
    mehlerKernel t f =ᵐ[standardGaussian] mehlerKernel t g := by
  have he := (measurePreserving_mehlerMix ht).quasiMeasurePreserving.ae_eq h
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with x hx
  exact integral_congr_ae hx

theorem coe_mehler_toLp {t : ℝ} (ht : 0 ≤ t) {f : ℝ → ℝ} (hf : MemLp f 2 standardGaussian) :
    mehler t (hf.toLp f) =ᵐ[standardGaussian] mehlerKernel t f :=
  (coe_mehler ht _).trans (mehlerKernel_congr_ae ht hf.coeFn_toLp)

@[simp] theorem mehler_zero : mehler 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [coe_mehler (le_refl 0) f] with x hx
  simpa using hx

end Foundations
