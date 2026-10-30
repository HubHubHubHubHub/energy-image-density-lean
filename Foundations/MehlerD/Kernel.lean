import Foundations.MehlerD.Gaussian
import Foundations.Sections.Corollaries

noncomputable section
open Filter Topology Set MeasureTheory ProbabilityTheory Polynomial
open scoped InnerProductSpace
namespace Foundations
variable {ι : Type*} [Fintype ι]

def gaussianMeanD : Lp ℝ 2 (gaussianProduct ι) →L[ℝ] ℝ := innerSL ℝ (hermiteLpD 0)

theorem gaussianMean_applyD (f : Lp ℝ 2 (gaussianProduct ι)) :
    gaussianMeanD f = ∫ x, f x ∂(gaussianProduct ι) := by
  change ⟪hermiteLpD 0, f⟫_ℝ = _
  rw [real_inner_comm, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_hermiteLpD (0 : ι → ℕ)] with x hx
  simp [hx, real_inner_comm]

theorem norm_gaussianMeanD : ‖gaussianMeanD (ι := ι)‖ = 1 := by
  rw [gaussianMeanD, innerSL_apply_norm]
  simpa using (orthonormal_hermiteNormalizedD (ι := ι)).norm_eq_one 0

theorem sq_integral_gaussian_leD {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (gaussianProduct ι)) :
    (∫ x, f x ∂(gaussianProduct ι))^2 ≤ ∫ x, f x^2 ∂(gaussianProduct ι) := by
  have h := gaussianMeanD.le_opNorm (hf.toLp f)
  rw [norm_gaussianMeanD, one_mul, gaussianMean_applyD,
    integral_congr_ae hf.coeFn_toLp] at h
  rw [← norm_toLp_sq (gaussianProduct ι) hf]
  simpa only [Real.norm_eq_abs, sq_abs] using
    (pow_le_pow_left₀ (norm_nonneg (∫ x, f x ∂(gaussianProduct ι))) h 2)


theorem sq_mehlerKernel_leD (t : ℝ) (x : ι → ℝ) {f : (ι → ℝ) → ℝ}
    (hf : MemLp (fun y => f (fun i => mehlerCoeffA t*x i+mehlerCoeffB t*y i)) 2 (gaussianProduct ι)) :
    (mehlerKernelD t f x)^2 ≤ mehlerKernelD t (fun z => f z^2) x :=
  sq_integral_gaussian_leD hf

def gaussianAverageD : Lp ℝ 2 ((gaussianProduct ι).prod (gaussianProduct ι)) →L[ℝ]
    Lp ℝ 2 (gaussianProduct ι) :=
  (gaussianMeanD.compLpL 2 (gaussianProduct ι)).comp
    (sectionLpₗᵢ (gaussianProduct ι) (gaussianProduct ι)).toContinuousLinearMap

theorem norm_gaussianAverage_apply_leD (F : Lp ℝ 2 ((gaussianProduct ι).prod (gaussianProduct ι))) :
    ‖gaussianAverageD F‖ ≤ ‖F‖ := by
  exact (gaussianMeanD.norm_compLp_le (sectionLpₗᵢ (gaussianProduct ι) (gaussianProduct ι) F)).trans_eq
    (by rw [norm_gaussianMeanD, one_mul, LinearIsometry.norm_map])

theorem coe_gaussianAverageD (F : Lp ℝ 2 ((gaussianProduct ι).prod (gaussianProduct ι))) :
    gaussianAverageD F =ᵐ[(gaussianProduct ι)] fun x => ∫ y, F (y,x) ∂(gaussianProduct ι) := by
  filter_upwards [gaussianMeanD.coeFn_compLpL (sectionLpₗᵢ (gaussianProduct ι) (gaussianProduct ι) F),
    coeFn_sectionLpₗᵢ (gaussianProduct ι) (gaussianProduct ι) F,
    coeFn_sectionLp (gaussianProduct ι) (Lp.memLp F)] with x h1 h2 h3
  change (gaussianMeanD.compLpL 2 (gaussianProduct ι) (sectionLpₗᵢ (gaussianProduct ι) (gaussianProduct ι) F)) x = _
  rw [h1, h2, gaussianMean_applyD]
  exact integral_congr_ae h3

/-- Mehler's integral operator on equivalence classes. Only nonnegative times are used. -/
def mehlerD (t : ℝ) : Lp ℝ 2 (gaussianProduct ι) →L[ℝ] Lp ℝ 2 (gaussianProduct ι) :=
  if ht : 0 ≤ t then gaussianAverageD.comp
    (Lp.compMeasurePreservingₗᵢ ℝ (mehlerMixD t) (measurePreserving_mehlerMixD ht)).toContinuousLinearMap
  else 0

theorem mehlerD_apply_of_nonneg {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (gaussianProduct ι)) :
    mehlerD t f = gaussianAverageD (Lp.compMeasurePreserving (mehlerMixD t)
      (measurePreserving_mehlerMixD ht) f) := by
  rw [mehlerD, dif_pos ht]
  rfl

theorem norm_mehlerD_apply_le {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (gaussianProduct ι)) :
    ‖mehlerD t f‖ ≤ ‖f‖ := by
  rw [mehlerD_apply_of_nonneg ht]
  exact (norm_gaussianAverage_apply_leD _).trans_eq (Lp.norm_compMeasurePreserving _ _)

theorem norm_mehlerD_le_one {t : ℝ} (ht : 0 ≤ t) : ‖mehlerD (ι := ι) t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using norm_mehlerD_apply_le ht f

theorem coe_mehlerD {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (gaussianProduct ι)) :
    mehlerD t f =ᵐ[(gaussianProduct ι)] mehlerKernelD t f := by
  rw [mehlerD_apply_of_nonneg ht]
  have h := Lp.coeFn_compMeasurePreserving f (measurePreserving_mehlerMixD ht)
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq h
  filter_upwards [coe_gaussianAverageD (Lp.compMeasurePreserving (mehlerMixD t)
    (measurePreserving_mehlerMixD ht) f), Measure.ae_ae_of_ae_prod hs] with x hx hy
  exact hx.trans (integral_congr_ae hy)

theorem mehlerKernelD_congr_ae {t : ℝ} (ht : 0 ≤ t) {f g : (ι → ℝ) → ℝ}
    (h : f =ᵐ[(gaussianProduct ι)] g) :
    mehlerKernelD t f =ᵐ[(gaussianProduct ι)] mehlerKernelD t g := by
  have he := (measurePreserving_mehlerMixD ht).quasiMeasurePreserving.ae_eq h
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with x hx
  exact integral_congr_ae hx

theorem coe_mehlerD_toLp {t : ℝ} (ht : 0 ≤ t) {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (gaussianProduct ι)) :
    mehlerD t (hf.toLp f) =ᵐ[(gaussianProduct ι)] mehlerKernelD t f :=
  (coe_mehlerD ht _).trans (mehlerKernelD_congr_ae ht hf.coeFn_toLp)

@[simp] theorem mehlerD_zero : mehlerD (ι := ι) 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [coe_mehlerD (le_refl 0) f] with x hx
  simpa using hx

end Foundations
