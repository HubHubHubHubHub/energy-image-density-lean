import GeometricMeasure.Analysis.TruncatedBessel
import GeometricMeasure.Current.BesselResolvent

/-!
# Truncated Bessel potentials

This file contains the definitions and results of the development of
`GeometricMeasure.Current.TruncatedBessel` that the main statements of the library (the head
theorems listed in the README of the repository) use, together with the basic API of their
definitions. `GeometricMeasure.Current.TruncatedBessel` imports it and continues the development.

## Main definitions

* `truncatedSecondTest`: Transferred operator on tests; its identification with K^η*u is separate.

## Main statements

* `truncatedBessel_resolves_test`: Truncated resolvent on tests, obtained from the heat evolution.
* `integrable_truncatedSecondKernel`: Kη ∈ L¹ for η > 0. Source: DPR context, transcription pp.
  9–10.
* `norm_truncatedSecondKernel_le`: Kη is bounded for η > 0, with an explicit majorant.
* `truncatedSecondKernel_convolution_test_eq`: For `0 < η`, the convolution of a test `u` with
  `truncatedSecondKernel η a b` is the function `truncatedSecondTest η a b u`.
* `truncatedSecondKernel_tendsto`: As `η → 0` from the right, `scalarConvolution
  (truncatedSecondKernel η a b) u x` tends to `besselSecond a b u x`, for every test `u` and point
  `x`.

## References

Bibliographic context: De Philippis–Rindler, pp. 9–10, (2.9)–(2.12). The heat-kernel and energy
estimates specialize the distributional framework.
-/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology RealInnerProductSpace Convolution ContDiff
namespace GeometricMeasure
variable {d : ℕ}

/--
Pointwise Fubini after convolution against a test. Source: DPR context, transcription pp. 9–10.
Exact scope: parameters, assumptions and conclusion below.
-/
theorem truncatedBessel_convolution_eq_heat_integral {η : ℝ} (hη : 0 ≤ η)
    (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    scalarConvolution (truncatedBessel d η) u x =
      ∫ t in Ioi η, Real.exp (-t) * scalarConvolution (heatKernel d t) u x := by
  have h := (integrable_prod_mul_scalarTest (integrable_weighted_heatKernel d)
    (translatedKernelTest u x)).mono_measure
      (Measure.prod_mono (Measure.restrict_mono (Ioi_subset_Ioi hη) le_rfl) le_rfl)
  change (∫ y, (∫ t in Ioi η, Real.exp (-t) * heatKernel d t y) * u (x-y)) = _
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (f := fun t y =>
    (Real.exp (-t) * heatKernel d t y) * u (x-y)) h]
  simp only [mul_assoc, integral_const_mul, scalarConvolution_apply]

/--
Linearity in the kernel, with integrability assumptions explicit. Source: DPR context, transcription
pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem scalarConvolution_sub_kernel_test {K L : EuclideanSpace ℝ (Fin d) → ℝ}
    (hK : Integrable K) (hL : Integrable L) (u : ScalarCurrentTest d) :
    scalarConvolution (K - L) u =
      fun x => scalarConvolution K u x - scalarConvolution L u x := by
  funext x
  simp only [scalarConvolution_apply, Pi.sub_apply, sub_mul]
  exact integral_sub (scalarConvolution_exists K hK u x) (scalarConvolution_exists L hL u x)

/--
Uniform pointwise bound; no ambiguous essential norm. Source: DPR context, transcription pp. 9–10.
Exact scope: parameters, assumptions and conclusion below.
-/
theorem norm_truncated_convolution_sub_le {η : ℝ} (hη : 0 ≤ η)
    (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    ‖scalarConvolution (truncatedBessel d η) u x -
      scalarConvolution (besselKernel d) u x‖ ≤
      (1 - Real.exp (-η)) *
        ‖(u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ := by
  have h := norm_scalarConvolution_test_le
    ((integrable_besselKernel d).sub (integrable_truncatedBessel d hη)) u x
  rw [scalarConvolution_sub_kernel_test (integrable_besselKernel d)
    (integrable_truncatedBessel d hη) u] at h
  simp only [Pi.sub_apply] at h
  rw [integral_norm_besselKernel_sub_truncated d hη] at h
  simpa only [norm_sub_rev] using h

/--
Transferred operator on tests; its identification with K^η*u is separate. Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
def truncatedSecondTest (η : ℝ) (a b : Fin d) (u : ScalarCurrentTest d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  scalarConvolution (truncatedBessel d η) (cutoffPartialTest (cutoffPartialTest u b) a)

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem truncatedSecondTest_zero_time (a b : Fin d) (u : ScalarCurrentTest d) :
    truncatedSecondTest 0 a b u = besselSecond a b u := rfl

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integrable_truncatedSecondTest {η : ℝ} (hη : 0 ≤ η)
    (a b : Fin d) (u : ScalarCurrentTest d) : Integrable (truncatedSecondTest η a b u) :=
  integrable_scalarConvolution (integrable_truncatedBessel d hη) (scalarTest_integrable _)

/--
The transferred pointwise supremum estimate. Source: DPR context, transcription pp. 9–10. Exact
scope: parameters, assumptions and conclusion below.
-/
theorem truncatedSecondTest_uniform_error {η : ℝ} (hη : 0 ≤ η)
    (a b : Fin d) (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    ‖truncatedSecondTest η a b u x - besselSecond a b u x‖ ≤
      (1 - Real.exp (-η)) *
      ‖(cutoffPartialTest (cutoffPartialTest u b) a :
        BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ :=
  norm_truncated_convolution_sub_le hη _ x

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem truncatedSecondTest_uniform_rate {η : ℝ} (hη : 0 ≤ η)
    (a b : Fin d) (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    ‖truncatedSecondTest η a b u x - besselSecond a b u x‖ ≤
      η * ‖(cutoffPartialTest (cutoffPartialTest u b) a :
        BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ :=
  (truncatedSecondTest_uniform_error hη a b u x).trans
    (mul_le_mul_of_nonneg_right one_sub_exp_neg_le (norm_nonneg _))

/--
Truncated resolvent on tests, obtained from the heat evolution. Source: DPR context, transcription
pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem truncatedBessel_resolves_test {η : ℝ} (hη : 0 < η)
    (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    scalarConvolution (truncatedBessel d η) (u - scalarTestLaplacian u : ScalarCurrentTest d) x =
      Real.exp (-η) * scalarConvolution (heatKernel d η) u x := by
  have hi := (integrable_heat_convolution (u - scalarTestLaplacian u : ScalarCurrentTest d) x).mono_set
    (Ioi_subset_Ioi hη.le)
  have he := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => heatTrajectory_hasDerivAt u x t (hη.trans_le ht)) hi.neg
    (heatTrajectory_tendsto_zero u x)
  rw [integral_neg, zero_sub, heatTrajectory, if_neg hη.ne'] at he
  rw [truncatedBessel_convolution_eq_heat_integral hη.le]
  linarith

/--
The bound is uniform in x; the pointwise limit requires no subsequence. Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem truncatedSecondTest_tendsto (a b : Fin d) (u : ScalarCurrentTest d)
    (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun η : ℝ => truncatedSecondTest η a b u x)
      (𝓝[Set.Ici 0] 0) (𝓝 (besselSecond a b u x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact truncatedSecondTest_uniform_rate hη a b u x
  · have hid : Tendsto (fun η : ℝ => η) (𝓝[Set.Ici 0] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h := hid.mul_const
      ‖(cutoffPartialTest (cutoffPartialTest u b) a :
        BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖
    simpa only [zero_mul] using h

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
private theorem norm_single_one (a : Fin d) : ‖EuclideanSpace.single a (1 : ℝ)‖ = 1 := by simp

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integrable_weighted_heatSecond_tail {η : ℝ} (hη : 0 < η) (a b : Fin d) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      Real.exp (-p.1) * heatSecondDirectional d p.1 (EuclideanSpace.single a 1)
        (EuclideanSpace.single b 1) p.2)
      ((volume.restrict (Ioi η)).prod volume) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      Real.exp (-p.1) * heatSecondDirectional d p.1 (EuclideanSpace.single a 1)
        (EuclideanSpace.single b 1) p.2) ((volume.restrict (Ioi η)).prod volume) :=
    ((Real.measurable_exp.comp measurable_fst.neg).mul
      (measurable_heatSecondDirectional _ _)).aestronglyMeasurable
  apply (integrable_prod_iff hm).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (integrable_heatSecondDirectional (hη.trans ht) (norm_single_one a)
      (norm_single_one b)).const_mul _
  · apply ((integrableOn_exp_neg_Ioi η).mul_const ((Real.exp 1 + 1 / 2) / η)).mono'
    · exact hm.norm.integral_prod_right'
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := hη.trans ht
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      simp only [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact (integral_norm_heatSecondDirectional_le ht0 (norm_single_one a)
        (norm_single_one b)).trans
        (div_le_div_of_nonneg_left (by positivity) hη ht.le)

/--
Kη ∈ L¹ for η > 0. Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions
and conclusion below.
-/
theorem integrable_truncatedSecondKernel {η : ℝ} (hη : 0 < η) (a b : Fin d) :
    Integrable (truncatedSecondKernel (d := d) η a b) :=
  (integrable_weighted_heatSecond_tail hη a b).integral_prod_right

/--
Kη is bounded for η > 0, with an explicit majorant. Source: DPR context, transcription pp. 9–10.
Exact scope: parameters, assumptions and conclusion below.
-/
theorem norm_truncatedSecondKernel_le {η : ℝ} (hη : 0 < η) (a b : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖truncatedSecondKernel η a b x‖ ≤
      Real.exp (-η) * (3 / (2 * η) * ((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹) := by
  unfold truncatedSecondKernel
  calc _ ≤ ∫ t in Ioi η, Real.exp (-t) *
        (3 / (2 * η) * ((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹) := by
        apply norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi η).mul_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_mul_of_nonneg_left (norm_heatSecondDirectional_le_sup hη ht.le
          (norm_single_one a) (norm_single_one b) x) (Real.exp_pos _).le
    _ = _ := by rw [integral_mul_const, integral_exp_neg_Ioi]


/--
Two integrations by parts at fixed time: ∫ ∂a∂b H_t · w = ∫ H_t · ∂a∂b w. Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem heatSecond_integration_by_parts {t : ℝ} (ht : 0 < t) (a b : Fin d)
    (w : ScalarCurrentTest d) :
    (∫ x, heatSecondDirectional d t (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) x *
      w x) = ∫ x, heatKernel d t x * cutoffPartialTest (cutoffPartialTest w b) a x := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (f := heatDirectional d t (EuclideanSpace.single a 1))
    (g := (w : EuclideanSpace ℝ (Fin d) → ℝ))
    (v := EuclideanSpace.single b (1 : ℝ))
    (by simpa only [← heatSecondDirectional_eq_fderiv ht] using
      integrable_mul_scalarTest (integrable_heatSecondDirectional ht (norm_single_one a)
        (norm_single_one b)) w)
    (by simpa only [← cutoffPartialTest_apply] using
      integrable_mul_scalarTest (integrable_heatDirectional ht _) (cutoffPartialTest w b))
    (integrable_mul_scalarTest (integrable_heatDirectional ht _) w)
    (fun x _ => (differentiable_heatDirectional ht _).differentiableAt)
    (fun x _ => (w.contDiff.differentiable (by simp)).differentiableAt)
  simp only [← heatSecondDirectional_eq_fderiv ht, ← cutoffPartialTest_apply] at h
  have h2 := heatKernel_integration_by_parts ht a (cutoffPartialTest w b)
  rw [h2, h, neg_neg]

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem cutoffPartialTest_neg (χ : ScalarCurrentTest d) (a : Fin d) :
    cutoffPartialTest (-χ) a = - cutoffPartialTest χ a := by
  simp only [cutoffPartialTest, map_neg]

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem cutoffPartialTest_translated (u : ScalarCurrentTest d)
    (x : EuclideanSpace ℝ (Fin d)) (b : Fin d) (y : EuclideanSpace ℝ (Fin d)) :
    cutoffPartialTest (translatedKernelTest u x) b y = - cutoffPartialTest u b (x - y) := by
  rw [cutoffPartialTest_apply, translatedKernelTest_fderiv, cutoffPartialTest_apply]

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem cutoffPartialTest_translated_test (u : ScalarCurrentTest d)
    (x : EuclideanSpace ℝ (Fin d)) (b : Fin d) :
    cutoffPartialTest (translatedKernelTest u x) b =
      - translatedKernelTest (cutoffPartialTest u b) x := by
  ext y
  rw [cutoffPartialTest_translated]
  rfl

/--
Convolution of the Gaussian Hessian against a test, at fixed time. Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem heatSecond_convolution_test {t : ℝ} (ht : 0 < t) (a b : Fin d)
    (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    scalarConvolution (heatSecondDirectional d t (EuclideanSpace.single a 1)
      (EuclideanSpace.single b 1)) u x =
      scalarConvolution (heatKernel d t) (cutoffPartialTest (cutoffPartialTest u b) a) x := by
  have h := heatSecond_integration_by_parts ht a b (translatedKernelTest u x)
  have he (y : EuclideanSpace ℝ (Fin d)) :
      cutoffPartialTest (cutoffPartialTest (translatedKernelTest u x) b) a y =
        cutoffPartialTest (cutoffPartialTest u b) a (x - y) := by
    rw [cutoffPartialTest_translated_test, cutoffPartialTest_neg]
    change -(cutoffPartialTest (translatedKernelTest (cutoffPartialTest u b) x) a y) = _
    rw [cutoffPartialTest_translated, neg_neg]
  simp only [he] at h
  exact h

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integrable_prod_mul_scalarTest_measure {μ : Measure ℝ}
    {f : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Integrable f (μ.prod volume)) (u : ScalarCurrentTest d) :
    Integrable (fun p => f p * u p.2) (μ.prod volume) := by
  apply (hf.norm.mul_const ‖(u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖).mono'
    (hf.aestronglyMeasurable.mul (u.continuous.comp continuous_snd).aestronglyMeasurable)
  exact ae_of_all _ (fun p => by
    simp only [Pi.mul_apply, Function.comp_apply, norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm p.2)
      (norm_nonneg _))

/--
Obligation no. 2, identification: Kη * u = Tη u for every test u and every η > 0. Source: DPR
context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem truncatedSecondKernel_convolution_test {η : ℝ} (hη : 0 < η) (a b : Fin d)
    (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    scalarConvolution (truncatedSecondKernel η a b) u x = truncatedSecondTest η a b u x := by
  have h := integrable_prod_mul_scalarTest_measure
    (integrable_weighted_heatSecond_tail hη a b) (translatedKernelTest u x)
  rw [truncatedSecondTest, truncatedBessel_convolution_eq_heat_integral hη.le]
  change (∫ y, (∫ t in Ioi η, Real.exp (-t) * heatSecondDirectional d t
    (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) y) * u (x - y)) = _
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (f := fun t y => (Real.exp (-t) * heatSecondDirectional d t
    (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) y) * u (x - y)) h]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [mul_assoc, integral_const_mul]
  congr 1
  exact heatSecond_convolution_test (hη.trans ht) a b u x

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem truncatedSecondKernel_convolution_test_eq {η : ℝ} (hη : 0 < η) (a b : Fin d)
    (u : ScalarCurrentTest d) :
    scalarConvolution (truncatedSecondKernel η a b) u = truncatedSecondTest η a b u :=
  funext (truncatedSecondKernel_convolution_test hη a b u)

/--
pointwise right limit, c_ab = 0. Source: DPR context, transcription pp. 9–10. Exact scope:
parameters, assumptions and conclusion below.
-/
theorem truncatedSecondKernel_tendsto (a b : Fin d) (u : ScalarCurrentTest d)
    (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun η : ℝ => scalarConvolution (truncatedSecondKernel η a b) u x)
      (𝓝[Set.Ioi 0] 0) (𝓝 (besselSecond a b u x)) := by
  have h := (truncatedSecondTest_tendsto a b u x).mono_left
    (nhdsWithin_mono _ Ioi_subset_Ici_self)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact (truncatedSecondKernel_convolution_test hη a b u x).symm


end GeometricMeasure
