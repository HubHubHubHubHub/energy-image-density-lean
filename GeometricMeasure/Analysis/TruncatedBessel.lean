import GeometricMeasure.Analysis.HeatHessian
import GeometricMeasure.Analysis.BesselKernel

/-!
# Truncated Bessel

## Main results
Truncated potential: mass for η ≥ 0, continuity and bound for η > 0. Integrable bounded derivative
kernel for η > 0; identification on tests, rates and time limits. No C³ regularity of the potential
is claimed.

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
time-truncated potential, Bochner representative. Source: DPR context, transcription pp. 9–10. Exact
scope: parameters, assumptions and conclusion below.
-/
def truncatedBessel (d : ℕ) (η : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ t in Ioi η, Real.exp (-t) * heatKernel d t x

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem truncatedBessel_nonneg (d : ℕ) (η : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ truncatedBessel d η x := by
  exact integral_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg d t x))

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integrable_weighted_heatKernel_tail (d : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      Real.exp (-p.1) * heatKernel d p.1 p.2)
      ((volume.restrict (Ioi η)).prod volume) := by
  apply (integrable_prod_iff (by
    exact (Real.measurable_exp.comp measurable_fst.neg |>.mul
      (measurable_heatKernel d)).aestronglyMeasurable)).2
  constructor
  · exact ae_of_all _ (fun t => (integrable_heatKernel d t).const_mul (Real.exp (-t)))
  · apply (integrableOn_exp_neg_Ioi η).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [norm_mul, Real.norm_of_nonneg (Real.exp_pos (-t)).le,
      integral_const_mul, integral_norm_heatKernel d (lt_of_le_of_lt hη ht), mul_one]

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integrable_truncatedBessel (d : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    Integrable (truncatedBessel d η) :=
  (integrable_weighted_heatKernel_tail d hη).integral_prod_right

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integral_truncatedBessel (d : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    (∫ x, truncatedBessel d η x) = Real.exp (-η) := by
  unfold truncatedBessel
  rw [← integral_integral_swap (f := fun t x => Real.exp (-t) * heatKernel d t x)
    (integrable_weighted_heatKernel_tail d hη)]
  calc
    (∫ t in Ioi η, ∫ x, Real.exp (-t) * heatKernel d t x) =
        ∫ t in Ioi η, Real.exp (-t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [integral_const_mul, integral_heatKernel d (lt_of_le_of_lt hη ht), mul_one]
    _ = _ := integral_exp_neg_Ioi η

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integral_norm_truncatedBessel (d : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    (∫ x, ‖truncatedBessel d η x‖) = Real.exp (-η) := by
  simpa only [Real.norm_of_nonneg (truncatedBessel_nonneg d η _)] using
    integral_truncatedBessel d hη

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem truncatedBessel_zero (d : ℕ) : truncatedBessel d 0 = besselKernel d := rfl

/--
An almost-everywhere comparison: no pointwise assertion about B(0). Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem truncatedBessel_le_besselKernel_ae (d : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    ∀ᵐ x, truncatedBessel d η x ≤ besselKernel d x := by
  filter_upwards [besselKernel_time_integrable_ae d] with x hx
  exact setIntegral_mono_set hx (ae_of_all _ (fun t =>
    mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg d t x)))
    (ae_of_all _ (fun t ht => lt_of_le_of_lt hη ht))

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integral_norm_besselKernel_sub_truncated (d : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    (∫ x, ‖besselKernel d x - truncatedBessel d η x‖) = 1 - Real.exp (-η) := by
  calc
    _ = ∫ x, besselKernel d x - truncatedBessel d η x := by
      apply integral_congr_ae
      filter_upwards [truncatedBessel_le_besselKernel_ae d hη] with x hx
      exact Real.norm_of_nonneg (sub_nonneg.mpr hx)
    _ = _ := by
      rw [integral_sub (integrable_besselKernel d) (integrable_truncatedBessel d hη),
        integral_besselKernel, integral_truncatedBessel d hη]

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem one_sub_exp_neg_le {η : ℝ} : 1 - Real.exp (-η) ≤ η := by
  have h := Real.add_one_le_exp (-η)
  linarith

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem truncatedBessel_time_integrable {η : ℝ} (hη : 0 < η)
    (x : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun t => Real.exp (-t) * heatKernel d t x) (Ioi η) := by
  apply ((integrableOn_exp_neg_Ioi η).mul_const
    (((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹)).mono'
  · exact ((Real.measurable_exp.comp measurable_id.neg).mul
      ((measurable_heatKernel d).comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg d t x))]
    exact mul_le_mul_of_nonneg_left (heatKernel_le_at_positive_time hη ht.le x)
      (Real.exp_pos _).le

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem norm_truncatedBessel_le {η : ℝ} (hη : 0 < η)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖truncatedBessel d η x‖ ≤
      Real.exp (-η) * ((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹ := by
  rw [Real.norm_of_nonneg (truncatedBessel_nonneg d η x)]
  calc
    _ ≤ ∫ t in Ioi η, Real.exp (-t) * ((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹ := by
      apply integral_mono_ae (truncatedBessel_time_integrable hη x)
        ((integrableOn_exp_neg_Ioi η).mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_le_mul_of_nonneg_left (heatKernel_le_at_positive_time hη ht.le x)
        (Real.exp_pos _).le
    _ = _ := by rw [integral_mul_const, integral_exp_neg_Ioi]

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem truncatedBessel_memLp_top {η : ℝ} (hη : 0 < η) :
    MemLp (truncatedBessel d η) ⊤ :=
  memLp_top_of_bound (integrable_truncatedBessel d hη.le).aestronglyMeasurable _
    (ae_of_all _ (norm_truncatedBessel_le hη))

/--
Actual continuity of the potential at each η>0. C³ remains a separate obligation. Source: DPR
context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem continuous_truncatedBessel {η : ℝ} (hη : 0 < η) :
    Continuous (truncatedBessel d η) := by
  apply continuous_of_dominated (bound := fun t =>
    Real.exp (-t) * ((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹)
  · intro x
    exact (truncatedBessel_time_integrable hη x).aestronglyMeasurable
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg d t x))]
    exact mul_le_mul_of_nonneg_left (heatKernel_le_at_positive_time hη ht.le x) (Real.exp_pos _).le
  · exact (integrableOn_exp_neg_Ioi η).mul_const _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact continuous_const.mul (differentiable_heatKernel (hη.trans ht)).continuous

/--
Candidate truncated derivative kernel; the definition contains no integrability assertion. Source:
DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
def truncatedSecondKernel (η : ℝ) (a b : Fin d) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ t in Ioi η, Real.exp (-t) *
    heatSecondDirectional d t (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) x

/--
Strong measurability of Kη for every η. Source: DPR context, transcription pp. 9–10. Exact scope:
parameters, assumptions and conclusion below.
-/
theorem stronglyMeasurable_truncatedSecondKernel (η : ℝ) (a b : Fin d) :
    StronglyMeasurable (truncatedSecondKernel (d := d) η a b) := by
  have h : StronglyMeasurable (Function.uncurry fun (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) =>
      Real.exp (-t) * heatSecondDirectional d t (EuclideanSpace.single a 1)
        (EuclideanSpace.single b 1) x) :=
    ((Real.measurable_exp.comp measurable_fst.neg).mul
      (measurable_heatSecondDirectional _ _)).stronglyMeasurable
  exact h.integral_prod_left (μ := volume.restrict (Ioi η))

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem differentiable_heatDirectional {t : ℝ} (ht : 0 < t) (v : EuclideanSpace ℝ (Fin d)) :
    Differentiable ℝ (heatDirectional d t v) := by
  intro x
  have hlin := (((innerSL ℝ v).hasFDerivAt (x := x)).mul_const (2 * t)⁻¹).neg
  have h := hlin.mul ((differentiable_heatKernel ht x).hasFDerivAt)
  change HasFDerivAt (heatDirectional d t v) _ x at h
  exact h.differentiableAt

end GeometricMeasure
