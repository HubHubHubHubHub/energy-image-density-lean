import GeometricMeasure.Analysis.HeatKernel

/-!
# Bessel Kernel

## Main results
B and its candidate derivatives are defined by heat integrals. B is nonnegative, with mass and L¹
norm one; unit-direction derivatives have zero mass and norm ≤ e√π. Their identification as weak
derivatives is established in Current/BesselResolvent.

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
Bochner representative of the heat integral. Source: DPR p. 9 (context), heat-kernel representation.
-/
def besselKernel (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-t) * heatKernel d t x

/--
The chosen representative is everywhere nonnegative. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem besselKernel_nonneg (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ besselKernel d x := by
  exact integral_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg d t x))

/--
absolute integrability on the time-space product. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integrable_weighted_heatKernel (d : ℕ) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      Real.exp (-p.1) * heatKernel d p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  apply (integrable_prod_iff (by
    exact (Real.measurable_exp.comp measurable_fst.neg |>.mul
      (measurable_heatKernel d)).aestronglyMeasurable)).2
  constructor
  · exact ae_of_all _ (fun t => (integrable_heatKernel d t).const_mul (Real.exp (-t)))
  · apply (integrableOn_exp_neg_Ioi (0 : ℝ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [norm_mul, Real.norm_of_nonneg (Real.exp_pos (-t)).le,
      integral_const_mul, integral_norm_heatKernel d ht, mul_one]

/--
The Bessel representative is integrable, with no points excluded. Source: DPR p. 9 (context),
heat-kernel representation.
-/
theorem integrable_besselKernel (d : ℕ) : Integrable (besselKernel d) :=
  (integrable_weighted_heatKernel d).integral_prod_right

/--
For almost every spatial point, the section as a function of time is integrable. Source: DPR p. 9
(context), heat-kernel representation.
-/
theorem besselKernel_time_integrable_ae (d : ℕ) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin d),
      IntegrableOn (fun t => Real.exp (-t) * heatKernel d t x) (Ioi 0) :=
  (integrable_weighted_heatKernel d).prod_left_ae

/--
mass exactly one, by Fubini with absolute integrability proved. Source: DPR p. 9 (context),
heat-kernel representation.
-/
theorem integral_besselKernel (d : ℕ) : (∫ x, besselKernel d x) = 1 := by
  unfold besselKernel
  rw [← integral_integral_swap (f := fun t x => Real.exp (-t) * heatKernel d t x)
    (integrable_weighted_heatKernel d)]
  calc
    (∫ t in Ioi (0 : ℝ), ∫ x, Real.exp (-t) * heatKernel d t x) =
        ∫ t in Ioi (0 : ℝ), Real.exp (-t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [integral_const_mul, integral_heatKernel d ht, mul_one]
    _ = 1 := integral_exp_neg_Ioi_zero

/-- L¹ norm exactly one. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem integral_norm_besselKernel (d : ℕ) : (∫ x, ‖besselKernel d x‖) = 1 := by
  simpa only [Real.norm_of_nonneg (besselKernel_nonneg d _)] using integral_besselKernel d

/--
candidate weak derivative, constructed by the heat integral. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def besselDirectional (d : ℕ) (v x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-t) * heatDirectional d t v x

/-- integrable time majorant. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem integrable_exp_neg_inv_sqrt :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / Real.sqrt t) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_rpow
    (s := -(1/2 : ℝ)) (p := 1) (by norm_num) le_rfl
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.rpow_one, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  exact mul_comm _ _

/--
integral of the time majorant, via Gamma(1/2). Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integral_exp_neg_inv_sqrt :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t) / Real.sqrt t) = Real.sqrt Real.pi := by
  rw [← Real.Gamma_one_half_eq, Real.Gamma_eq_integral (by norm_num : (0:ℝ) < 1/2)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  norm_num only [show (1/2 : ℝ) - 1 = -(1/2) by norm_num]
  rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

/--
joint measurability of the weighted derivative kernel. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem measurable_weighted_heatDirectional (v : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      Real.exp (-p.1) * heatDirectional d p.1 v p.2) := by
  unfold heatDirectional
  exact (Real.measurable_exp.comp measurable_fst.neg).mul
    ((((continuous_const.inner continuous_snd).measurable.div
      (measurable_const.mul measurable_fst)).neg).mul (measurable_heatKernel d))

/--
absolute integrability of the derivative kernel on the product, for a unit direction. Source: DPR p.
9 (context), heat-kernel representation.
-/
theorem integrable_weighted_heatDirectional (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      Real.exp (-p.1) * heatDirectional d p.1 v p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hm := (measurable_weighted_heatDirectional v).aestronglyMeasurable
    (μ := (volume.restrict (Ioi (0 : ℝ))).prod volume)
  apply (integrable_prod_iff hm).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (integrable_heatDirectional ht v).const_mul (Real.exp (-t))
  · apply (integrable_exp_neg_inv_sqrt.const_mul (Real.exp 1)).mono'
      hm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖∫ y, ‖Real.exp (-t) * heatDirectional d t v y‖‖ ≤
      Real.exp 1 * (Real.exp (-t) / Real.sqrt t)
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simp only [norm_mul, Real.norm_of_nonneg (Real.exp_pos (-t)).le, integral_const_mul]
    have h := mul_le_mul_of_nonneg_left (integral_norm_heatDirectional_le ht v hv)
      (Real.exp_pos (-t)).le
    have he : Real.exp (-t) * (Real.exp 1 / Real.sqrt t) =
        Real.exp 1 * (Real.exp (-t) / Real.sqrt t) := by ring
    rw [← he]
    exact h

/--
Bessel derivative in L¹, for a unit direction. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integrable_besselDirectional (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    Integrable (besselDirectional d v) :=
  (integrable_weighted_heatDirectional v hv).integral_prod_right

/--
explicit, nonoptimal bound e sqrt(pi), for a unit direction. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integral_norm_besselDirectional_le (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    (∫ x, ‖besselDirectional d v x‖) ≤ Real.exp 1 * Real.sqrt Real.pi := by
  have h := integrable_weighted_heatDirectional v hv
  calc
    _ ≤ ∫ x, ∫ t in Ioi (0 : ℝ), ‖Real.exp (-t) * heatDirectional d t v x‖ :=
      integral_mono (integrable_besselDirectional v hv).norm h.integral_norm_prod_right
        (fun x => norm_integral_le_integral_norm _)
    _ = ∫ t in Ioi (0 : ℝ), ∫ x, ‖Real.exp (-t) * heatDirectional d t v x‖ :=
      (integral_integral_swap (f := fun t x => ‖Real.exp (-t) * heatDirectional d t v x‖)
        h.norm).symm
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp 1 * (Real.exp (-t) / Real.sqrt t) := by
      apply integral_mono_ae h.integral_norm_prod_left
        (integrable_exp_neg_inv_sqrt.const_mul (Real.exp 1))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [norm_mul, Real.norm_of_nonneg (Real.exp_pos (-t)).le, integral_const_mul]
      convert mul_le_mul_of_nonneg_left (integral_norm_heatDirectional_le ht v hv)
        (Real.exp_pos (-t)).le using 1
      ring
    _ = _ := by rw [integral_const_mul, integral_exp_neg_inv_sqrt]

/--
The Bessel derivative has zero mass for a unit direction. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integral_besselDirectional (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    (∫ x, besselDirectional d v x) = 0 := by
  unfold besselDirectional
  rw [← integral_integral_swap (f := fun t x => Real.exp (-t) * heatDirectional d t v x)
    (integrable_weighted_heatDirectional v hv)]
  simp only [integral_const_mul, integral_heatDirectional, mul_zero, integral_zero]

/--
representative of the coordinate derivative B_a. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def besselPartial (d : ℕ) (a : Fin d) : EuclideanSpace ℝ (Fin d) → ℝ :=
  besselDirectional d (EuclideanSpace.single a (1 : ℝ))

/-- integrability of B_a. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem integrable_besselPartial (a : Fin d) : Integrable (besselPartial d a) :=
  integrable_besselDirectional _ (by simp)

/--
L¹ norm bound on B_a, with an explicit constant. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integral_norm_besselPartial_le (a : Fin d) :
    (∫ x, ‖besselPartial d a x‖) ≤ Real.exp 1 * Real.sqrt Real.pi :=
  integral_norm_besselDirectional_le _ (by simp)

/-- B_a has zero mass. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem integral_besselPartial (a : Fin d) : (∫ x, besselPartial d a x) = 0 :=
  integral_besselDirectional _ (by simp)

end GeometricMeasure
