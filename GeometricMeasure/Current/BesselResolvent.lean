import GeometricMeasure.Analysis.BesselKernel
import GeometricMeasure.Current.LocalizedMollification
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Bessel Resolvent

## Main results
Weak derivatives and pointwise resolvent B*(u−Δu)=u in every dimension. Continuity at zero and the
time derivative are proved by dilation and integration by parts. The evolution and resolvent
hypotheses are proved by heatEvolution_holds and besselResolves_holds. The resolvent identity is
stated on smooth tests.

Bibliographic context: De Philippis–Rindler, p. 9, (2.9)–(2.10). The heat-kernel argument is a
specialization. The Annals page reference, pp. 1027–1028, is unverified against that edition.
-/


noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped Topology RealInnerProductSpace Convolution
namespace GeometricMeasure
variable {d : ℕ}

/-- integrability of every scalar test. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem scalarTest_integrable (u : ScalarCurrentTest d) :
    Integrable (u : EuclideanSpace ℝ (Fin d) → ℝ) :=
  u.continuous.integrable_of_hasCompactSupport u.hasCompactSupport

/--
The integral of a compactly supported derivative is zero. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integral_cutoffPartialTest (u : ScalarCurrentTest d) (a : Fin d) :
    (∫ x, cutoffPartialTest u a x) = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (f := fun _ => (1 : ℝ)) (g := (u : EuclideanSpace ℝ (Fin d) → ℝ))
    (v := EuclideanSpace.single a (1 : ℝ))
    (by simp) (by simpa only [one_mul, ← cutoffPartialTest_apply] using
      scalarTest_integrable (cutoffPartialTest u a))
    (by simpa using scalarTest_integrable u)
    (fun _ _ => differentiableAt_const _)
    (fun x _ => (u.contDiff.differentiable (by simp)).differentiableAt)
  simpa only [one_mul, ← cutoffPartialTest_apply, fderiv_const_apply, zero_apply,
    zero_mul, integral_zero, neg_zero] using h

/--
Laplacian in orthonormal coordinates, on tests. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def scalarTestLaplacian (u : ScalarCurrentTest d) : ScalarCurrentTest d :=
  ∑ a : Fin d, cutoffPartialTest (cutoffPartialTest u a) a

/-- The Laplacian has zero mass. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem integral_scalarTestLaplacian (u : ScalarCurrentTest d) :
    (∫ x, scalarTestLaplacian u x) = 0 := by
  simp only [scalarTestLaplacian, ← FunLike.coeAddMonoidHom_apply, map_sum, Finset.sum_apply]
  simp only [FunLike.coeAddMonoidHom_apply]
  rw [integral_finsetSum]
  · simp only [integral_cutoffPartialTest, Finset.sum_const_zero]
  · intro a _
    exact scalarTest_integrable _

/--
pointwise existence on a test for an L¹ kernel. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem scalarConvolution_exists (K : EuclideanSpace ℝ (Fin d) → ℝ)
    (hK : Integrable K) (u : ScalarCurrentTest d) :
    ConvolutionExists K (u : EuclideanSpace ℝ (Fin d) → ℝ)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
  u.hasCompactSupport.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
    hK.locallyIntegrable u.continuous

/--
resolution by a separately verified heat trajectory. The analytic assumptions are explicit; no
resolvent identity is postulated. Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem resolvent_of_heat_trajectory
    {P Q : ℝ → ℝ} {u : ℝ}
    (hzero : P 0 = u) (hcont : ContinuousWithinAt P (Ici 0) 0)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt P (-Q t) t)
    (hQ : IntegrableOn Q (Ioi 0)) (hinfty : Tendsto P atTop (𝓝 0)) :
    (∫ t in Ioi (0 : ℝ), Q t) = u := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hQ.neg hinfty
  rw [integral_neg, hzero, zero_sub, neg_inj] at h
  exact h

/-- a bounded test factor preserves L¹. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem integrable_mul_scalarTest {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Integrable f) (u : ScalarCurrentTest d) : Integrable (fun x => f x * u x) := by
  apply (hf.norm.mul_const ‖(u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖).mono'
    (hf.aestronglyMeasurable.mul u.continuous.aestronglyMeasurable)
  exact ae_of_all _ (fun x => by
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm x)
      (norm_nonneg _))

/--
The same bound on the time-space product. Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem integrable_prod_mul_scalarTest
    {f : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Integrable f ((volume.restrict (Ioi (0 : ℝ))).prod volume))
    (u : ScalarCurrentTest d) :
    Integrable (fun p => f p * u p.2) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  apply (hf.norm.mul_const ‖(u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖).mono'
    (hf.aestronglyMeasurable.mul (u.continuous.comp continuous_snd).aestronglyMeasurable)
  exact ae_of_all _ (fun p => by
    simp only [Pi.mul_apply, Function.comp_apply, norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm p.2)
      (norm_nonneg _))

/--
integration by parts against a test at fixed time. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem heatKernel_integration_by_parts {t : ℝ} (ht : 0 < t)
    (a : Fin d) (u : ScalarCurrentTest d) :
    (∫ x, heatKernel d t x * cutoffPartialTest u a x) =
      - ∫ x, heatDirectional d t (EuclideanSpace.single a 1) x * u x := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (f := heatKernel d t) (g := (u : EuclideanSpace ℝ (Fin d) → ℝ))
    (v := EuclideanSpace.single a (1 : ℝ))
    (by simpa only [← heatDirectional_eq_fderiv ht] using
      integrable_mul_scalarTest (integrable_heatDirectional ht _) u)
    (by simpa only [← cutoffPartialTest_apply] using
      integrable_mul_scalarTest (integrable_heatKernel d t) (cutoffPartialTest u a))
    (integrable_mul_scalarTest (integrable_heatKernel d t) u)
    (fun x _ => (differentiable_heatKernel ht).differentiableAt)
    (fun x _ => (u.contDiff.differentiable (by simp)).differentiableAt)
  simpa only [← heatDirectional_eq_fderiv ht, ← cutoffPartialTest_apply] using h

/--
B_a actually represents the distributional derivative of B. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem besselPartial_weak_derivative (a : Fin d) (u : ScalarCurrentTest d) :
    (∫ x, besselKernel d x * cutoffPartialTest u a x) =
      - ∫ x, besselPartial d a x * u x := by
  have hH := integrable_prod_mul_scalarTest (integrable_weighted_heatKernel d)
    (cutoffPartialTest u a)
  have hD := integrable_prod_mul_scalarTest
    (integrable_weighted_heatDirectional (EuclideanSpace.single a 1) (by simp)) u
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∫ x,
        (Real.exp (-t) * heatKernel d t x) * cutoffPartialTest u a x := by
      simp only [besselKernel, ← integral_mul_const]
      exact (integral_integral_swap (f := fun t x =>
        (Real.exp (-t) * heatKernel d t x) * cutoffPartialTest u a x) hH).symm
    _ = ∫ t in Ioi (0 : ℝ), - ∫ x,
        (Real.exp (-t) * heatDirectional d t (EuclideanSpace.single a 1) x) * u x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [mul_assoc, integral_const_mul, heatKernel_integration_by_parts ht,
        mul_neg]
    _ = - ∫ x, ∫ t in Ioi (0 : ℝ),
        (Real.exp (-t) * heatDirectional d t (EuclideanSpace.single a 1) x) * u x := by
      rw [integral_neg, integral_integral_swap (f := fun t x =>
        (Real.exp (-t) * heatDirectional d t (EuclideanSpace.single a 1) x) * u x) hD]
    _ = _ := by simp only [besselPartial, besselDirectional, integral_mul_const]

/--
pointwise transfer of a derivative to B in convolution. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem besselPartial_convolution (a : Fin d) (u : ScalarCurrentTest d)
    (x : EuclideanSpace ℝ (Fin d)) :
    scalarConvolution (besselKernel d) (cutoffPartialTest u a) x =
      scalarConvolution (besselPartial d a) u x := by
  have h := besselPartial_weak_derivative a (translatedKernelTest u x)
  have he (y : EuclideanSpace ℝ (Fin d)) :
      cutoffPartialTest (translatedKernelTest u x) a y = -cutoffPartialTest u a (x-y) := by
    rw [cutoffPartialTest_apply, translatedKernelTest_fderiv, cutoffPartialTest_apply]
  simp only [he, mul_neg, integral_neg] at h
  exact neg_injective h

/--
convolution by an L¹ kernel is linear on tests. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def scalarConvolutionTest (K : EuclideanSpace ℝ (Fin d) → ℝ) (hK : Integrable K) :
    ScalarCurrentTest d →ₗ[ℝ] (EuclideanSpace ℝ (Fin d) → ℝ) where
  toFun u := scalarConvolution K u
  map_add' u v := by
    exact (scalarConvolution_exists K hK u).distrib_add
      (scalarConvolution_exists K hK v)
  map_smul' c u := by
    ext x
    simp only [scalarConvolution_apply, smul_apply, smul_eq_mul, Pi.smul_apply]
    simp_rw [show ∀ y, K y * (c * u (x-y)) = c * (K y * u (x-y)) by intro y; ring]
    exact integral_const_mul _ _

/--
source with two derivatives and row-wise divergence. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def doubleDivergenceTest (f : Fin d → Fin d → ScalarCurrentTest d) : ScalarCurrentTest d :=
  ∑ a : Fin d, ∑ b : Fin d, cutoffPartialTest (cutoffPartialTest (f a b) b) a

/--
divergence of the regular right-hand side. Source: DPR p. 9 (context), heat-kernel representation.
-/
def divergenceTest (g : Fin d → ScalarCurrentTest d) : ScalarCurrentTest d :=
  ∑ a : Fin d, cutoffPartialTest (g a) a

/--
gradient equation on tests, before taking a divergence. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def SmoothGradientEquation (z : ScalarCurrentTest d)
    (f : Fin d → Fin d → ScalarCurrentTest d) (g : Fin d → ScalarCurrentTest d) : Prop :=
  ∀ a, cutoffPartialTest z a = (∑ b : Fin d, cutoffPartialTest (f a b) b) + g a

/--
taking a divergence in the gradient equation. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem scalarTestLaplacian_eq_of_gradient {z : ScalarCurrentTest d}
    {f : Fin d → Fin d → ScalarCurrentTest d} {g : Fin d → ScalarCurrentTest d}
    (heq : SmoothGradientEquation z f g) :
    scalarTestLaplacian z = doubleDivergenceTest f + divergenceTest g := by
  unfold SmoothGradientEquation at heq
  unfold scalarTestLaplacian
  simp_rw [heq]
  simp only [cutoffPartialTest, map_add, map_sum, Finset.sum_add_distrib,
    doubleDivergenceTest, divergenceTest]

/--
resolvent property, proved in every dimension by besselResolves_holds. Source: DPR p. 9 (context),
heat-kernel representation.
-/
def BesselResolves (d : ℕ) : Prop :=
  ∀ u : ScalarCurrentTest d,
    scalarConvolution (besselKernel d) (u - scalarTestLaplacian u : ScalarCurrentTest d) = u

/--
order-zero operator restricted to test inputs. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def besselSecond (a b : Fin d) (u : ScalarCurrentTest d) : EuclideanSpace ℝ (Fin d) → ℝ :=
  scalarConvolution (besselKernel d) (cutoffPartialTest (cutoffPartialTest u b) a)

/-- zero-mass term. Source: DPR p. 9 (context), heat-kernel representation. -/
def resolventError (f : Fin d → Fin d → ScalarCurrentTest d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  - scalarConvolution (besselKernel d) (doubleDivergenceTest f)

/--
regularizing term with the signs of the resolvent decomposition. Source: DPR p. 9 (context),
heat-kernel representation.
-/
def resolventRegular (z : ScalarCurrentTest d) (g : Fin d → ScalarCurrentTest d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  scalarConvolution (besselKernel d) z - ∑ a : Fin d, scalarConvolution (besselPartial d a) (g a)

/-- expression as a sum of the S_ab. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem resolventError_eq_sum (f : Fin d → Fin d → ScalarCurrentTest d) :
    resolventError f = - ∑ a : Fin d, ∑ b : Fin d, besselSecond a b (f a b) := by
  change -(scalarConvolutionTest (besselKernel d) (integrable_besselKernel d)
    (doubleDivergenceTest f)) = _
  simp only [doubleDivergenceTest, map_sum]
  rfl

/-- integrability of each S_ab. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem integrable_besselSecond (a b : Fin d) (u : ScalarCurrentTest d) :
    Integrable (besselSecond a b u) :=
  integrable_scalarConvolution (integrable_besselKernel d) (scalarTest_integrable _)

/-- Each S_ab has zero mass. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem integral_besselSecond (a b : Fin d) (u : ScalarCurrentTest d) :
    (∫ x, besselSecond a b u x) = 0 := by
  rw [besselSecond, integral_scalarConvolution (integrable_besselKernel d)
    (scalarTest_integrable _), integral_cutoffPartialTest, mul_zero]

/--
individual estimate involving derivatives of the input. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integral_norm_besselSecond_le (a b : Fin d) (u : ScalarCurrentTest d) :
    (∫ x, ‖besselSecond a b u x‖) ≤
      ∫ x, ‖cutoffPartialTest (cutoffPartialTest u b) a x‖ := by
  simpa only [besselSecond, integral_norm_besselKernel, one_mul] using
    integral_norm_scalarConvolution_le (integrable_besselKernel d)
      (scalarTest_integrable (cutoffPartialTest (cutoffPartialTest u b) a))

/--
t belongs to L¹ without a resolvent assumption. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integrable_resolventError (f : Fin d → Fin d → ScalarCurrentTest d) :
    Integrable (resolventError f) :=
  (integrable_scalarConvolution (integrable_besselKernel d) (scalarTest_integrable _)).neg

/--
The source with two derivatives has zero mass. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integral_doubleDivergenceTest (f : Fin d → Fin d → ScalarCurrentTest d) :
    (∫ x, doubleDivergenceTest f x) = 0 := by
  simp only [doubleDivergenceTest, ← FunLike.coeAddMonoidHom_apply, map_sum, Finset.sum_apply]
  simp only [FunLike.coeAddMonoidHom_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro a _
    rw [integral_finsetSum]
    · simp only [integral_cutoffPartialTest, Finset.sum_const_zero]
    · intro b _; exact scalarTest_integrable _
  · intro a _
    exact integrable_finsetSum _ (fun b _ => scalarTest_integrable _)

/--
t has zero mass without a resolvent assumption. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integral_resolventError (f : Fin d → Fin d → ScalarCurrentTest d) :
    (∫ x, resolventError f x) = 0 := by
  simp only [resolventError, Pi.neg_apply, integral_neg]
  rw [integral_scalarConvolution (integrable_besselKernel d) (scalarTest_integrable _),
    integral_doubleDivergenceTest, mul_zero, neg_zero]

/--
h belongs to L¹ without a resolvent assumption. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integrable_resolventRegular (z : ScalarCurrentTest d) (g : Fin d → ScalarCurrentTest d) :
    Integrable (resolventRegular z g) := by
  unfold resolventRegular
  apply (integrable_scalarConvolution (integrable_besselKernel d) (scalarTest_integrable z)).sub
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum Finset.univ (fun a _ =>
      integrable_scalarConvolution (integrable_besselPartial a) (scalarTest_integrable (g a))))

/--
conditional assembly; the resolvent assumption is named. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem resolvent_decomposition (hres : BesselResolves d) (z : ScalarCurrentTest d)
    (f : Fin d → Fin d → ScalarCurrentTest d) (g : Fin d → ScalarCurrentTest d)
    (heq : SmoothGradientEquation z f g) :
    (z : EuclideanSpace ℝ (Fin d) → ℝ) = resolventError f + resolventRegular z g := by
  let T := scalarConvolutionTest (besselKernel d) (integrable_besselKernel d)
  have hz : T (z - scalarTestLaplacian z) = z := hres z
  rw [scalarTestLaplacian_eq_of_gradient heq, map_sub, map_add] at hz
  have hg : T (divergenceTest g) =
      ∑ a : Fin d, scalarConvolution (besselPartial d a) (g a) := by
    simp only [divergenceTest, map_sum]
    congr 1
    ext a x
    exact besselPartial_convolution a (g a) x
  rw [hg] at hz
  rw [← hz]
  change T z - (T (doubleDivergenceTest f) + _) = -T (doubleDivergenceTest f) + (T z - _)
  abel

/--
package of conclusions with the resolvent assumption visible. Source: DPR p. 9 (context),
heat-kernel representation.
-/
theorem resolvent_L6 (hres : BesselResolves d) (z : ScalarCurrentTest d)
    (f : Fin d → Fin d → ScalarCurrentTest d) (g : Fin d → ScalarCurrentTest d)
    (heq : SmoothGradientEquation z f g) :
    (z : EuclideanSpace ℝ (Fin d) → ℝ) = resolventError f + resolventRegular z g ∧
    Integrable (resolventError f) ∧ Integrable (resolventRegular z g) ∧
    (∫ x, resolventError f x) = 0 :=
  ⟨resolvent_decomposition hres z f g heq, integrable_resolventError f,
    integrable_resolventRegular z g, integral_resolventError f⟩

/--
smoothed trajectory, extended at time zero by the test. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def heatTrajectory (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) : ℝ :=
  if t = 0 then u x else Real.exp (-t) * scalarConvolution (heatKernel d t) u x

/--
pointwise convolution bound on a bounded test. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem norm_scalarConvolution_test_le {K : EuclideanSpace ℝ (Fin d) → ℝ}
    (hK : Integrable K) (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    ‖scalarConvolution K u x‖ ≤ (∫ y, ‖K y‖) *
      ‖(u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ := by
  calc
    _ ≤ ∫ y, ‖K y * u (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖K y‖ * ‖(u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ := by
      apply integral_mono (scalarConvolution_exists K hK u x).norm (hK.norm.mul_const _)
      intro y
      change ‖K y * u (x-y)‖ ≤ ‖K y‖ *
        ‖(u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        ((u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm _)
        (norm_nonneg _)
    _ = _ := integral_mul_const _ _

/--
uniform e^-t decay of the weighted trajectory. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem norm_heatTrajectory_le (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d))
    (t : ℝ) : ‖heatTrajectory u x t‖ ≤ Real.exp (-t) *
      ‖(u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ := by
  by_cases h0 : t = 0
  · subst t
    simpa [heatTrajectory] using
      (u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm x
  · by_cases ht : 0 < t
    · simp only [heatTrajectory, if_neg h0, norm_mul, Real.norm_of_nonneg (Real.exp_pos (-t)).le]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos (-t)).le
      simpa only [integral_norm_heatKernel d ht, one_mul] using
        norm_scalarConvolution_test_le (integrable_heatKernel d t) u x
    · simp only [heatTrajectory, if_neg h0]
      have hk : heatKernel d t = 0 := by ext y; simp [heatKernel, ht]
      rw [hk]
      simp [scalarConvolution]
      positivity

/--
The limit at infinity is proved, rather than supplied as an assumption field. Source: DPR p. 9
(context), heat-kernel representation.
-/
theorem heatTrajectory_tendsto_zero (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto (heatTrajectory u x) atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_heatTrajectory_le u x)
  have h := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const
    ‖(u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖
  simpa only [zero_mul, Function.comp_apply] using h

/--
analytic resolvent interface, realized by heatEvolution_holds. The differentiation field concerns
the constructed heat kernel, rather than B*(I-Delta). Source: DPR p. 9 (context), heat-kernel
representation.
-/
structure HeatEvolution (d : ℕ) : Prop where
  continuous_zero : ∀ (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)),
    ContinuousWithinAt (heatTrajectory u x) (Ici 0) 0
  derivative : ∀ (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ),
    0 < t → HasDerivAt (heatTrajectory u x)
      (-(Real.exp (-t) * scalarConvolution (heatKernel d t) (u - scalarTestLaplacian u : ScalarCurrentTest d) x)) t

/--
pointwise Fubini for the heat representation of B*u. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem besselConvolution_eq_heat_integral (u : ScalarCurrentTest d)
    (x : EuclideanSpace ℝ (Fin d)) :
    scalarConvolution (besselKernel d) u x =
      ∫ t in Ioi (0 : ℝ), Real.exp (-t) * scalarConvolution (heatKernel d t) u x := by
  have h := integrable_prod_mul_scalarTest (integrable_weighted_heatKernel d)
    (translatedKernelTest u x)
  change (∫ y, (∫ t in Ioi (0:ℝ), Real.exp (-t) * heatKernel d t y) * u (x-y)) = _
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (f := fun t y =>
    (Real.exp (-t) * heatKernel d t y) * u (x-y)) h]
  simp only [mul_assoc, integral_const_mul, scalarConvolution_apply]

/--
The resolvent integrand is time-integrable at each point. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integrable_heat_convolution (u : ScalarCurrentTest d)
    (x : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun t => Real.exp (-t) * scalarConvolution (heatKernel d t) u x) (Ioi 0) := by
  have h := (integrable_prod_mul_scalarTest (integrable_weighted_heatKernel d)
    (translatedKernelTest u x)).integral_prod_left
  simpa only [translatedKernelTest, TestFunction.coe_mk, mul_assoc, integral_const_mul,
    scalarConvolution_apply, IntegrableOn] using h

/--
proof of the resolvent by time integration, under HeatEvolution. Source: DPR p. 9 (context),
heat-kernel representation.
-/
theorem besselResolves_of_heatEvolution (h : HeatEvolution d) : BesselResolves d := by
  intro u
  ext x
  rw [besselConvolution_eq_heat_integral]
  apply resolvent_of_heat_trajectory (P := heatTrajectory u x)
    (by simp [heatTrajectory]) (h.continuous_zero u x)
    (fun t ht => h.derivative u x t ht)
    (integrable_heat_convolution (u - scalarTestLaplacian u : ScalarCurrentTest d) x) (heatTrajectory_tendsto_zero u x)

/--
L¹ norm bound on the regular term, with the constant actually proved. Source: DPR p. 9 (context),
heat-kernel representation.
-/
theorem integral_norm_resolventRegular_le (z : ScalarCurrentTest d)
    (g : Fin d → ScalarCurrentTest d) :
    (∫ x, ‖resolventRegular z g x‖) ≤
      (∫ x, ‖z x‖) + (Real.exp 1 * Real.sqrt Real.pi) * ∑ a : Fin d, ∫ x, ‖g a x‖ := by
  have hi (a : Fin d) :=
    integrable_scalarConvolution (integrable_besselPartial a) (scalarTest_integrable (g a))
  calc
    _ ≤ ∫ x, ‖scalarConvolution (besselKernel d) z x‖ +
        ∑ a : Fin d, ‖scalarConvolution (besselPartial d a) (g a) x‖ := by
      apply integral_mono (integrable_resolventRegular z g).norm
        ((integrable_scalarConvolution (integrable_besselKernel d) (scalarTest_integrable z)).norm.add
          (integrable_finsetSum _ (fun a _ => (hi a).norm)))
      intro x
      change ‖scalarConvolution (besselKernel d) z x -
        (∑ a : Fin d, scalarConvolution (besselPartial d a) (g a)) x‖ ≤ _
      rw [Finset.sum_apply]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ = (∫ x, ‖scalarConvolution (besselKernel d) z x‖) +
        ∑ a : Fin d, ∫ x, ‖scalarConvolution (besselPartial d a) (g a) x‖ := by
      rw [integral_add
        (integrable_scalarConvolution (integrable_besselKernel d) (scalarTest_integrable z)).norm
        (integrable_finsetSum _ (fun a _ => (hi a).norm)),
        integral_finsetSum _ (fun a _ => (hi a).norm)]
    _ ≤ (∫ x, ‖z x‖) + ∑ a : Fin d,
        (Real.exp 1 * Real.sqrt Real.pi) * ∫ x, ‖g a x‖ := by
      apply add_le_add
      · simpa only [integral_norm_besselKernel, one_mul] using
          integral_norm_scalarConvolution_le (integrable_besselKernel d) (scalarTest_integrable z)
      · apply Finset.sum_le_sum
        intro a _
        exact (integral_norm_scalarConvolution_le (integrable_besselPartial a)
          (scalarTest_integrable (g a))).trans
          (mul_le_mul_of_nonneg_right (integral_norm_besselPartial_le a)
            (integral_nonneg (fun _ => norm_nonneg _)))
    _ = _ := by rw [Finset.mul_sum]

/--
dilated profile, defined for every real number (√ is zero on negative numbers). Source: DPR p. 9
(context), heat-kernel representation.
-/
def heatScaledProfile (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) : ℝ :=
  ∫ z, heatKernel d 1 z * u (x - Real.sqrt t • z)

/--
continuity of the dilated profile by dominated convergence. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem continuous_heatScaledProfile (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    Continuous (heatScaledProfile u x) := by
  have hu : Continuous (fun y : EuclideanSpace ℝ (Fin d) => u y) := u.continuous
  set N := ‖(u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ with hN
  have hb (y : EuclideanSpace ℝ (Fin d)) : ‖u y‖ ≤ N :=
    (u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm y
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin d) => heatKernel d 1 z * u (x - Real.sqrt t • z)) volume := by
    have hc : Continuous (fun z : EuclideanSpace ℝ (Fin d) => u (x - Real.sqrt t • z)) :=
      hu.comp (by fun_prop : Continuous fun z : EuclideanSpace ℝ (Fin d) => x - Real.sqrt t • z)
    exact (integrable_heatKernel d 1).aestronglyMeasurable.mul hc.aestronglyMeasurable
  have hdom (t : ℝ) : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ‖heatKernel d 1 z * u (x - Real.sqrt t • z)‖ ≤ heatKernel d 1 z * N :=
    ae_of_all _ (fun z => by
      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg d 1 z)]
      exact mul_le_mul_of_nonneg_left (hb _) (heatKernel_nonneg d 1 z))
  have hcont : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      Continuous (fun t : ℝ => heatKernel d 1 z * u (x - Real.sqrt t • z)) :=
    ae_of_all _ (fun z => continuous_const.mul
      (hu.comp (continuous_const.sub (Real.continuous_sqrt.smul continuous_const))))
  exact continuous_of_dominated (F := fun t z => heatKernel d 1 z * u (x - Real.sqrt t • z))
    hmeas hdom ((integrable_heatKernel d 1).mul_const N) hcont

/-- value of the profile at time zero. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem heatScaledProfile_zero (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    heatScaledProfile u x 0 = u x := by
  simp only [heatScaledProfile, Real.sqrt_zero, zero_smul, sub_zero]
  rw [integral_mul_const, integral_heatKernel d one_pos, one_mul]

/--
The trajectory equals e^{-t} times the profile on [0, ∞). Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem heatTrajectory_eq_scaled (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d))
    {t : ℝ} (ht : 0 ≤ t) :
    heatTrajectory u x t = Real.exp (-t) * heatScaledProfile u x t := by
  rcases ht.eq_or_lt with h0 | hp
  · subst h0
    simp [heatTrajectory, heatScaledProfile_zero]
  · simp only [heatTrajectory, if_neg hp.ne', heatScaledProfile]
    rw [heatConvolution_eq_scaled hp]

/--
First field of `HeatEvolution`, proved in every dimension. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem heatTrajectory_continuousWithinAt_zero (u : ScalarCurrentTest d)
    (x : EuclideanSpace ℝ (Fin d)) :
    ContinuousWithinAt (heatTrajectory u x) (Ici 0) 0 := by
  have hc : Continuous (fun t => Real.exp (-t) * heatScaledProfile u x t) :=
    (Real.continuous_exp.comp continuous_neg).mul (continuous_heatScaledProfile u x)
  exact hc.continuousWithinAt.congr (fun t ht => heatTrajectory_eq_scaled u x ht)
    (heatTrajectory_eq_scaled u x le_rfl)

/--
The reflected dilated test z ↦ φ(x − c z), c ≠ 0. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def affineReflectTest (φ : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (hc : c ≠ 0) : ScalarCurrentTest d where
  toFun z := φ (x - c • z)
  contDiff' := φ.contDiff.comp (contDiff_const.sub (contDiff_const_smul c))
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph
    ((Homeomorph.smulOfNeZero c hc).trans (Homeomorph.subLeft x))
  tsupport_subset' := subset_univ _

/--
evaluation of the reflected dilated test. Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem affineReflectTest_apply (φ : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (hc : c ≠ 0) (z : EuclideanSpace ℝ (Fin d)) :
    affineReflectTest φ x c hc z = φ (x - c • z) := rfl

/--
derivative of the reflected dilated test. Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem affineReflectTest_fderiv (φ : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (hc : c ≠ 0) (z v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (affineReflectTest φ x c hc) z v = -(c * fderiv ℝ φ (x - c • z) v) := by
  have hg : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => x - c • y)
      (-(c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))) z :=
    ((hasFDerivAt_id z).const_smul c).const_sub x
  have h := (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp z hg
  change fderiv ℝ ((φ : EuclideanSpace ℝ (Fin d) → ℝ) ∘ fun y => x - c • y) z v = _
  rw [h.fderiv]
  simp [smul_eq_mul]

/--
coordinate derivative of the reflected dilated test. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem cutoffPartialTest_affineReflectTest (φ : ScalarCurrentTest d)
    (x : EuclideanSpace ℝ (Fin d)) (c : ℝ) (hc : c ≠ 0) (a : Fin d) (z : EuclideanSpace ℝ (Fin d)) :
    cutoffPartialTest (affineReflectTest φ x c hc) a z =
      -(c * cutoffPartialTest φ a (x - c • z)) := by
  rw [cutoffPartialTest_apply, affineReflectTest_fderiv, cutoffPartialTest_apply]

/--
a continuous linear form in Euclidean coordinates. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem clm_apply_eq_sum_coord (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (z : EuclideanSpace ℝ (Fin d)) :
    L z = ∑ a : Fin d, z a * L (EuclideanSpace.single a 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.sum_repr z]
  simp [map_sum, map_smul, smul_eq_mul]

/--
pointwise evaluation of the test Laplacian. Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem scalarTestLaplacian_apply (u : ScalarCurrentTest d) (w : EuclideanSpace ℝ (Fin d)) :
    scalarTestLaplacian u w = ∑ a : Fin d, cutoffPartialTest (cutoffPartialTest u a) a w := by
  simp only [scalarTestLaplacian, ← FunLike.coeAddMonoidHom_apply, map_sum, Finset.sum_apply]

/--
differentiated integrand of the dilated profile. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def heatScaledDeriv (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (Real.sqrt s)⁻¹ * ∑ a : Fin d, heatDirectional d 1 (EuclideanSpace.single a 1) z *
    cutoffPartialTest u a (x - Real.sqrt s • z)

/--
pointwise time derivative of the integrand, s > 0. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem hasDerivAt_heatScaled_integrand (u : ScalarCurrentTest d) (x z : EuclideanSpace ℝ (Fin d))
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r => heatKernel d 1 z * u (x - Real.sqrt r • z))
      (heatScaledDeriv u x s z) s := by
  have hq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have h1 : HasDerivAt (fun r => Real.sqrt r • z) ((1 / (2 * Real.sqrt s)) • z) s :=
    (Real.hasDerivAt_sqrt hs.ne').smul_const z
  have h2 : HasDerivAt (fun r => x - Real.sqrt r • z) (-((1 / (2 * Real.sqrt s)) • z)) s :=
    h1.const_sub x
  have h3 := ((u.contDiff.differentiable (by simp)).differentiableAt
    (x := x - Real.sqrt s • z)).hasFDerivAt.comp_hasDerivAt s h2
  have h4 := h3.const_mul (heatKernel d 1 z)
  apply h4.congr_deriv
  rw [map_neg, map_smul, clm_apply_eq_sum_coord _ z, smul_eq_mul]
  simp only [heatScaledDeriv, heatDirectional, EuclideanSpace.inner_single_left, map_one,
    one_mul, cutoffPartialTest_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  field_simp

/--
The differentiated integrand is spatially integrable. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem integrable_heatScaledDeriv (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d))
    {s : ℝ} (hs : 0 < s) : Integrable (heatScaledDeriv u x s) := by
  have hq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  unfold heatScaledDeriv
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro a _
  exact integrable_mul_scalarTest (integrable_heatDirectional one_pos _)
    (affineReflectTest (cutoffPartialTest u a) x (Real.sqrt s) hq)

/-- uniform majorant for s > t/2. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem norm_heatScaledDeriv_le (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d))
    {t s : ℝ} (ht : 0 < t) (hs : t / 2 < s) (z : EuclideanSpace ℝ (Fin d)) :
    ‖heatScaledDeriv u x s z‖ ≤ (Real.sqrt (t / 2))⁻¹ * ∑ a : Fin d,
      ‖heatDirectional d 1 (EuclideanSpace.single a 1) z‖ *
        ‖(cutoffPartialTest u a : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ := by
  have ht2 : 0 < t / 2 := by positivity
  have hq : 0 < Real.sqrt (t / 2) := Real.sqrt_pos.2 ht2
  have hinv : (Real.sqrt s)⁻¹ ≤ (Real.sqrt (t / 2))⁻¹ :=
    inv_anti₀ hq (Real.sqrt_le_sqrt hs.le)
  unfold heatScaledDeriv
  rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg s))]
  apply mul_le_mul hinv _ (norm_nonneg _) (inv_nonneg.2 hq.le)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((cutoffPartialTest u a : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm _)
    (norm_nonneg _)

/--
differentiation of the dilated profile under the integral sign. Source: DPR p. 9 (context),
heat-kernel representation.
-/
theorem hasDerivAt_heatScaledProfile (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d))
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (heatScaledProfile u x) (∫ z, heatScaledDeriv u x t z) t := by
  have hu : Continuous (fun y : EuclideanSpace ℝ (Fin d) => u y) := u.continuous
  have hmeas (s : ℝ) : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin d) => heatKernel d 1 z * u (x - Real.sqrt s • z)) volume := by
    have hc : Continuous (fun z : EuclideanSpace ℝ (Fin d) => u (x - Real.sqrt s • z)) :=
      hu.comp (by fun_prop : Continuous fun z : EuclideanSpace ℝ (Fin d) => x - Real.sqrt s • z)
    exact (integrable_heatKernel d 1).aestronglyMeasurable.mul hc.aestronglyMeasurable
  have hq : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hint : Integrable
      (fun z : EuclideanSpace ℝ (Fin d) => heatKernel d 1 z * u (x - Real.sqrt t • z)) :=
    integrable_mul_scalarTest (integrable_heatKernel d 1) (affineReflectTest u x (Real.sqrt t) hq)
  have hbound : Integrable (fun z : EuclideanSpace ℝ (Fin d) => (Real.sqrt (t / 2))⁻¹ *
      ∑ a : Fin d, ‖heatDirectional d 1 (EuclideanSpace.single a 1) z‖ *
        ‖(cutoffPartialTest u a : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro a _
    exact (integrable_heatDirectional one_pos _).norm.mul_const _
  have hnhds : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s z => heatKernel d 1 z * u (x - Real.sqrt s • z))
    (F' := fun s z => heatScaledDeriv u x s z) hnhds
    (Filter.Eventually.of_forall hmeas) hint
    (integrable_heatScaledDeriv u x ht).aestronglyMeasurable
    (ae_of_all _ (fun z s hs => norm_heatScaledDeriv_le u x ht hs z)) hbound
    (ae_of_all _ (fun z s hs => hasDerivAt_heatScaled_integrand u x z
      (lt_trans (by positivity) (mem_Ioi.1 hs))))
  exact h.2

/--
integration by parts at time 1; the profile derivative pairs H_1 with Δu. Source: DPR p. 9
(context), heat-kernel representation.
-/
theorem integral_heatScaledDeriv (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d))
    {t : ℝ} (ht : 0 < t) :
    (∫ z, heatScaledDeriv u x t z) =
      ∫ z, heatKernel d 1 z * scalarTestLaplacian u (x - Real.sqrt t • z) := by
  have hq : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hIBP (a : Fin d) :
      (∫ z, heatDirectional d 1 (EuclideanSpace.single a 1) z *
        cutoffPartialTest u a (x - Real.sqrt t • z)) =
      Real.sqrt t * ∫ z, heatKernel d 1 z *
        cutoffPartialTest (cutoffPartialTest u a) a (x - Real.sqrt t • z) := by
    have h := heatKernel_integration_by_parts one_pos a
      (affineReflectTest (cutoffPartialTest u a) x (Real.sqrt t) hq)
    simp only [cutoffPartialTest_affineReflectTest, affineReflectTest_apply, mul_neg,
      integral_neg, neg_inj] at h
    rw [← h, ← integral_const_mul]
    congr 1
    ext z
    ring
  have hiD (a : Fin d) : Integrable (fun z => heatDirectional d 1 (EuclideanSpace.single a 1) z *
      cutoffPartialTest u a (x - Real.sqrt t • z)) :=
    integrable_mul_scalarTest (integrable_heatDirectional one_pos _)
      (affineReflectTest (cutoffPartialTest u a) x (Real.sqrt t) hq)
  have hiK (a : Fin d) : Integrable (fun z => heatKernel d 1 z *
      cutoffPartialTest (cutoffPartialTest u a) a (x - Real.sqrt t • z)) :=
    integrable_mul_scalarTest (integrable_heatKernel d 1)
      (affineReflectTest (cutoffPartialTest (cutoffPartialTest u a) a) x (Real.sqrt t) hq)
  unfold heatScaledDeriv
  rw [integral_const_mul, integral_finsetSum _ (fun a _ => hiD a)]
  simp only [hIBP, ← Finset.mul_sum]
  rw [← mul_assoc, inv_mul_cancel₀ hq, one_mul, ← integral_finsetSum _ (fun a _ => hiK a)]
  congr 1
  ext z
  rw [scalarTestLaplacian_apply, Finset.mul_sum]

/--
second field of `HeatEvolution`, proved in every dimension. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem heatTrajectory_hasDerivAt (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d))
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (heatTrajectory u x)
      (-(Real.exp (-t) * scalarConvolution (heatKernel d t)
        (u - scalarTestLaplacian u : ScalarCurrentTest d) x)) t := by
  have hq : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have he : heatTrajectory u x =ᶠ[𝓝 t] (fun s => Real.exp (-s) * heatScaledProfile u x s) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact heatTrajectory_eq_scaled u x hs.le
  have hP := hasDerivAt_heatScaledProfile u x ht
  have hprod := ((hasDerivAt_id t).neg.exp).mul hP
  apply (hprod.congr_deriv _).congr_of_eventuallyEq he
  rw [integral_heatScaledDeriv u x ht, heatConvolution_eq_scaled ht, heatScaledProfile]
  have hi1 : Integrable (fun z => heatKernel d 1 z * u (x - Real.sqrt t • z)) :=
    integrable_mul_scalarTest (integrable_heatKernel d 1)
      (affineReflectTest u x (Real.sqrt t) hq)
  have hi2 : Integrable (fun z => heatKernel d 1 z *
      scalarTestLaplacian u (x - Real.sqrt t • z)) :=
    integrable_mul_scalarTest (integrable_heatKernel d 1)
      (affineReflectTest (scalarTestLaplacian u) x (Real.sqrt t) hq)
  have hsub : (∫ z, heatKernel d 1 z *
      (u - scalarTestLaplacian u : ScalarCurrentTest d) (x - Real.sqrt t • z)) =
      (∫ z, heatKernel d 1 z * u (x - Real.sqrt t • z)) -
        ∫ z, heatKernel d 1 z * scalarTestLaplacian u (x - Real.sqrt t • z) := by
    rw [← integral_sub hi1 hi2]
    congr 1
    ext z
    change heatKernel d 1 z * (u (x - Real.sqrt t • z) -
      scalarTestLaplacian u (x - Real.sqrt t • z)) = _
    ring
  rw [hsub]
  simp only [Pi.neg_apply, id_eq]
  ring

/--
The `HeatEvolution` interface is realized in every dimension. Source: DPR p. 9 (context),
heat-kernel representation.
-/
theorem heatEvolution_holds (d : ℕ) : HeatEvolution d where
  continuous_zero u x := heatTrajectory_continuousWithinAt_zero u x
  derivative u x t ht := heatTrajectory_hasDerivAt u x t ht

/--
The resolvent identity B * (u − Δu) = u at every point, in every dimension. Source: DPR p. 9
(context), heat-kernel representation.
-/
theorem besselResolves_holds (d : ℕ) : BesselResolves d :=
  besselResolves_of_heatEvolution (heatEvolution_holds d)

end GeometricMeasure
