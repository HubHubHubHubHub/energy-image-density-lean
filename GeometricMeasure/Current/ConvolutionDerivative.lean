import GeometricMeasure.VectorMeasure.MeasureConvolution
import GeometricMeasure.Current.WeakConvergence
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.LinearAlgebra.Trace

/-!
# Convolution Derivative

## Main results
Differentiation under the integral and commutation of the global equation. Source: DPR arXiv, pp.
8–9, (2.5) and (2.9). Integrable domination replaces any invariance assumption on the source
measure. Divergence is the trace of the derivative; the reflected translated kernel provides the
minus sign needed for commutation.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology Convolution
namespace GeometricMeasure
variable {d m : ℕ}

/--
DPR arXiv, p. 8 (2.5). Differentiation under a finite-variation density integral; the base measure
need not be Haar.
-/
theorem scalarDensityConvolution_hasFDerivAt
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (p : EuclideanSpace ℝ (Fin d) → ℝ) (hp : Integrable p μ)
    (ρ : ScalarCurrentTest d) (x₀ : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun x => ∫ y, ρ (x - y) * p y ∂μ)
      (∫ y, p y • fderiv ℝ ρ (x₀ - y) ∂μ) x₀ := by
  let C := ‖(currentTestDerivative ρ : BoundedCovectorField d d)‖
  have hD : Continuous (fderiv ℝ ρ) := ρ.contDiff.continuous_fderiv (by simp)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun x y => p y • fderiv ℝ ρ (x - y))
    (bound := fun y => ‖p y‖ * C) (s := univ) (Filter.univ_mem)
  · filter_upwards with x
    exact (ρ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      hp.aestronglyMeasurable
  · exact hp.bdd_mul (f := fun y => ρ (x₀ - y))
      (ρ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall (fun y => (ρ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm _))
  · exact hp.aestronglyMeasurable.smul
      (hD.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards with y
    intro x _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      ((currentTestDerivative ρ : BoundedCovectorField d d).norm_coe_le_norm (x - y)) (norm_nonneg _)
  · exact hp.norm.mul_const C
  · filter_upwards with y
    intro x _
    have h := ((ρ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const y)).mul_const (p y)
    simpa only [ContinuousLinearMap.comp_id, Function.comp_apply, id_eq, mul_comm] using h

/--
DPR arXiv, p. 8 (2.5). Differentiation of an integrable vector density against an arbitrary
measure by integrable domination.
-/
theorem vectorDensityConvolution_hasFDerivAt {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (p : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m)) (hp : Integrable p μ)
    (ρ : ScalarCurrentTest d) (x₀ : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun x => ∫ y, ρ (x - y) • p y ∂μ)
      (∫ y, (fderiv ℝ ρ (x₀ - y)).smulRight (p y) ∂μ) x₀ := by
  let C := ‖(currentTestDerivative ρ : BoundedCovectorField d d)‖
  have hD : Continuous (fderiv ℝ ρ) := ρ.contDiff.continuous_fderiv (by simp)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun x y => (fderiv ℝ ρ (x - y)).smulRight (p y))
    (bound := fun y => C * ‖p y‖) (s := univ) (Filter.univ_mem)
  · filter_upwards with x
    exact (ρ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.smul
      hp.aestronglyMeasurable
  · exact hp.bdd_smul (φ := fun y => ρ (x₀ - y))
      ‖(ρ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖
      (ρ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall (fun y => (ρ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm _))
  · exact (ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m))).aestronglyMeasurable_comp₂
      (hD.comp (continuous_const.sub continuous_id)).aestronglyMeasurable hp.aestronglyMeasurable
  · filter_upwards with y
    intro x _
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_right
      ((currentTestDerivative ρ : BoundedCovectorField d d).norm_coe_le_norm (x - y)) (norm_nonneg _)
  · exact hp.norm.const_mul C
  · filter_upwards with y
    intro x _
    have h := ((ρ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const y)).smul_const (p y)
    simpa only [ContinuousLinearMap.comp_id, Function.comp_apply, id_eq] using h

/--
DPR arXiv, p. 8 (2.5). Actual derivative of vector convolution, given by the integral of Dρ ⊗ p.
-/
theorem measureConvolution_hasFDerivAt {m : ℕ}
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ρ : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (measureConvolution N ρ)
      (∫ y, (fderiv ℝ ρ (x - y)).smulRight (polarDensity N y) ∂N.variation) x :=
  vectorDensityConvolution_hasFDerivAt N.variation _ (integrable_polarDensity N) ρ x

/--
DPR arXiv, p. 8 (2.5). Reflected translated kernel y ↦ ρ(x−y), viewed as a global smooth compactly
supported scalar test.
-/
def translatedKernelTest (ρ : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) : ScalarCurrentTest d where
  toFun := fun y => ρ (x - y)
  contDiff' := ρ.contDiff.comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := ρ.hasCompactSupport.comp_homeomorph (Homeomorph.subLeft x)
  tsupport_subset' := subset_univ _

/--
DPR arXiv, p. 8 (2.5). The derivative of the reflected translated kernel carries a minus sign:
−Dρ(x−y).
-/
theorem translatedKernelTest_fderiv (ρ : ScalarCurrentTest d)
    (x y v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (translatedKernelTest ρ x) y v = - fderiv ℝ ρ (x - y) v := by
  have h := (ρ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  have hd := h.fderiv
  change fderiv ℝ (fun z => ρ (x - z)) y v = _
  simpa [Function.comp_def] using congrArg (fun L => L v) hd

/--
DPR arXiv, p. 8 (2.5). Trace on derivatives, continuous because the domain is finite dimensional.
-/
def derivativeTrace (d : ℕ) :
    (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ :=
  ({ toFun := fun A => LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d)) A.toLinearMap
     map_add' := by intro A B; simp
     map_smul' := by intro c A; simp } :
    (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ).toContinuousLinearMap

/--
DPR arXiv, p. 8 (2.5). Usual divergence of a Euclidean field, defined as the trace of its Fréchet
derivative.
-/
def smoothDivergence (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ := derivativeTrace d (fderiv ℝ f x)

/-- DPR arXiv, p. 8 (2.5). The trace of the rank-one operator L ⊗ v is L(v). -/
theorem derivativeTrace_smulRight (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : derivativeTrace d (L.smulRight v) = L v :=
  LinearMap.trace_smulRight L.toLinearMap v

/--
DPR arXiv, p. 8 (2.5). Integrability of the kernel derivative tensored with the polar against
Euclidean variation.
-/
theorem convolutionDerivative_integrable
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (ρ : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun y => (fderiv ℝ ρ (x - y)).smulRight (polarDensity N y)) N.variation := by
  let C := ‖(currentTestDerivative ρ : BoundedCovectorField d d)‖
  apply ((integrable_polarDensity N).norm.const_mul C).mono'
  · exact (ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d))).aestronglyMeasurable_comp₂
      ((ρ.contDiff.continuous_fderiv (by simp)).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (integrable_polarDensity N).aestronglyMeasurable
  · filter_upwards with y
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_right
      ((currentTestDerivative ρ : BoundedCovectorField d d).norm_coe_le_norm _) (norm_nonneg _)

/--
DPR arXiv, p. 8 (2.5). The divergence of convolution is the integral of Dρ(x−y) applied to the
polar.
-/
theorem smoothDivergence_measureConvolution
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (ρ : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    smoothDivergence (measureConvolution N ρ) x =
      ∫ y, fderiv ℝ ρ (x - y) (polarDensity N y) ∂N.variation := by
  rw [smoothDivergence, (measureConvolution_hasFDerivAt N ρ x).fderiv,
    ← (derivativeTrace d).integral_comp_comm (convolutionDerivative_integrable N ρ x)]
  apply integral_congr_ae
  filter_upwards with y
  exact derivativeTrace_smulRight _ _

/--
DPR arXiv, p. 8 (2.5). The directional derivative of positive-measure convolution is obtained under
the integral.
-/
theorem positiveConvolution_fderiv
    (ν : FiniteMeasure (EuclideanSpace ℝ (Fin d))) (ρ : ScalarCurrentTest d)
    (x v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (positiveConvolution ν ρ) x v =
      ∫ y, fderiv ℝ ρ (x - y) v ∂(ν : Measure (EuclideanSpace ℝ (Fin d))) := by
  have h := scalarDensityConvolution_hasFDerivAt (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (fun _ => 1) (integrable_const _) ρ x
  simp only [mul_one, one_smul] at h
  have heq : positiveConvolution ν ρ = fun x => ∫ y, ρ (x - y) ∂(ν : Measure (EuclideanSpace ℝ (Fin d))) := by
    funext z
    exact positiveConvolution_apply ν ρ z
  rw [heq, h.fderiv, ContinuousLinearMap.integral_apply]
  exact ((ρ.contDiff.continuous_fderiv (by simp)).comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
    (ρ.hasCompactSupport.fderiv ℝ |>.comp_homeomorph (Homeomorph.subLeft x))

/--
DPR arXiv, p. 8 (2.5). Signed convolution at x is exactly the current evaluated on the reflected
translated kernel.
-/
theorem signedConvolution_translated_test
    (q : SignedMeasure (EuclideanSpace ℝ (Fin d))) (ρ : ScalarCurrentTest d)
    (x : EuclideanSpace ℝ (Fin d)) :
    signedTestCurrent q (translatedKernelTest ρ x) = signedConvolution q ρ x := by
  rw [signedTestCurrent_apply]
  change (∫ y, ρ (x - y) ∂q.toJordanDecomposition.posPart) -
    (∫ y, ρ (x - y) ∂q.toJordanDecomposition.negPart) = _
  simp only [signedConvolution, Pi.sub_apply, positiveConvolution_apply]
  rfl

/--
DPR arXiv, p. 8 (2.5). Evaluation of the boundary on the reflected kernel, with the minus sign
explicit.
-/
theorem boundary_translatedKernel
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (ρ : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    oneCurrentBoundary (measureOneCurrent N) (translatedKernelTest ρ x) =
      -(∫ y, fderiv ℝ ρ (x - y) (polarDensity N y) ∂N.variation) := by
  rw [oneCurrentBoundary_apply, measureOneCurrent_apply]
  change (∫ y, fderiv ℝ (translatedKernelTest ρ x) y (polarDensity N y) ∂N.variation) = _
  simp only [translatedKernelTest_fderiv, integral_neg]

/--
DPR arXiv, p. 8 (2.5). Full pointwise commutation of the global gradient/divergence identity with a
smooth kernel.
-/
theorem convolved_gradient_equation
    (ν : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (F : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (G : SignedMeasure (EuclideanSpace ℝ (Fin d))) (a : Fin d)
    (heq : ∀ φ : ScalarCurrentTest d,
      oneCurrentBoundary (measureOneCurrent ((ν : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
        (fun _ => EuclideanSpace.single a (1 : ℝ)))) φ =
      oneCurrentBoundary (measureOneCurrent F) φ - signedTestCurrent G φ)
    (ρ : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (positiveConvolution ν ρ) x (EuclideanSpace.single a (1 : ℝ)) =
      smoothDivergence (measureConvolution F ρ) x + signedConvolution G ρ x := by
  have h := heq (translatedKernelTest ρ x)
  rw [boundary_translatedKernel F, signedConvolution_translated_test,
    oneCurrentBoundary_apply, ← vectorMeasurePairing_currentTest,
    vectorMeasurePairing_withDensityᵥ _ (integrable_const _)] at h
  change (∫ y, fderiv ℝ (translatedKernelTest ρ x) y (EuclideanSpace.single a (1 : ℝ))
    ∂(ν : Measure (EuclideanSpace ℝ (Fin d)))) = _ at h
  simp only [translatedKernelTest_fderiv, integral_neg] at h
  rw [positiveConvolution_fderiv, smoothDivergence_measureConvolution]
  linarith

end GeometricMeasure
