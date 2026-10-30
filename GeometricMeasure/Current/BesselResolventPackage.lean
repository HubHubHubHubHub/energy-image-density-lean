import GeometricMeasure.Current.BesselResolvent

/-!
# Bessel Resolvent Package

## Main results
Connection to the tests and gradient equation of the localized mollification data. The resolvent
decomposition holds without a resolvent assumption, with zero mass of t and a uniform bound on h.
Smallness of the components provides no uniform bound on their derivatives.

Bibliographic context: De Philippis–Rindler, p. 9, (2.9)–(2.10). The heat-kernel argument is a
specialization. The Annals page reference, pp. 1027–1028, is unverified against that edition.
-/


noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped Topology RealInnerProductSpace Convolution
namespace GeometricMeasure
variable {d : ℕ}

namespace MatrixPolarBlowupData
variable {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))}
variable {x : EuclideanSpace ℝ (Fin d)}

/--
z_n as a smooth compactly supported test, under the same hypotheses. Source: DPR p. 9 (context),
heat-kernel representation.
-/
def mollifiedPositiveTest (b : MatrixPolarBlowupData M D x) (n : ℕ) : ScalarCurrentTest d where
  toFun := b.mollifiedPositive n
  contDiff' := (b.mollified_smooth n).1
  hasCompactSupport' := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 2).of_isClosed_subset
    isClosed_closure (b.mollified_common_support n).1
  tsupport_subset' := subset_univ _

/--
g_n,a as a smooth compactly supported test. Source: DPR p. 9 (context), heat-kernel representation.
-/
def mollifiedRemainderTest (b : MatrixPolarBlowupData M D x) (n : ℕ) (a : Fin d) :
    ScalarCurrentTest d where
  toFun := b.mollifiedRemainder n a
  contDiff' := ((b.mollified_smooth n).2 a).2
  hasCompactSupport' := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 2).of_isClosed_subset
    isClosed_closure ((b.mollified_common_support n).2 a).2
  tsupport_subset' := subset_univ _

/--
L¹ norm at most 1 of the resolvent input z_n. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem mollifiedPositiveTest_L1_le_one (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    (∫ y, ‖b.mollifiedPositiveTest n y‖) ≤ 1 := by
  change (∫ y, ‖b.mollifiedPositive n y‖) ≤ 1
  simp only [Real.norm_of_nonneg (b.mollifiedPositive_nonneg n _)]
  rw [b.mollifiedPositive_mass]
  exact b.localizedPositive_mass_le_one n

/--
uniform bound on the regular term of the localized mollifications. Source: DPR p. 9 (context),
heat-kernel representation.
-/
theorem resolventRegular_mollified_uniform (b : MatrixPolarBlowupData M D x) :
    ∃ C : ℝ, ∀ n,
      (∫ y, ‖resolventRegular (b.mollifiedPositiveTest n) (b.mollifiedRemainderTest n) y‖) ≤ C := by
  choose C hC using b.mollifiedRemainder_L1_bounded
  refine ⟨1 + (Real.exp 1 * Real.sqrt Real.pi) * ∑ a : Fin d, C a, fun n => ?_⟩
  apply (integral_norm_resolventRegular_le _ _).trans
  apply add_le_add (b.mollifiedPositiveTest_L1_le_one n)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun a _ => hC a n)

end MatrixPolarBlowupData

/--
trace of the derivative written in the Euclidean basis. Source: DPR p. 9 (context), heat-kernel
representation.
-/
theorem smoothDivergence_eq_coordinate_sum
    (v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    smoothDivergence v x = ∑ a : Fin d,
      (fderiv ℝ v x (EuclideanSpace.single a (1 : ℝ))) a := by
  change LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d)) (fderiv ℝ v x).toLinearMap = _
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]
  simp [Matrix.trace, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply]

namespace MatrixPolarBlowupData
variable {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))}
variable {x : EuclideanSpace ℝ (Fin d)}

/--
component f_n,ab as a smooth compactly supported test. Source: DPR p. 9 (context), heat-kernel
representation.
-/
def mollifiedDefectTest (b : MatrixPolarBlowupData M D x) (n : ℕ) (a j : Fin d) :
    ScalarCurrentTest d where
  toFun y := b.mollifiedDefectRow n a y j
  contDiff' := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j).contDiff.comp
    ((b.mollified_smooth n).2 a).1
  hasCompactSupport' := by
    apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 2).of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    apply ((b.mollified_common_support n).2 a).1
    apply subset_closure
    intro hz
    apply hy
    simp [hz]
  tsupport_subset' := subset_univ _

/--
L¹ smallness of each component, inherited from the localized row norm. Source: DPR p. 9 (context),
heat-kernel representation.
-/
theorem mollifiedDefectTest_L1_tendsto (b : MatrixPolarBlowupData M D x) (a j : Fin d) :
    Tendsto (fun n => ∫ y, ‖b.mollifiedDefectTest n a j y‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg (fun y => norm_nonneg _)) _
    (b.mollifiedDefectRow_L1_tendsto a)
  intro n
  have hi : Integrable (b.mollifiedDefectRow n a) :=
    (((b.mollified_smooth n).2 a).1.continuous).integrable_of_hasCompactSupport
      ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 2).of_isClosed_subset
        isClosed_closure ((b.mollified_common_support n).2 a).1)
  apply integral_mono (scalarTest_integrable (b.mollifiedDefectTest n a j)).norm hi.norm
  intro y
  exact PiLp.norm_apply_le (b.mollifiedDefectRow n a y) j

/-- derivative of the component f_n,ab. Source: DPR p. 9 (context), heat-kernel representation. -/
theorem mollifiedDefectTest_partial (b : MatrixPolarBlowupData M D x) (n : ℕ)
    (a j k : Fin d) (y : EuclideanSpace ℝ (Fin d)) :
    cutoffPartialTest (b.mollifiedDefectTest n a j) k y =
      (fderiv ℝ (b.mollifiedDefectRow n a) y (EuclideanSpace.single k (1 : ℝ))) j := by
  rw [cutoffPartialTest_apply]
  have h := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j).hasFDerivAt.comp y
    ((((b.mollified_smooth n).2 a).1.differentiable (by simp)).differentiableAt.hasFDerivAt)
  change fderiv ℝ ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j) ∘
    b.mollifiedDefectRow n a) y (EuclideanSpace.single k 1) = _
  rw [h.fderiv]
  rfl

/--
The mollified pointwise equation provides exactly the smooth gradient equation for the resolvent.
Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem mollified_smoothGradientEquation (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    SmoothGradientEquation (b.mollifiedPositiveTest n) (b.mollifiedDefectTest n)
      (b.mollifiedRemainderTest n) := by
  intro a
  ext y
  rw [cutoffPartialTest_apply]
  change fderiv ℝ (b.mollifiedPositive n) y (EuclideanSpace.single a 1) = _
  rw [b.mollified_gradient_equation, smoothDivergence_eq_coordinate_sum]
  simp only [add_apply, ← FunLike.coeAddMonoidHom_apply, map_sum, Finset.sum_apply]
  simp only [FunLike.coeAddMonoidHom_apply, mollifiedDefectTest_partial]
  rfl

/--
identity z_n=t_n+h_n on the localized mollification data, under the explicit resolvent property.
Source: DPR p. 9 (context), heat-kernel representation.
-/
theorem mollified_resolvent_L6 (b : MatrixPolarBlowupData M D x) (hres : BesselResolves d) (n : ℕ) :
    b.mollifiedPositive n = resolventError (b.mollifiedDefectTest n) +
      resolventRegular (b.mollifiedPositiveTest n) (b.mollifiedRemainderTest n) ∧
    Integrable (resolventError (b.mollifiedDefectTest n)) ∧
    Integrable (resolventRegular (b.mollifiedPositiveTest n) (b.mollifiedRemainderTest n)) ∧
    (∫ y, resolventError (b.mollifiedDefectTest n) y) = 0 :=
  resolvent_L6 hres _ _ _ (b.mollified_smoothGradientEquation n)

end MatrixPolarBlowupData

/--
The resolvent decomposition on the localized mollification data. Source: DPR p. 9 (context),
heat-kernel representation.
-/
theorem MatrixPolarBlowupData.mollified_resolvent_L6_uncond
    {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
    {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}
    (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    b.mollifiedPositive n = resolventError (b.mollifiedDefectTest n) +
      resolventRegular (b.mollifiedPositiveTest n) (b.mollifiedRemainderTest n) ∧
    Integrable (resolventError (b.mollifiedDefectTest n)) ∧
    Integrable (resolventRegular (b.mollifiedPositiveTest n) (b.mollifiedRemainderTest n)) ∧
    (∫ y, resolventError (b.mollifiedDefectTest n) y) = 0 :=
  b.mollified_resolvent_L6 (besselResolves_holds d) n

end GeometricMeasure
