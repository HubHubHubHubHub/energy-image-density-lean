import GeometricMeasure.VectorMeasure.Localization
import GeometricMeasure.Current.ConvolutionDerivative
import GeometricMeasure.Current.MollificationDiagonal
import GeometricMeasure.Current.MatrixBlowup

/-!
# Localization and mollification of matrix polar blow-ups

## Main results
Localization precedes convolution. The interior mass lies in B(0, 3/4), the localized support in
B̄(0, 13/16), and the common smoothed support in B̄(0, 2). A common index gives convergence of the
remainder and density against smooth tests, and weak convergence of positive finite measures.
Defects are represented by Euclidean rows.

References: De Philippis–Rindler, arXiv p. 9, (2.9), and p. 8, (2.5).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology Convolution
namespace GeometricMeasure
variable {d m : ℕ}

/-- DPR arXiv, p. 9 (2.9). Fixed interior cutoff; closed support is strictly inside radius 7/8. -/
def interiorCutoff (d : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) where
  rIn := 3 / 4
  rOut := 13 / 16
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/--
DPR arXiv, p. 9 (2.9). Explicit cutoff viewed as a global smooth compactly supported scalar test.
-/
def interiorCutoffTest (d : ℕ) : ScalarCurrentTest d where
  toFun := interiorCutoff d
  contDiff' := (interiorCutoff d).contDiff
  hasCompactSupport' := (interiorCutoff d).hasCompactSupport
  tsupport_subset' := subset_univ _

/-- DPR arXiv, p. 9 (2.9). The closed support of the cutoff lies strictly inside B(0,7/8). -/
theorem interiorCutoff_support :
    tsupport (interiorCutoff d) ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) (7 / 8) := by
  rw [(interiorCutoff d).tsupport_eq]
  exact closedBall_subset_ball (by norm_num [interiorCutoff])

/-- DPR arXiv, p. 9 (2.9). The cutoff equals exactly 1 on the closed ball of radius 3/4. -/
theorem interiorCutoff_one {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ closedBall 0 (3 / 4)) : interiorCutoff d y = 1 :=
  (interiorCutoff d).one_of_mem_closedBall hy

namespace MatrixPolarBlowupData
variable {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))}
variable {x : EuclideanSpace ℝ (Fin d)}

/--
DPR arXiv, p. 9 (2.9). Positive measure w_n = χν_n, constructed from the matrix polar blow-up data.
-/
def localizedPositive (b : MatrixPolarBlowupData M D x) (n : ℕ) :=
  localPositive (interiorCutoffTest d : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) (b.positive n)

/--
DPR arXiv, p. 9 (2.9). Localized limit measure w = χν, without a density assumption with respect to
volume.
-/
def localizedTangent (b : MatrixPolarBlowupData M D x) :=
  localPositive (interiorCutoffTest d : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) b.tangent

/--
DPR arXiv, p. 9 (2.9). Convergence of the localized measures in the actual FiniteMeasure topology.
-/
theorem localizedPositive_tendsto (b : MatrixPolarBlowupData M D x) :
    Tendsto b.localizedPositive atTop (𝓝 b.localizedTangent) :=
  localPositive_tendsto _ (interiorCutoff d).nonneg' _ _ b.positive_convergence

/--
DPR arXiv, p. 9 (2.9). The localized limit mass belongs to [2⁻ᵈ,1], thanks to the mass in B(0,3/4).
-/
theorem localizedTangent_mass_bounds (b : MatrixPolarBlowupData M D x) :
    ((2 : ℝ) ^ d)⁻¹ ≤ (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).real univ ∧
      (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).real univ ≤ 1 := by
  have heq : (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).real univ =
      ∫ y, interiorCutoff d y ∂(b.tangent : Measure (EuclideanSpace ℝ (Fin d))) := by
    have h := integral_localPositive
      (interiorCutoffTest d : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
      (interiorCutoff d).nonneg' b.tangent (fun _ => 1)
    simpa [localizedTangent, interiorCutoffTest] using h
  constructor
  · rw [heq]
    apply b.tangent_three_quarters_ge.trans
    apply (measureReal_mono ball_subset_closedBall).trans
    exact (interiorCutoff d).measure_closedBall_le_integral _
  · have h := localPositive_le
      (interiorCutoffTest d : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
      (fun _ => (interiorCutoff d).le_one) b.tangent univ
    have hm : (b.tangent : Measure (EuclideanSpace ℝ (Fin d))).real univ = 1 := by
      rw [measureReal_def, ← FiniteMeasure.ennreal_mass, b.tangent_mass_eq_one]
      simp
    exact (ENNReal.toReal_mono (measure_ne_top _ _) h).trans_eq hm

/--
DPR arXiv, p. 9 (2.9). The localized limit measure has strictly positive mass, even in dimension
zero.
-/
theorem localizedTangent_mass_pos (b : MatrixPolarBlowupData M D x) :
    0 < (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).real univ :=
  (inv_pos.mpr (pow_pos (by norm_num) d)).trans_le b.localizedTangent_mass_bounds.1

end MatrixPolarBlowupData


/--
DPR arXiv, p. 9 (2.9). The weight transfers from the measure to the covector field in the pairing.
-/
theorem localVector_pairing (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ω : BoundedCovectorField d m) :
    vectorMeasurePairing (localVector χ N) ω = vectorMeasurePairing N (χ • ω) := by
  rw [localVector, vectorMeasurePairing_withDensityᵥ _ (localVector_integrable χ N)]
  apply integral_congr_ae
  filter_upwards with y
  change ω y (χ y • polarDensity N y) = χ y • ω y (polarDensity N y)
  exact map_smul (ω y) (χ y) (polarDensity N y)

/--
DPR arXiv, p. 9 (2.9). Localization preserves weak convergence tested by bounded continuous covector
fields.
-/
theorem localVector_tendsto (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (Ns : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (h : VectorMeasureWeaklyTendsto Ns N) :
    VectorMeasureWeaklyTendsto (fun n => localVector χ (Ns n)) (localVector χ N) := by
  intro ω
  simp only [localVector_pairing]
  exact h (χ • ω)

/--
DPR arXiv, p. 9 (2.9). Global scalar test product, used to consume the interior local gradient
equation.
-/
def scalarTestMul (χ φ : ScalarCurrentTest d) : ScalarCurrentTest d where
  toFun := fun y => χ y * φ y
  contDiff' := χ.contDiff.mul φ.contDiff
  hasCompactSupport' := χ.hasCompactSupport.mul_right
  tsupport_subset' := subset_univ _

/--
DPR arXiv, p. 9 (2.9). The support of the product of tests is contained in that of the first factor.
-/
theorem scalarTestMul_support (χ φ : ScalarCurrentTest d) :
    tsupport (scalarTestMul χ φ) ⊆ tsupport χ := tsupport_mul_subset_left

/--
DPR arXiv, p. 9 (2.9). Pointwise Leibniz identity for the exact test used in the local gradient
equation.
-/
theorem scalarTestMul_fderiv (χ φ : ScalarCurrentTest d)
    (y v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (scalarTestMul χ φ) y v =
      χ y * fderiv ℝ φ y v + φ y * fderiv ℝ χ y v := by
  change fderiv ℝ ((χ : EuclideanSpace ℝ (Fin d) → ℝ) * (φ : EuclideanSpace ℝ (Fin d) → ℝ)) y v = _
  rw [fderiv_mul (χ.contDiff.differentiable (by simp)).differentiableAt
    (φ.contDiff.differentiable (by simp)).differentiableAt]
  rfl

/-- DPR arXiv, p. 9 (2.9). The product rule integrated against a genuinely vector-valued density. -/
theorem boundary_density_testMul
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (p : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hp : Integrable p μ)
    (χ φ : ScalarCurrentTest d) :
    oneCurrentBoundary (measureOneCurrent (μ.withDensityᵥ p)) (scalarTestMul χ φ) =
      (∫ y, χ y * fderiv ℝ φ y (p y) ∂μ) +
      ∫ y, φ y * fderiv ℝ χ y (p y) ∂μ := by
  rw [oneCurrentBoundary_apply, ← vectorMeasurePairing_currentTest,
    vectorMeasurePairing_withDensityᵥ μ hp]
  simp only [currentTestDerivative_apply]
  change (∫ y, fderiv ℝ (scalarTestMul χ φ) y (p y) ∂μ) = _
  simp only [scalarTestMul_fderiv]
  apply integral_add
  · exact (integrable_boundedCovector_apply μ hp
      (currentTestDerivative φ : BoundedCovectorField d d)).bdd_mul
      χ.continuous.aestronglyMeasurable
      (Eventually.of_forall (fun y => (χ : BoundedContinuousFunction _ ℝ).norm_coe_le_norm y))
  · exact (integrable_boundedCovector_apply μ hp
      (currentTestDerivative χ : BoundedCovectorField d d)).bdd_mul
      φ.continuous.aestronglyMeasurable
      (Eventually.of_forall (fun y => (φ : BoundedContinuousFunction _ ℝ).norm_coe_le_norm y))

/--
DPR arXiv, p. 9 (2.9). Integrated Leibniz rule for the boundary of a vector measure, via its polar.
-/
theorem boundary_testMul (N : VectorMeasure (EuclideanSpace ℝ (Fin d))
    (EuclideanSpace ℝ (Fin d))) (χ φ : ScalarCurrentTest d) :
    oneCurrentBoundary (measureOneCurrent N) (scalarTestMul χ φ) =
      (∫ y, χ y * fderiv ℝ φ y (polarDensity N y) ∂N.variation) +
      ∫ y, φ y * fderiv ℝ χ y (polarDensity N y) ∂N.variation := by
  conv_lhs => rw [← withDensityᵥ_polarDensity N]
  exact boundary_density_testMul N.variation _ (integrable_polarDensity N) χ φ

/--
DPR arXiv, p. 9 (2.9). Exact global test identity, including both derivative-of-cutoff terms and the
signed source. It uses only the local gradient equation on the support of χ.
-/
theorem localize_gradient_integral
    (ν : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (E : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (q : SignedMeasure (EuclideanSpace ℝ (Fin d))) (a : Fin d)
    (χ : ScalarCurrentTest d) (U : Set (EuclideanSpace ℝ (Fin d)))
    (hχ : tsupport χ ⊆ U)
    (heq : ∀ ψ : ScalarCurrentTest d, tsupport ψ ⊆ U →
      oneCurrentBoundary (measureOneCurrent ((ν : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
        (fun _ => EuclideanSpace.single a (1 : ℝ)))) ψ =
      oneCurrentBoundary (measureOneCurrent E) ψ - signedTestCurrent q ψ)
    (φ : ScalarCurrentTest d) :
    (∫ y, χ y * fderiv ℝ φ y (EuclideanSpace.single a (1 : ℝ)) ∂(ν : Measure (EuclideanSpace ℝ (Fin d)))) =
      (∫ y, χ y * fderiv ℝ φ y (polarDensity E y) ∂E.variation) -
      ((∫ y, φ y * fderiv ℝ χ y (EuclideanSpace.single a (1 : ℝ)) ∂(ν : Measure (EuclideanSpace ℝ (Fin d)))) -
        (∫ y, φ y * fderiv ℝ χ y (polarDensity E y) ∂E.variation) +
        signedTestCurrent q (scalarTestMul χ φ)) := by
  have h := heq (scalarTestMul χ φ) ((scalarTestMul_support χ φ).trans hχ)
  rw [boundary_density_testMul _ _ (integrable_const _) χ φ, boundary_testMul E χ φ] at h
  linarith

namespace MatrixPolarBlowupData
variable {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))}
variable {x : EuclideanSpace ℝ (Fin d)}

/--
DPR arXiv, p. 9 (2.9). The local gradient equation gives the global identity on every test, with no
support condition on φ.
-/
theorem localized_gradient_integral (b : MatrixPolarBlowupData M D x)
    (n : ℕ) (a : Fin d) (φ : ScalarCurrentTest d) :
    (∫ y, interiorCutoff d y * fderiv ℝ φ y (EuclideanSpace.single a (1 : ℝ))
      ∂(b.positive n : Measure (EuclideanSpace ℝ (Fin d)))) =
      (∫ y, interiorCutoff d y * fderiv ℝ φ y (polarDensity (rowMeasure (b.inverseDefect n) a) y)
        ∂(rowMeasure (b.inverseDefect n) a).variation) -
      ((∫ y, φ y * fderiv ℝ (interiorCutoffTest d) y (EuclideanSpace.single a (1 : ℝ))
        ∂(b.positive n : Measure (EuclideanSpace ℝ (Fin d)))) -
        (∫ y, φ y * fderiv ℝ (interiorCutoffTest d) y
          (polarDensity (rowMeasure (b.inverseDefect n) a) y) ∂(rowMeasure (b.inverseDefect n) a).variation) +
        signedTestCurrent (b.inverseRhs n a) (scalarTestMul (interiorCutoffTest d) φ)) := by
  apply localize_gradient_integral (b.positive n) _ (b.inverseRhs n a) a (interiorCutoffTest d)
    (ball 0 1) _ (b.gradient_equation n a) φ
  exact interiorCutoff_support.trans (ball_subset_ball (by norm_num))

end MatrixPolarBlowupData


/-- DPR arXiv, p. 9 (2.9). Test identity for localSigned, first for smooth compact tests. -/
theorem localSigned_test (χ φ : ScalarCurrentTest d)
    (q : SignedMeasure (EuclideanSpace ℝ (Fin d))) :
    signedTestCurrent (localSigned (χ : BoundedContinuousFunction _ ℝ) q) φ =
      signedTestCurrent q (scalarTestMul χ φ) := by
  rw [localSigned, sub_eq_add_neg, signedTestCurrent_add, signedTestCurrent_neg]
  change signedTestCurrent _ φ - signedTestCurrent _ φ = _
  rw [← signedMeasurePairing_currentTest, ← signedMeasurePairing_currentTest]
  change signedMeasurePairing (q.toJordanDecomposition.posPart.withDensityᵥ (fun y => χ y))
      (φ : BoundedContinuousFunction _ ℝ) -
    signedMeasurePairing (q.toJordanDecomposition.negPart.withDensityᵥ (fun y => χ y))
      (φ : BoundedContinuousFunction _ ℝ) = _
  rw [signedMeasurePairing_density _ (fun y => χ y) (χ.integrable (locallyIntegrableOn_const (1 : ℝ))),
    signedMeasurePairing_density _ (fun y => χ y) (χ.integrable (locallyIntegrableOn_const (1 : ℝ))),
    signedTestCurrent_apply]
  change (∫ y, φ y * χ y ∂q.toJordanDecomposition.posPart) -
      (∫ y, φ y * χ y ∂q.toJordanDecomposition.negPart) =
    (∫ y, χ y * φ y ∂q.toJordanDecomposition.posPart) -
      (∫ y, χ y * φ y ∂q.toJordanDecomposition.negPart)
  simp only [mul_comm]

/--
DPR arXiv, p. 9 (2.9). Actual signed measure G = ν∂ₐχ − E·∇χ + χq, with the signs of the product
rule.
-/
def localizedGradientRemainder
    (ν : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (E : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (q : SignedMeasure (EuclideanSpace ℝ (Fin d))) (a : Fin d) (χ : ScalarCurrentTest d) :
    SignedMeasure (EuclideanSpace ℝ (Fin d)) :=
  (ν : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
      (fun y => fderiv ℝ χ y (EuclideanSpace.single a (1 : ℝ))) -
    E.variation.withDensityᵥ (fun y => fderiv ℝ χ y (polarDensity E y)) +
    localSigned (χ : BoundedContinuousFunction _ ℝ) q

/--
DPR arXiv, p. 9 (2.9). Exact integral expression of the signed remainder on every smooth compactly
supported scalar test.
-/
theorem localizedGradientRemainder_test
    (ν : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (E : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (q : SignedMeasure (EuclideanSpace ℝ (Fin d))) (a : Fin d) (χ φ : ScalarCurrentTest d) :
    signedTestCurrent (localizedGradientRemainder ν E q a χ) φ =
      (∫ y, φ y * fderiv ℝ χ y (EuclideanSpace.single a (1 : ℝ)) ∂(ν : Measure (EuclideanSpace ℝ (Fin d)))) -
      (∫ y, φ y * fderiv ℝ χ y (polarDensity E y) ∂E.variation) +
      signedTestCurrent q (scalarTestMul χ φ) := by
  have hν : Integrable (fun y => fderiv ℝ χ y (EuclideanSpace.single a (1 : ℝ)))
      (ν : Measure (EuclideanSpace ℝ (Fin d))) :=
    integrable_boundedCovector_apply _ (integrable_const _)
      (currentTestDerivative χ : BoundedCovectorField d d)
  have hE : Integrable (fun y => fderiv ℝ χ y (polarDensity E y)) E.variation :=
    integrable_vectorMeasurePairing E (currentTestDerivative χ : BoundedCovectorField d d)
  rw [localizedGradientRemainder, sub_eq_add_neg, signedTestCurrent_add,
    signedTestCurrent_add, signedTestCurrent_neg]
  change signedTestCurrent _ φ - signedTestCurrent _ φ + signedTestCurrent _ φ = _
  rw [localSigned_test, ← signedMeasurePairing_currentTest,
    ← signedMeasurePairing_currentTest, signedMeasurePairing_density _ _ hν,
    signedMeasurePairing_density _ _ hE]
  rfl

/--
DPR arXiv, p. 9 (2.9). The localization identity as an equation of actual measures tested on every
compact smooth test.
-/
theorem localize_gradient_equation
    (ν : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (E : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (q : SignedMeasure (EuclideanSpace ℝ (Fin d))) (a : Fin d)
    (χ : ScalarCurrentTest d) (hχpos : ∀ y, 0 ≤ χ y)
    (U : Set (EuclideanSpace ℝ (Fin d))) (hχ : tsupport χ ⊆ U)
    (heq : ∀ ψ : ScalarCurrentTest d, tsupport ψ ⊆ U →
      oneCurrentBoundary (measureOneCurrent ((ν : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
        (fun _ => EuclideanSpace.single a (1 : ℝ)))) ψ =
      oneCurrentBoundary (measureOneCurrent E) ψ - signedTestCurrent q ψ)
    (φ : ScalarCurrentTest d) :
    oneCurrentBoundary (measureOneCurrent
      ((localPositive (χ : BoundedContinuousFunction _ ℝ) ν : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
        (fun _ => EuclideanSpace.single a (1 : ℝ)))) φ =
      oneCurrentBoundary (measureOneCurrent (localVector (χ : BoundedContinuousFunction _ ℝ) E)) φ -
      signedTestCurrent (localizedGradientRemainder ν E q a χ) φ := by
  rw [oneCurrentBoundary_apply, ← vectorMeasurePairing_currentTest,
    vectorMeasurePairing_withDensityᵥ _ (integrable_const _)]
  change (∫ y, fderiv ℝ φ y (EuclideanSpace.single a (1 : ℝ))
      ∂(localPositive (χ : BoundedContinuousFunction _ ℝ) ν : Measure (EuclideanSpace ℝ (Fin d)))) = _
  rw [integral_localPositive _ hχpos, localizedGradientRemainder_test,
    oneCurrentBoundary_apply, ← vectorMeasurePairing_currentTest, localVector_pairing]
  exact localize_gradient_integral ν E q a χ U hχ heq φ

/--
DPR arXiv, p. 9 (2.9). Pairing bound by the covector field uniform norm times the total Euclidean
variation. See also measureOneCurrent_abs_le_supNorm, which uses a current test instead of a
BoundedCovectorField; both interfaces are retained.
-/
theorem vectorMeasurePairing_abs_le_supNorm
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ω : BoundedCovectorField d m) :
    |vectorMeasurePairing N ω| ≤ ‖ω‖ * N.variation.real univ := by
  rw [vectorMeasurePairing, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ (Fin d), ‖ω‖ ∂N.variation := by
      apply integral_mono_ae (integrable_vectorMeasurePairing N ω).norm (integrable_const _)
      filter_upwards [norm_polarDensity_ae N] with y hy
      exact ((ω y).le_opNorm _).trans (by simpa [hy] using ω.norm_coe_le_norm y)
    _ = _ := by simp [mul_comm]

/--
DPR arXiv, p. 9 (2.9). Euclidean variation tending to zero makes every fixed bounded continuous
field pairing vanish.
-/
theorem vectorMeasurePairing_tendsto_zero
    (Ns : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (h : Tendsto (fun n => (Ns n).variation univ) atTop (𝓝 0))
    (ω : BoundedCovectorField d m) :
    Tendsto (fun n => vectorMeasurePairing (Ns n) ω) atTop (𝓝 0) := by
  have hr : Tendsto (fun n => (Ns n).variation.real univ) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal (by simp)).comp h
  have hc := hr.const_mul ‖ω‖
  rw [mul_zero] at hc
  exact squeeze_zero_norm (fun n => by
    simpa only [Real.norm_eq_abs] using vectorMeasurePairing_abs_le_supNorm (Ns n) ω) hc

/--
DPR arXiv, p. 9 (2.9). Bound by the test's uniform norm times the total Jordan variation. See
signedTestCurrent_abs_le_bound for an arbitrary pointwise bound C; this version is its case C = ‖φ‖.
-/
theorem signedTestCurrent_abs_le_supNorm
    (q : SignedMeasure (EuclideanSpace ℝ (Fin d))) (φ : ScalarCurrentTest d) :
    |signedTestCurrent q φ| ≤ ‖(φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ * q.totalVariation.real univ := by
  haveI : IsFiniteMeasure q.totalVariation := by unfold SignedMeasure.totalVariation; infer_instance
  apply (signedTestCurrent_abs_le_integral_norm q φ).trans
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ (Fin d), ‖(φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ ∂q.totalVariation :=
      integral_mono (φ.integrable (locallyIntegrableOn_const (1 : ℝ))).norm
        (integrable_const _) (fun y => (φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm y)
    _ = _ := by simp [mul_comm]

/--
DPR arXiv, p. 9 (2.9). Jordan variation tending to zero makes every fixed smooth compactly supported
scalar test vanish.
-/
theorem signedTestCurrent_tendsto_zero
    (qs : ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (h : Tendsto (fun n => (qs n).totalVariation univ) atTop (𝓝 0))
    (φ : ScalarCurrentTest d) : Tendsto (fun n => signedTestCurrent (qs n) φ) atTop (𝓝 0) := by
  have hr : Tendsto (fun n => (qs n).totalVariation.real univ) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal (by simp)).comp h
  have hc := hr.const_mul ‖(φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖
  rw [mul_zero] at hc
  exact squeeze_zero_norm (fun n => by
    simpa only [Real.norm_eq_abs] using signedTestCurrent_abs_le_supNorm (qs n) φ) hc

/-- DPR arXiv, p. 9 (2.9). The coordinate derivative is itself a smooth compact scalar test. -/
def cutoffPartialTest (χ : ScalarCurrentTest d) (a : Fin d) : ScalarCurrentTest d :=
  TestFunction.lineDerivCLM ℝ (EuclideanSpace.single a (1 : ℝ)) χ

/--
DPR arXiv, p. 9 (2.9). The directional derivative of the test is its Fréchet derivative applied to
the coordinate vector.
-/
theorem cutoffPartialTest_apply (χ : ScalarCurrentTest d) (a : Fin d)
    (y : EuclideanSpace ℝ (Fin d)) :
    cutoffPartialTest χ a y = fderiv ℝ χ y (EuclideanSpace.single a (1 : ℝ)) := by
  rw [cutoffPartialTest, TestFunction.lineDerivCLM_eq_fderivCLM]
  have h := TestFunction.fderivCLM_apply_of_le (𝕜 := ℝ) (k := (⊤ : ℕ∞)) χ (by simp)
  exact congrArg (fun f => f y (EuclideanSpace.single a (1 : ℝ))) h

namespace MatrixPolarBlowupData
variable {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))}
variable {x : EuclideanSpace ℝ (Fin d)}

/--
DPR arXiv, p. 9 (2.9). Euclidean row of the rescaled inverse defect localized by the cutoff χ.
-/
def localizedDefectRow (b : MatrixPolarBlowupData M D x) (n : ℕ) (a : Fin d) :=
  localVector (interiorCutoffTest d : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) (rowMeasure (b.inverseDefect n) a)

/--
DPR arXiv, p. 9 (2.9). Signed product-rule remainder for row a of the matrix polar blow-up data at
index n.
-/
def localizedRemainder (b : MatrixPolarBlowupData M D x) (n : ℕ) (a : Fin d) :=
  localizedGradientRemainder (b.positive n) (rowMeasure (b.inverseDefect n) a)
    (b.inverseRhs n a) a (interiorCutoffTest d)

/--
DPR arXiv, p. 9 (2.9). The variation of every row of the rescaled inverse defect tends to zero.
-/
theorem inverseDefectRow_tendsto (b : MatrixPolarBlowupData M D x) (a : Fin d) :
    Tendsto (fun n => (rowMeasure (b.inverseDefect n) a).variation univ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds b.inverseDefect_tendsto
    (fun _ => zero_le) (fun n => variation_rowMeasure_le (b.inverseDefect n) a univ)

/-- DPR arXiv, p. 9 (2.9). The variation of every row of the localized defect tends to zero. -/
theorem localizedDefectRow_tendsto (b : MatrixPolarBlowupData M D x) (a : Fin d) :
    Tendsto (fun n => (b.localizedDefectRow n a).variation univ) atTop (𝓝 0) :=
  localVector_variation_tendsto_zero _ _ (b.inverseDefectRow_tendsto a)

/--
DPR arXiv, p. 9 (2.9). Global equation B(w_n eₐ) = B(F_n,a) − G_n,a on all smooth compactly
supported tests.
-/
theorem localized_gradient_equation (b : MatrixPolarBlowupData M D x)
    (n : ℕ) (a : Fin d) (φ : ScalarCurrentTest d) :
    oneCurrentBoundary (measureOneCurrent
      ((b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
        (fun _ => EuclideanSpace.single a (1 : ℝ)))) φ =
      oneCurrentBoundary (measureOneCurrent (b.localizedDefectRow n a)) φ -
        signedTestCurrent (b.localizedRemainder n a) φ := by
  exact localize_gradient_equation (b.positive n) _ (b.inverseRhs n a) a (interiorCutoffTest d)
    (interiorCutoff d).nonneg' (ball 0 1)
    (interiorCutoff_support.trans (ball_subset_ball (by norm_num))) (b.gradient_equation n a) φ

/--
DPR arXiv, p. 9 (2.9). The rescaled inverse right-hand side, tested after multiplication by χ,
tends to zero.
-/
theorem localized_source_test_tendsto_zero (b : MatrixPolarBlowupData M D x)
    (a : Fin d) (φ : ScalarCurrentTest d) :
    Tendsto (fun n => signedTestCurrent (b.inverseRhs n a)
      (scalarTestMul (interiorCutoffTest d) φ)) atTop (𝓝 0) :=
  signedTestCurrent_tendsto_zero _ (b.inverseRhs_tendsto a) _

/--
DPR arXiv, p. 9 (2.9). G_j converges on all scalar current tests to ν times the derivative of the
cutoff.
-/
theorem localizedRemainder_test_tendsto (b : MatrixPolarBlowupData M D x)
    (a : Fin d) (φ : ScalarCurrentTest d) :
    Tendsto (fun n => signedTestCurrent (b.localizedRemainder n a) φ) atTop
      (𝓝 (signedTestCurrent ((b.tangent : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
        (fun y => fderiv ℝ (interiorCutoffTest d) y (EuclideanSpace.single a (1 : ℝ)))) φ)) := by
  let χ := interiorCutoffTest d
  have hm := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp b.positive_convergence
    ((φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) *
      (cutoffPartialTest χ a : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ))
  change Tendsto (fun n => ∫ y, φ y * cutoffPartialTest χ a y
    ∂(b.positive n : Measure (EuclideanSpace ℝ (Fin d)))) atTop
    (𝓝 (∫ y, φ y * cutoffPartialTest χ a y ∂(b.tangent : Measure (EuclideanSpace ℝ (Fin d))))) at hm
  simp only [cutoffPartialTest_apply] at hm
  have he := vectorMeasurePairing_tendsto_zero _ (b.inverseDefectRow_tendsto a)
    ((φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) •
      (currentTestDerivative χ : BoundedCovectorField d d))
  change Tendsto (fun n => ∫ y, φ y * fderiv ℝ χ y
    (polarDensity (rowMeasure (b.inverseDefect n) a) y)
    ∂(rowMeasure (b.inverseDefect n) a).variation) atTop (𝓝 0) at he
  have hq := b.localized_source_test_tendsto_zero a φ
  have hh := (hm.sub he).add hq
  simp only [sub_zero, add_zero] at hh
  simp only [localizedRemainder, localizedGradientRemainder_test]
  have hi : Integrable (fun y => fderiv ℝ (interiorCutoffTest d) y (EuclideanSpace.single a (1 : ℝ)))
      (b.tangent : Measure (EuclideanSpace ℝ (Fin d))) :=
    integrable_boundedCovector_apply _ (integrable_const _)
      (currentTestDerivative χ : BoundedCovectorField d d)
  rw [← signedMeasurePairing_currentTest, signedMeasurePairing_density _ _ hi]
  exact hh

end MatrixPolarBlowupData


/--
DPR arXiv, p. 9 (2.9). Bound C times the total Jordan variation, for any pointwise majorant C of the
test norm. See signedTestCurrent_abs_le_supNorm for the uniform norm case.
-/
theorem signedTestCurrent_abs_le_bound
    (q : SignedMeasure (EuclideanSpace ℝ (Fin d))) (ψ : ScalarCurrentTest d)
    (C : ℝ) (hC : ∀ y, ‖ψ y‖ ≤ C) :
    |signedTestCurrent q ψ| ≤ C * q.totalVariation.real univ := by
  haveI : IsFiniteMeasure q.totalVariation := by unfold SignedMeasure.totalVariation; infer_instance
  apply (signedTestCurrent_abs_le_integral_norm q ψ).trans
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ (Fin d), C ∂q.totalVariation :=
      integral_mono (ψ.integrable (locallyIntegrableOn_const (1 : ℝ))).norm (integrable_const _) hC
    _ = _ := by simp [mul_comm]

/--
DPR arXiv, p. 9 (2.9). For a test bounded by one and an integrable vector density of norm at most
one a.e., the cutoff-derivative term is bounded by the derivative's uniform norm times the finite
source mass.
-/
theorem integral_cutoff_derivative_abs_le
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    (p : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hp : Integrable p μ) (hpn : ∀ᵐ y ∂μ, ‖p y‖ ≤ 1)
    (χ φ : ScalarCurrentTest d) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    |∫ y, φ y * fderiv ℝ χ y (p y) ∂μ| ≤
      ‖(currentTestDerivative χ : BoundedCovectorField d d)‖ * μ.real univ := by
  let C := ‖(currentTestDerivative χ : BoundedCovectorField d d)‖
  have hi : Integrable (fun y => φ y * fderiv ℝ χ y (p y)) μ :=
    (integrable_boundedCovector_apply μ hp (currentTestDerivative χ : BoundedCovectorField d d)).bdd_mul
      φ.continuous.aestronglyMeasurable (Eventually.of_forall hφ)
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ (Fin d), C ∂μ := by
      apply integral_mono_ae hi.norm (integrable_const _)
      filter_upwards [hpn] with y hy
      rw [norm_mul]
      have hd : ‖fderiv ℝ χ y‖ ≤ C :=
        (currentTestDerivative χ : BoundedCovectorField d d).norm_coe_le_norm y
      calc
        _ ≤ 1 * (‖fderiv ℝ χ y‖ * ‖p y‖) :=
          mul_le_mul (hφ y) ((fderiv ℝ χ y).le_opNorm _) (norm_nonneg _) (by norm_num)
        _ ≤ C := by nlinarith [norm_nonneg (fderiv ℝ χ y), norm_nonneg (p y)]
    _ = _ := by simp [C, mul_comm]

/--
DPR arXiv, p. 9 (2.9). Bound on the remainder's Jordan variation by the masses of ν, E and q and the
norms of χ and ∇χ.
-/
theorem localizedGradientRemainder_mass_le
    (ν : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (E : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (q : SignedMeasure (EuclideanSpace ℝ (Fin d))) (a : Fin d) (χ : ScalarCurrentTest d) :
    (localizedGradientRemainder ν E q a χ).totalVariation.real univ ≤
      ‖(currentTestDerivative χ : BoundedCovectorField d d)‖ * (ν : Measure (EuclideanSpace ℝ (Fin d))).real univ +
      ‖(currentTestDerivative χ : BoundedCovectorField d d)‖ * E.variation.real univ +
      ‖(χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ * q.totalVariation.real univ := by
  let C := ‖(currentTestDerivative χ : BoundedCovectorField d d)‖ * (ν : Measure (EuclideanSpace ℝ (Fin d))).real univ +
      ‖(currentTestDerivative χ : BoundedCovectorField d d)‖ * E.variation.real univ +
      ‖(χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ * q.totalVariation.real univ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have htv : (localizedGradientRemainder ν E q a χ).totalVariation univ ≤ ENNReal.ofReal C := by
    rw [← signedTestCurrent_mass_eq_totalVariation _ isOpen_univ]
    apply testFunctionalMassOn_le
    intro φ _ hn
    rw [localizedGradientRemainder_test]
    have hν := integral_cutoff_derivative_abs_le (ν : Measure (EuclideanSpace ℝ (Fin d)))
      (fun _ => EuclideanSpace.single a (1 : ℝ)) (integrable_const _)
      (Eventually.of_forall (fun _ => by simp)) χ φ hn
    have hE := integral_cutoff_derivative_abs_le E.variation (polarDensity E)
      (integrable_polarDensity E) ((norm_polarDensity_ae E).mono (fun _ h => h.le)) χ φ hn
    have hq := signedTestCurrent_abs_le_bound q (scalarTestMul χ φ)
      ‖(χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ (fun y => by
        change ‖χ y * φ y‖ ≤ _
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left (hn y) (norm_nonneg _)).trans
          (by simpa using (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm y))
    apply ENNReal.ofReal_le_ofReal
    rcases abs_le.mp hν with ⟨hν₁, hν₂⟩
    rcases abs_le.mp hE with ⟨hE₁, hE₂⟩
    rcases abs_le.mp hq with ⟨hq₁, hq₂⟩
    have hsum := add_le_add (add_le_add hν₂ (neg_le_neg hE₁)) hq₂
    simpa only [neg_neg, sub_eq_add_neg] using hsum
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top htv).trans_eq (ENNReal.toReal_ofReal hC)

/--
DPR arXiv, p. 9 (2.9). The localized Jordan variation vanishes outside the support of the cutoff
test.
-/
theorem localSigned_support (χ : ScalarCurrentTest d)
    (q : SignedMeasure (EuclideanSpace ℝ (Fin d))) :
    (localSigned (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) q).totalVariation
      (tsupport χ)ᶜ = 0 := by
  apply le_antisymm _ bot_le
  rw [← signedTestCurrent_mass_eq_totalVariation _ (isClosed_tsupport χ).isOpen_compl]
  apply testFunctionalMassOn_le
  intro φ hs _
  rw [localSigned_test]
  have hz : scalarTestMul χ φ = 0 := by
    apply TestFunction.ext
    intro y
    change χ y * φ y = 0
    by_cases hy : y ∈ tsupport χ
    · have hp : y ∉ tsupport φ := fun hp => hs hp hy
      rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  simp [hz]

set_option maxHeartbeats 800000 in
/--
DPR arXiv, p. 9 (2.9). All three signed remainder terms are carried by the closed support of the
cutoff.
-/
theorem localizedGradientRemainder_support
    (ν : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (E : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (q : SignedMeasure (EuclideanSpace ℝ (Fin d))) (a : Fin d) (χ : ScalarCurrentTest d) :
    (localizedGradientRemainder ν E q a χ).totalVariation (tsupport χ)ᶜ = 0 := by
  have hν : Integrable (fun y => fderiv ℝ χ y (EuclideanSpace.single a (1 : ℝ)))
      (ν : Measure (EuclideanSpace ℝ (Fin d))) :=
    integrable_boundedCovector_apply _ (integrable_const _)
      (currentTestDerivative χ : BoundedCovectorField d d)
  have hE : Integrable (fun y => fderiv ℝ χ y (polarDensity E y)) E.variation :=
    integrable_vectorMeasurePairing E (currentTestDerivative χ : BoundedCovectorField d d)
  have hn := signedDensity_support (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (fun y => fderiv ℝ χ y (EuclideanSpace.single a (1 : ℝ))) hν (tsupport χ) (isClosed_tsupport χ)
    (Eventually.of_forall (fun y hy => by rw [fderiv_of_notMem_tsupport ℝ hy]; rfl))
  have he := signedDensity_support E.variation (fun y => fderiv ℝ χ y (polarDensity E y))
    hE (tsupport χ) (isClosed_tsupport χ)
    (Eventually.of_forall (fun y hy => by rw [fderiv_of_notMem_tsupport ℝ hy]; rfl))
  have hq := localSigned_support χ q
  let Nν : SignedMeasure (EuclideanSpace ℝ (Fin d)) :=
    (ν : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
      (fun y => fderiv ℝ χ y (EuclideanSpace.single a (1 : ℝ)))
  let NE : SignedMeasure (EuclideanSpace ℝ (Fin d)) :=
    E.variation.withDensityᵥ (fun y => fderiv ℝ χ y (polarDensity E y))
  let Nq := localSigned (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) q
  have h1 := signedTotalVariation_add_le_of_isOpen (Nν + -NE) Nq (isClosed_tsupport χ).isOpen_compl
  have h2 := signedTotalVariation_add_le_of_isOpen Nν (-NE) (isClosed_tsupport χ).isOpen_compl
  change Nν.totalVariation (tsupport χ)ᶜ = 0 at hn
  change NE.totalVariation (tsupport χ)ᶜ = 0 at he
  change Nq.totalVariation (tsupport χ)ᶜ = 0 at hq
  have h3 := h1.trans (add_le_add h2 (le_rfl : Nq.totalVariation (tsupport χ)ᶜ ≤ _))
  change (Nν - NE + Nq).totalVariation (tsupport χ)ᶜ = 0
  apply le_antisymm _ bot_le
  simpa [sub_eq_add_neg, SignedMeasure.totalVariation_neg, hn, he, hq] using h3

namespace MatrixPolarBlowupData
variable {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))}
variable {x : EuclideanSpace ℝ (Fin d)}

/--
DPR arXiv, p. 9 (2.9). The total variation of every row of the localized remainder is uniformly
bounded in n.
-/
theorem localizedRemainder_uniform_bound (b : MatrixPolarBlowupData M D x) (a : Fin d) :
    ∃ C : ℝ, ∀ n, (b.localizedRemainder n a).totalVariation.real univ ≤ C := by
  let A := ‖(currentTestDerivative (interiorCutoffTest d) : BoundedCovectorField d d)‖
  let B := ‖(interiorCutoffTest d : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖
  have he : Tendsto (fun n => (rowMeasure (b.inverseDefect n) a).variation.real univ) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal (by simp)).comp (b.inverseDefectRow_tendsto a)
  have hq : Tendsto (fun n => (b.inverseRhs n a).totalVariation.real univ) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal (by simp)).comp (b.inverseRhs_tendsto a)
  have ht := ((he.const_mul A).const_add A).add (hq.const_mul B)
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  refine ⟨C, fun n => ?_⟩
  have h := localizedGradientRemainder_mass_le (b.positive n) (rowMeasure (b.inverseDefect n) a) (b.inverseRhs n a) a (interiorCutoffTest d)
  have hm : (b.positive n : Measure (EuclideanSpace ℝ (Fin d))).real univ = 1 := by
    rw [measureReal_def, ← FiniteMeasure.ennreal_mass, b.positive_mass]
    simp
  rw [hm, mul_one] at h
  exact h.trans (hC ⟨n, rfl⟩)

/--
DPR arXiv, p. 8 (2.5). Each localized positive measure is carried by the closed ball of radius
13/16.
-/
theorem localizedPositive_support (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d)))
      (closedBall (0 : EuclideanSpace ℝ (Fin d)) (13 / 16))ᶜ = 0 := by
  have h := localPositive_support (interiorCutoffTest d : BoundedContinuousFunction _ ℝ) (b.positive n)
  change (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))) (tsupport (interiorCutoff d))ᶜ = 0 at h
  simpa only [ContDiffBump.tsupport_eq, interiorCutoff] using h

/--
DPR arXiv, p. 8 (2.5). The localized limit measure is carried by the same closed ball of radius
13/16.
-/
theorem localizedTangent_support (b : MatrixPolarBlowupData M D x) :
    (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d)))
      (closedBall (0 : EuclideanSpace ℝ (Fin d)) (13 / 16))ᶜ = 0 := by
  have h := localPositive_support (interiorCutoffTest d : BoundedContinuousFunction _ ℝ) b.tangent
  change (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))) (tsupport (interiorCutoff d))ᶜ = 0 at h
  simpa only [ContDiffBump.tsupport_eq, interiorCutoff] using h

/--
DPR arXiv, p. 8 (2.5). The unit support of the rescaled measure is preserved after localization by χ
≤ 1.
-/
theorem localizedPositive_support_unit (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d)))
      (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 :=
  le_antisymm ((localPositive_le _ (fun _ => (interiorCutoff d).le_one) (b.positive n)
    (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ).trans_eq (b.positive_support n)) bot_le

/--
DPR arXiv, p. 8 (2.5). The variation of every row of the localized defect vanishes outside the
closed ball of radius 13/16.
-/
theorem localizedDefectRow_support (b : MatrixPolarBlowupData M D x) (n : ℕ) (a : Fin d) :
    (b.localizedDefectRow n a).variation (closedBall (0 : EuclideanSpace ℝ (Fin d)) (13 / 16))ᶜ = 0 := by
  have h := localVector_support (interiorCutoffTest d : BoundedContinuousFunction _ ℝ)
    (rowMeasure (b.inverseDefect n) a)
  change (b.localizedDefectRow n a).variation (tsupport (interiorCutoff d))ᶜ = 0 at h
  simpa only [ContDiffBump.tsupport_eq, interiorCutoff] using h

/--
DPR arXiv, p. 8 (2.5). The variation of each localized remainder vanishes outside the closed ball of
radius 13/16.
-/
theorem localizedRemainder_support (b : MatrixPolarBlowupData M D x) (n : ℕ) (a : Fin d) :
    (b.localizedRemainder n a).totalVariation
      (closedBall (0 : EuclideanSpace ℝ (Fin d)) (13 / 16))ᶜ = 0 := by
  have h := localizedGradientRemainder_support (b.positive n) (rowMeasure (b.inverseDefect n) a) (b.inverseRhs n a) a (interiorCutoffTest d)
  change (b.localizedRemainder n a).totalVariation (tsupport (interiorCutoff d))ᶜ = 0 at h
  simpa only [ContDiffBump.tsupport_eq, interiorCutoff] using h

/--
DPR arXiv, p. 8 (2.5). Index chosen by the actual diagonal for the pair (w_n,w), shared by z, f and
g.
-/
def localizationMollifierIndex (b : MatrixPolarBlowupData M D x) : ℕ → ℕ :=
  Classical.choose (positive_mollification_tv_diagonal b.localizedPositive b.localizedTangent)

/--
DPR arXiv, p. 8 (2.5). The index is at least n, its radius tends to zero and is at most
1/(n+1), with the TV inequality at tolerance 1/(n+1).
-/
theorem localizationMollifierIndex_spec (b : MatrixPolarBlowupData M D x) :
    (∀ j, j ≤ b.localizationMollifierIndex j) ∧
    (∀ j, 0 < diagonalError (b.localizationMollifierIndex j) ∧
      diagonalError (b.localizationMollifierIndex j) ≤ diagonalError j) ∧
    Tendsto (fun j => diagonalError (b.localizationMollifierIndex j)) atTop (𝓝 0) ∧
    ∀ j, ((b.localizedPositive j : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure -
        (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure).totalVariation.real univ ≤
      (signedMollification (b.localizedPositive j) (b.localizationMollifierIndex j) -
        (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure).totalVariation.real univ + diagonalError j :=
  Classical.choose_spec (positive_mollification_tv_diagonal b.localizedPositive b.localizedTangent)

/--
DPR arXiv, p. 8 (2.5). Function z_n obtained by convolving w_n with the kernel at the chosen
diagonal index.
-/
def mollifiedPositive (b : MatrixPolarBlowupData M D x) (n : ℕ) :=
  positiveConvolution (b.localizedPositive n) (standardMollifier d (b.localizationMollifierIndex n))

/--
DPR arXiv, p. 8 (2.5). Vector function f_n,a obtained by convolving F_n,a at the same diagonal
index as z_n.
-/
def mollifiedDefectRow (b : MatrixPolarBlowupData M D x) (n : ℕ) (a : Fin d) :=
  measureConvolution (b.localizedDefectRow n a) (standardMollifier d (b.localizationMollifierIndex n))

/--
DPR arXiv, p. 8 (2.5). Signed function g_n,a obtained by convolving G_n,a at the same diagonal
index as z_n.
-/
def mollifiedRemainder (b : MatrixPolarBlowupData M D x) (n : ℕ) (a : Fin d) :=
  signedConvolution (b.localizedRemainder n a) (standardMollifier d (b.localizationMollifierIndex n))

/-- DPR arXiv, p. 8 (2.5). The mollified function z_n is nonnegative at every point. -/
theorem mollifiedPositive_nonneg (b : MatrixPolarBlowupData M D x) (n : ℕ)
    (y : EuclideanSpace ℝ (Fin d)) : 0 ≤ b.mollifiedPositive n y :=
  positiveConvolution_nonneg _ _ (standardMollifier_properties d _).1 y

/-- DPR arXiv, p. 8 (2.5). The functions z_n and all rows f_n,a and g_n,a are smooth. -/
theorem mollified_smooth (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (b.mollifiedPositive n) ∧
    ∀ a, ContDiff ℝ (⊤ : ℕ∞) (b.mollifiedDefectRow n a) ∧
      ContDiff ℝ (⊤ : ℕ∞) (b.mollifiedRemainder n a) := by
  have h := standardMollifier_properties d (b.localizationMollifierIndex n)
  exact ⟨positiveConvolution_smooth _ _ h.2.2.1 h.2.2.2.1,
    fun a => ⟨measureConvolution_smooth _ _ h.2.2.1 h.2.2.2.1,
      signedConvolution_smooth _ _ h.2.2.1 h.2.2.2.1⟩⟩

/--
DPR arXiv, p. 8 (2.5). Pointwise equation ∂ₐz_n = div f_n,a + g_n,a after localization and then
convolution.
-/
theorem mollified_gradient_equation (b : MatrixPolarBlowupData M D x) (n : ℕ) (a : Fin d)
    (y : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (b.mollifiedPositive n) y (EuclideanSpace.single a (1 : ℝ)) =
      smoothDivergence (b.mollifiedDefectRow n a) y + b.mollifiedRemainder n a y :=
  convolved_gradient_equation (b.localizedPositive n) (b.localizedDefectRow n a)
    (b.localizedRemainder n a) a (b.localized_gradient_equation n a)
    (standardMollifierTest d (b.localizationMollifierIndex n)) y

/-- DPR arXiv, p. 8 (2.5). The Euclidean L¹ norm of each row f_n,a tends to zero. -/
theorem mollifiedDefectRow_L1_tendsto (b : MatrixPolarBlowupData M D x) (a : Fin d) :
    Tendsto (fun n => ∫ y, ‖b.mollifiedDefectRow n a y‖) atTop (𝓝 0) :=
  measureConvolution_L1_tendsto_zero _ _
    (fun n => (standardMollifier_properties d (b.localizationMollifierIndex n)).2.2.2.2)
    (fun n => (standardMollifier_properties d (b.localizationMollifierIndex n)).1)
    (fun n => (standardMollifier_properties d (b.localizationMollifierIndex n)).2.1) (b.localizedDefectRow_tendsto a)

/-- DPR arXiv, p. 8 (2.5). The L¹ norm of each row g_n,a is uniformly bounded in n. -/
theorem mollifiedRemainder_L1_bounded (b : MatrixPolarBlowupData M D x) (a : Fin d) :
    ∃ C : ℝ, ∀ n, (∫ y, ‖b.mollifiedRemainder n a y‖) ≤ C := by
  obtain ⟨C, hC⟩ := b.localizedRemainder_uniform_bound a
  exact ⟨C, fun n => (signedConvolution_norm_le_variation _ _
    (standardMollifier_properties d _).2.2.2.2
    (standardMollifier_properties d _).1 (standardMollifier_properties d _).2.1).trans (hC n)⟩

/-- DPR arXiv, p. 8 (2.5). The mass of each localized positive measure is at most 1. -/
theorem localizedPositive_mass_le_one (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).real univ ≤ 1 := by
  have h := localPositive_le (interiorCutoffTest d : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (fun _ => (interiorCutoff d).le_one) (b.positive n) univ
  have hh := ENNReal.toReal_mono (measure_ne_top _ _) h
  have hm : (b.positive n : Measure (EuclideanSpace ℝ (Fin d))).real univ = 1 := by
    rw [measureReal_def, ← FiniteMeasure.ennreal_mass, b.positive_mass]
    simp
  exact hh.trans_eq hm

/--
DPR arXiv, p. 8 (2.5). Convergence of z_n dx to w on all smooth compactly supported scalar
tests only.
-/
theorem mollifiedPositive_test_tendsto (b : MatrixPolarBlowupData M D x) (φ : ScalarCurrentTest d) :
    Tendsto (fun n => ∫ y, φ y * b.mollifiedPositive n y) atTop
      (𝓝 (∫ y, φ y ∂(b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))))) :=
  variable_mollifier_test_tendsto _ _ b.localizedPositive_tendsto _
    b.localizationMollifierIndex_spec.2.2.1 1 b.localizedPositive_mass_le_one φ

/-- DPR arXiv, p. 8 (2.5). The integral of z_n is exactly the mass of w_n at each index. -/
theorem mollifiedPositive_mass (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    (∫ y, b.mollifiedPositive n y) =
      (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))).real univ :=
  positiveConvolution_mass _ _ (standardMollifier_properties d _).2.2.2.2
    (standardMollifier_properties d _).2.1

/--
DPR arXiv, p. 8 (2.5). The integrals of z_n converge to the mass of w, whose positivity is
established separately.
-/
theorem mollifiedPositive_mass_tendsto (b : MatrixPolarBlowupData M D x) :
    Tendsto (fun n => ∫ y, b.mollifiedPositive n y) atTop
      (𝓝 ((b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).real univ)) := by
  simp only [b.mollifiedPositive_mass]
  have h := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp b.localizedPositive_tendsto
    (1 : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
  simpa using h

/--
DPR arXiv, p. 8 (2.5). One common compact set, the closed ball of radius 2, carries z_n and all rows
f_n,a and g_n,a.
-/
theorem mollified_common_support (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    tsupport (b.mollifiedPositive n) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) 2 ∧
    ∀ a, tsupport (b.mollifiedDefectRow n a) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) 2 ∧
      tsupport (b.mollifiedRemainder n a) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) 2 := by
  have hb : closedBall (0 : EuclideanSpace ℝ (Fin d)) (13 / 16 + 1) ⊆ closedBall 0 2 :=
    closedBall_subset_closedBall (by norm_num)
  have hρ := standardMollifier_support_unit d (b.localizationMollifierIndex n)
  exact ⟨(positiveConvolution_support _ _ _ _ (b.localizedPositive_support n) hρ).trans hb,
    fun a => ⟨(measureConvolution_support _ _ _ _ (b.localizedDefectRow_support n a) hρ).trans hb,
      (signedConvolution_support _ _ _ _ (b.localizedRemainder_support n a) hρ).trans hb⟩⟩

/-- DPR arXiv, p. 8 (2.5). The mollified measure of the diagonal specification is exactly z_j dx. -/
theorem signedMollification_localized_eq (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    signedMollification (b.localizedPositive n) (b.localizationMollifierIndex n) =
      volume.withDensityᵥ (b.mollifiedPositive n) := rfl

/--
DPR arXiv, p. 8 (2.5). Each localized measure w_j is still singular (used in the
singularity contradiction).
-/
theorem localizedPositive_singular (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    (b.localizedPositive n : Measure (EuclideanSpace ℝ (Fin d))) ⟂ₘ volume :=
  (b.positive_singular n).mono_ac (withDensity_absolutelyContinuous _ _)
    Measure.AbsolutelyContinuous.rfl

/--
DPR arXiv, p. 8 (2.5). The weak limit G = ν ∂ₐχ of the remainders has the same common support
(used for convolution convergence).
-/
theorem localizedRemainderLimit_support (b : MatrixPolarBlowupData M D x) (a : Fin d) :
    (SignedMeasure.totalVariation ((b.tangent : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
        (fun y => fderiv ℝ (interiorCutoffTest d) y (EuclideanSpace.single a (1 : ℝ)))))
      (closedBall (0 : EuclideanSpace ℝ (Fin d)) (13 / 16))ᶜ = 0 := by
  have hi : Integrable (fun y => fderiv ℝ (interiorCutoffTest d) y (EuclideanSpace.single a (1 : ℝ)))
      (b.tangent : Measure (EuclideanSpace ℝ (Fin d))) :=
    integrable_boundedCovector_apply _ (integrable_const _)
      (currentTestDerivative (interiorCutoffTest d) : BoundedCovectorField d d)
  have h := signedDensity_support (b.tangent : Measure (EuclideanSpace ℝ (Fin d)))
    (fun y => fderiv ℝ (interiorCutoffTest d) y (EuclideanSpace.single a (1 : ℝ))) hi
    (tsupport (interiorCutoffTest d)) (isClosed_tsupport _)
    (Eventually.of_forall (fun y hy => by rw [fderiv_of_notMem_tsupport ℝ hy]; rfl))
  change (SignedMeasure.totalVariation ((b.tangent : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
      (fun y => fderiv ℝ (interiorCutoffTest d) y (EuclideanSpace.single a (1 : ℝ)))))
      (tsupport (interiorCutoff d))ᶜ = 0 at h
  simpa only [ContDiffBump.tsupport_eq, interiorCutoff] using h

end MatrixPolarBlowupData
end GeometricMeasure
