import GeometricMeasure.Current.MollificationDiagonal

/-!
# Signed mollification at variable scales

## Main results
For signed measures with bounded Jordan variations converging against smooth tests, convolution at
scales tending to zero preserves the test limit. The error estimate applies to both Jordan parts
without requiring them to converge separately. Monotonicity of the scales is unnecessary.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped Topology Convolution
namespace GeometricMeasure
namespace KernelCompactness
variable {d : ℕ}

/-- The product of a test and an integrable function is integrable (test on the left). -/
theorem integrable_test_mul {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Integrable f)
    (φ : ScalarCurrentTest d) : Integrable (fun y => φ y * f y) :=
  hf.bdd_mul φ.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun y => (φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm y))

/-- Quantitative mollification error of a signed measure against a smooth test. -/
theorem signed_mollifier_test_error (q : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (φ : ScalarCurrentTest d) (k : ℕ) :
    |(∫ y, φ y * signedConvolution q (standardMollifier d k) y) - signedTestCurrent q φ| ≤
      (‖(currentTestDerivative φ : BoundedCovectorField d d)‖ * diagonalError k) *
        q.totalVariation.real univ := by
  let μp : FiniteMeasure (EuclideanSpace ℝ (Fin d)) := ⟨q.toJordanDecomposition.posPart, inferInstance⟩
  let μn : FiniteMeasure (EuclideanSpace ℝ (Fin d)) := ⟨q.toJordanDecomposition.negPart, inferInstance⟩
  have hρ := (standardMollifier_properties d k).2.2.2.2
  have ip := integrable_test_mul (positiveConvolution_integrable μp _ hρ) φ
  have in' := integrable_test_mul (positiveConvolution_integrable μn _ hρ) φ
  have hsplit : (∫ y, φ y * signedConvolution q (standardMollifier d k) y) =
      (∫ y, φ y * positiveConvolution μp (standardMollifier d k) y) -
        ∫ y, φ y * positiveConvolution μn (standardMollifier d k) y := by
    rw [← integral_sub ip in']
    congr 1
    funext y
    simp only [signedConvolution, Pi.sub_apply, mul_sub]
    rfl
  have htv : q.totalVariation.real univ =
      (μp : Measure (EuclideanSpace ℝ (Fin d))).real univ +
        (μn : Measure (EuclideanSpace ℝ (Fin d))).real univ := by
    simp only [SignedMeasure.totalVariation, measureReal_def, Measure.add_apply]
    exact ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
  have ep := positive_mollifier_test_error μp φ k
  have en := positive_mollifier_test_error μn φ k
  rw [hsplit, signedTestCurrent_apply, htv, mul_add]
  have he : (∫ y, φ y * positiveConvolution μp (standardMollifier d k) y) -
        (∫ y, φ y * positiveConvolution μn (standardMollifier d k) y) -
      ((∫ x, φ x ∂q.toJordanDecomposition.posPart) - ∫ x, φ x ∂q.toJordanDecomposition.negPart) =
      ((∫ y, φ y * positiveConvolution μp (standardMollifier d k) y) -
          ∫ x, φ x ∂(μp : Measure (EuclideanSpace ℝ (Fin d)))) -
        ((∫ y, φ y * positiveConvolution μn (standardMollifier d k) y) -
          ∫ x, φ x ∂(μn : Measure (EuclideanSpace ℝ (Fin d)))) := by
    simp only [μp, μn, FiniteMeasure.toMeasure_mk]
    ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add ep en)

/--
For signed measures with bounded Jordan variations, mollifications at scales tending to zero have
the same smooth-test limit as the original sequence.
-/
theorem signed_variable_mollifier_test_tendsto
    (qs : ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d))) (q : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hq : ∀ φ : ScalarCurrentTest d,
      Tendsto (fun n => signedTestCurrent (qs n) φ) atTop (𝓝 (signedTestCurrent q φ)))
    (k : ℕ → ℕ) (hk : Tendsto (fun j => diagonalError (k j)) atTop (𝓝 0))
    (C : ℝ) (hC : ∀ j, (qs j).totalVariation.real univ ≤ C) (φ : ScalarCurrentTest d) :
    Tendsto (fun j => ∫ y, φ y * signedConvolution (qs j) (standardMollifier d (k j)) y)
      atTop (𝓝 (signedTestCurrent q φ)) := by
  have ht := (hk.const_mul ‖(currentTestDerivative φ : BoundedCovectorField d d)‖).mul_const C
  simp only [mul_zero, zero_mul] at ht
  have herr : Tendsto (fun j => (∫ y, φ y * signedConvolution (qs j) (standardMollifier d (k j)) y) -
      signedTestCurrent (qs j) φ) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ ht
    intro j
    rw [Real.norm_eq_abs]
    exact (signed_mollifier_test_error (qs j) φ (k j)).trans
      (mul_le_mul_of_nonneg_left (hC j)
        (mul_nonneg (norm_nonneg (currentTestDerivative φ : BoundedCovectorField d d))
          (diagonalError_pos _).le))
  have hh := herr.add (hq φ)
  simp only [zero_add, sub_add_cancel] at hh
  exact hh

end KernelCompactness
end GeometricMeasure
