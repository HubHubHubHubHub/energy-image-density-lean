import GeometricMeasure.Current.KernelCompactness
import GeometricMeasure.Current.SignedMollifierTests
import GeometricMeasure.Current.BesselResolventPackage
import GeometricMeasure.Current.StrongBlowupLimit

/-!
# The regular Bessel resolvent limit

## Main results
For the localized matrix polar blow-up data and its fixed diagonal sequence, the regular resolvent
terms converge in L¹ to h = B ∗ w − Σₐ Bₐ ∗ Gₐ, with w = χν and Gₐ = ν ∂ₐχ. This constructs the
witness for `RegularPartL1Limit` used by the strong-convergence argument.

Reference: De Philippis–Rindler, arXiv p. 9, (2.10).
The resulting limit is used in `Current.MatrixStructure` to prove De Philippis–Rindler, Corollary
1.13.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped Topology Convolution
namespace GeometricMeasure
namespace MatrixPolarBlowupData
variable {d : ℕ} {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}

/-- Weak limit Gₐ = ν ∂ₐχ of the localized remainders (from `localizedRemainder_test_tendsto`). -/
def regularRemainderLimit (b : MatrixPolarBlowupData M D x) (a : Fin d) :
    SignedMeasure (EuclideanSpace ℝ (Fin d)) :=
  (b.tangent : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
    (fun y => fderiv ℝ (interiorCutoffTest d) y (EuclideanSpace.single a (1 : ℝ)))

/--
The explicit regular-part limit is h = B ∗ w − Σₐ Bₐ ∗ Gₐ. Reference: De Philippis–Rindler, arXiv p.
9, (2.10), the regular resolvent terms.
-/
def regularPartLimit (b : MatrixPolarBlowupData M D x) : EuclideanSpace ℝ (Fin d) → ℝ :=
  signedConvolution (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure
      (besselKernel d) -
    ∑ a : Fin d, signedConvolution (b.regularRemainderLimit a) (besselPartial d a)

/--
Convergence of zₙ dx to w, expressed with the current of the signed measure associated with w.
-/
theorem mollifiedPositive_signed_test_tendsto (b : MatrixPolarBlowupData M D x)
    (φ : ScalarCurrentTest d) :
    Tendsto (fun n => ∫ y, φ y * b.mollifiedPositive n y) atTop
      (𝓝 (signedTestCurrent (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure φ)) := by
  rw [signedTestCurrent_toSignedMeasure]
  exact b.mollifiedPositive_test_tendsto φ

/-- Convergence of gₙ,ₐ dx to Gₐ = ν ∂ₐχ on all smooth tests (same diagonal index). -/
theorem mollifiedRemainder_test_tendsto (b : MatrixPolarBlowupData M D x) (a : Fin d)
    (φ : ScalarCurrentTest d) :
    Tendsto (fun n => ∫ y, φ y * b.mollifiedRemainder n a y) atTop
      (𝓝 (signedTestCurrent (b.regularRemainderLimit a) φ)) := by
  obtain ⟨C, hC⟩ := b.localizedRemainder_uniform_bound a
  exact KernelCompactness.signed_variable_mollifier_test_tendsto (fun n => b.localizedRemainder n a)
    (b.regularRemainderLimit a) (fun ψ => b.localizedRemainder_test_tendsto a ψ)
    b.localizationMollifierIndex b.localizationMollifierIndex_spec.2.2.1 C hC φ

/--
The regular resolvent terms B ∗ zₙ − Σₐ Bₐ ∗ gₙ,ₐ converge in L¹ to h = B ∗ w − Σₐ Bₐ ∗ Gₐ for the
given blow-up data and its diagonal sequence. References: De Philippis–Rindler, arXiv p. 9, (2.10),
and Lemma 2.1, specialized to the convolution kernels.
-/
theorem regularPart_l1_tendsto (b : MatrixPolarBlowupData M D x) :
    Integrable b.regularPartLimit ∧
    Tendsto (fun n => ∫ y, ‖resolventRegular (b.mollifiedPositiveTest n)
      (b.mollifiedRemainderTest n) y - b.regularPartLimit y‖) atTop (𝓝 0) := by
  have hP := KernelCompactness.kernel_l1_tendsto_of_test_tendsto (integrable_besselKernel d)
    (fun n => b.mollifiedPositiveTest n) 2 1 (fun n => (b.mollified_common_support n).1)
    (fun n => b.mollifiedPositiveTest_L1_le_one n)
    (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure
    (fun φ => b.mollifiedPositive_signed_test_tendsto φ)
  have hQ : ∀ a : Fin d,
      Integrable (signedConvolution (b.regularRemainderLimit a) (besselPartial d a)) ∧
      Tendsto (fun n => ∫ y, ‖scalarConvolution (besselPartial d a) (b.mollifiedRemainderTest n a) y -
        signedConvolution (b.regularRemainderLimit a) (besselPartial d a) y‖) atTop (𝓝 0) := by
    intro a
    obtain ⟨C, hC⟩ := b.mollifiedRemainder_L1_bounded a
    exact KernelCompactness.kernel_l1_tendsto_of_test_tendsto (integrable_besselPartial a)
      (fun n => b.mollifiedRemainderTest n a) 2 C (fun n => ((b.mollified_common_support n).2 a).2)
      hC (b.regularRemainderLimit a) (fun φ => b.mollifiedRemainder_test_tendsto a φ)
  have hint : Integrable b.regularPartLimit :=
    hP.1.sub (integrable_finsetSum' _ (fun a _ => (hQ a).1))
  refine ⟨hint, ?_⟩
  let P : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n y =>
    scalarConvolution (besselKernel d) (b.mollifiedPositiveTest n) y -
      signedConvolution (b.localizedTangent : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure
        (besselKernel d) y
  let Q : ℕ → Fin d → EuclideanSpace ℝ (Fin d) → ℝ := fun n a y =>
    scalarConvolution (besselPartial d a) (b.mollifiedRemainderTest n a) y -
      signedConvolution (b.regularRemainderLimit a) (besselPartial d a) y
  have iP : ∀ n, Integrable (P n) := fun n =>
    (integrable_scalarConvolution (integrable_besselKernel d) (scalarTest_integrable _)).sub hP.1
  have iQ : ∀ n a, Integrable (Q n a) := fun n a =>
    (integrable_scalarConvolution (integrable_besselPartial a) (scalarTest_integrable _)).sub (hQ a).1
  have hpt : ∀ n y, ‖resolventRegular (b.mollifiedPositiveTest n) (b.mollifiedRemainderTest n) y -
      b.regularPartLimit y‖ ≤ ‖P n y‖ + ∑ a : Fin d, ‖Q n a y‖ := by
    intro n y
    have heq : resolventRegular (b.mollifiedPositiveTest n) (b.mollifiedRemainderTest n) y -
        b.regularPartLimit y = P n y - ∑ a : Fin d, Q n a y := by
      simp only [resolventRegular, regularPartLimit, Pi.sub_apply, Finset.sum_apply, P, Q,
        Finset.sum_sub_distrib]
      ring
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
  have hbound : ∀ n, (∫ y, ‖resolventRegular (b.mollifiedPositiveTest n)
      (b.mollifiedRemainderTest n) y - b.regularPartLimit y‖) ≤
      (∫ y, ‖P n y‖) + ∑ a : Fin d, ∫ y, ‖Q n a y‖ := by
    intro n
    calc (∫ y, ‖resolventRegular (b.mollifiedPositiveTest n)
          (b.mollifiedRemainderTest n) y - b.regularPartLimit y‖) ≤
        ∫ y, (‖P n y‖ + ∑ a : Fin d, ‖Q n a y‖) :=
          integral_mono ((integrable_resolventRegular _ _).sub hint).norm
            ((iP n).norm.add (integrable_finsetSum _ (fun a _ => (iQ n a).norm))) (hpt n)
      _ = (∫ y, ‖P n y‖) + ∑ a : Fin d, ∫ y, ‖Q n a y‖ := by
          rw [integral_add (iP n).norm (integrable_finsetSum _ (fun a _ => (iQ n a).norm)),
            integral_finsetSum _ (fun a _ => (iQ n a).norm)]
  have hlim : Tendsto (fun n => (∫ y, ‖P n y‖) + ∑ a : Fin d, ∫ y, ‖Q n a y‖) atTop (𝓝 0) := by
    have h := hP.2.add (tendsto_finsetSum (Finset.univ : Finset (Fin d)) (fun a _ => (hQ a).2))
    simpa only [Finset.sum_const_zero, add_zero] using h
  exact squeeze_zero (fun n => integral_nonneg (fun _ => norm_nonneg _)) hbound hlim

end MatrixPolarBlowupData
end GeometricMeasure

namespace GeometricMeasure
namespace MatrixPolarBlowupData
variable {d : ℕ} {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}

/--
The explicit function B ∗ w − Σₐ Bₐ ∗ Gₐ satisfies `RegularPartL1Limit` for every matrix polar
blow-up datum.
-/
theorem regularPartL1Limit_holds (b : MatrixPolarBlowupData M D x) :
    b.RegularPartL1Limit b.regularPartLimit :=
  b.regularPart_l1_tendsto

/-- Existential form of the connection. -/
theorem exists_regularPartL1Limit (b : MatrixPolarBlowupData M D x) :
    ∃ h : EuclideanSpace ℝ (Fin d) → ℝ, b.RegularPartL1Limit h :=
  ⟨b.regularPartLimit, b.regularPartL1Limit_holds⟩

end MatrixPolarBlowupData
end GeometricMeasure
