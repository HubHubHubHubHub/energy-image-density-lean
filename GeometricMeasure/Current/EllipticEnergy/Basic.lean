import GeometricMeasure.Analysis.EllipticEnergy
import GeometricMeasure.Current.TruncatedBessel.Basic

/-!
# Integration by parts and elliptic energy estimates

This file contains the results of the development of `GeometricMeasure.Current.EllipticEnergy` that
the main statements of the library (the head theorems listed in the README of the repository) use.
`GeometricMeasure.Current.EllipticEnergy` imports it and continues the development.

## Main statements

* `l2EnergyData_test`: Concrete energy instance: every compactly supported C∞ test, in every
  dimension.
* `truncatedSecondTest_L2`: For `η > 0`, the L² norm of `truncatedSecondTest η a b u` is at most
  `Real.exp (-η)` times the L² norm of the test `u`.
* `exists_test_sq_sub_le`: Density of compactly supported C∞ tests in L² (Mathlib
  `MemLp.exist_eLpNorm_sub_le`), expressed in real integrals.

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
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem coordDeriv_test (a : Fin d) (u : ScalarCurrentTest d) :
    coordDeriv a u = (cutoffPartialTest u a : EuclideanSpace ℝ (Fin d) → ℝ) := by
  funext x
  exact (cutoffPartialTest_apply u a x).symm

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem scalarTest_memLp_two (u : ScalarCurrentTest d) :
    MemLp (u : EuclideanSpace ℝ (Fin d) → ℝ) 2 :=
  u.continuous.memLp_of_hasCompactSupport u.hasCompactSupport

/--
Concrete energy instance: every compactly supported C∞ test, in every dimension. Source: DPR
context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem l2EnergyData_test (u : ScalarCurrentTest d) : L2EnergyData u where
  smooth := u.contDiff.of_le (by decide)
  l2 := scalarTest_memLp_two u
  first a := by rw [coordDeriv_test]; exact scalarTest_memLp_two _
  second a b := by rw [coordDeriv_test, coordDeriv_test]; exact scalarTest_memLp_two _
  third a b c := by rw [coordDeriv_test, coordDeriv_test, coordDeriv_test]; exact scalarTest_memLp_two _

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem scalarConvolution_test_memLp_two {K : EuclideanSpace ℝ (Fin d) → ℝ}
    (hK : Integrable K) (u : ScalarCurrentTest d) : MemLp (scalarConvolution K u) 2 :=
  memLp_two_of_integrable_bound (integrable_scalarConvolution hK (scalarTest_integrable u))
    (norm_scalarConvolution_test_le hK u)

/--
Spatial differentiation of convolution on the test factor. Source: DPR context, transcription pp.
9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem coordDeriv_convolution_test {K : EuclideanSpace ℝ (Fin d) → ℝ}
    (hK : Integrable K) (u : ScalarCurrentTest d) (a : Fin d) :
    coordDeriv a (scalarConvolution K u) = scalarConvolution K (cutoffPartialTest u a) := by
  funext x
  have hs : ContDiff ℝ 1 (u : EuclideanSpace ℝ (Fin d) → ℝ) := u.contDiff.of_le (by simp)
  have h := u.hasCompactSupport.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hK.locallyIntegrable hs x
  change (fderiv ℝ (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u) x) (EuclideanSpace.single a 1) = _
  rw [h.fderiv, convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ)
    hK.locallyIntegrable (u.hasCompactSupport.fderiv ℝ) (hs.continuous_fderiv (by norm_num))]
  change scalarConvolution K (coordDeriv a u) x = _
  rw [coordDeriv_test]

/--
Regularity and L² membership of all required derivatives of K*u, K∈L¹. Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem l2EnergyData_convolution_test {K : EuclideanSpace ℝ (Fin d) → ℝ}
    (hK : Integrable K) (u : ScalarCurrentTest d) : L2EnergyData (scalarConvolution K u) where
  smooth := u.hasCompactSupport.contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hK.locallyIntegrable (u.contDiff.of_le (by exact_mod_cast (show (3 : ℕ∞) ≤ ⊤ from le_top)))
  l2 := scalarConvolution_test_memLp_two hK u
  first a := by rw [coordDeriv_convolution_test hK]; exact scalarConvolution_test_memLp_two hK _
  second a b := by
    rw [coordDeriv_convolution_test hK, coordDeriv_convolution_test hK]
    exact scalarConvolution_test_memLp_two hK _
  third a b c := by
    rw [coordDeriv_convolution_test hK, coordDeriv_convolution_test hK, coordDeriv_convolution_test hK]
    exact scalarConvolution_test_memLp_two hK _

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem laplacian_convolution_test {K : EuclideanSpace ℝ (Fin d) → ℝ}
    (hK : Integrable K) (u : ScalarCurrentTest d) :
    euclLaplacian (scalarConvolution K u) = scalarConvolution K (scalarTestLaplacian u) := by
  have h (a : Fin d) : coordDeriv a (coordDeriv a (scalarConvolution K u)) =
      scalarConvolution K (cutoffPartialTest (cutoffPartialTest u a) a) := by
    rw [coordDeriv_convolution_test hK, coordDeriv_convolution_test hK]
  funext x
  change (∑ a : Fin d, coordDeriv a (coordDeriv a (scalarConvolution K u)) x) =
    scalarConvolutionTest K hK (scalarTestLaplacian u) x
  simp only [h, scalarTestLaplacian, map_sum, Finset.sum_apply]
  rfl

/--
actual L² bound for every test input at η > 0. Source: DPR context, transcription pp. 9–10. Exact
scope: parameters, assumptions and conclusion below.
-/
theorem truncatedSecondTest_L2_sq {η : ℝ} (hη : 0 < η)
    (a b : Fin d) (u : ScalarCurrentTest d) :
    (∫ x, truncatedSecondTest η a b u x ^ 2) ≤
      (Real.exp (-η)) ^ 2 * ∫ x, u x ^ 2 := by
  have hK := integrable_truncatedBessel d hη.le
  have he := l2Sq_coordDeriv_le (l2EnergyData_convolution_test hK u) a b
  rw [coordDeriv_convolution_test hK, coordDeriv_convolution_test hK] at he
  have hr : (fun x => scalarConvolution (truncatedBessel d η) u x -
      euclLaplacian (scalarConvolution (truncatedBessel d η) u) x) =
      fun x => Real.exp (-η) * scalarConvolution (heatKernel d η) u x := by
    rw [laplacian_convolution_test hK]
    funext x
    have hh := truncatedBessel_resolves_test hη u x
    change scalarConvolutionTest (truncatedBessel d η) hK (u - scalarTestLaplacian u) x = _ at hh
    simp only [map_sub, Pi.sub_apply] at hh
    exact hh
  rw [hr] at he
  change (∫ x, truncatedSecondTest η a b u x ^ 2) ≤
    ∫ x, (Real.exp (-η) * scalarConvolution (heatKernel d η) u x) ^ 2 at he
  simp_rw [mul_pow, integral_const_mul] at he
  exact he.trans (mul_le_mul_of_nonneg_left
    (heatKernel_convolution_L2 hη (scalarTest_integrable u) (scalarTest_memLp_two u)).2
    (sq_nonneg _))

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem truncatedSecondTest_L2 {η : ℝ} (hη : 0 < η)
    (a b : Fin d) (u : ScalarCurrentTest d) :
    Real.sqrt (∫ x, truncatedSecondTest η a b u x ^ 2) ≤
      Real.exp (-η) * Real.sqrt (∫ x, u x ^ 2) := by
  have h := Real.sqrt_le_sqrt (truncatedSecondTest_L2_sq hη a b u)
  simpa only [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le] using h

/--
Density of compactly supported C∞ tests in L² (Mathlib `MemLp.exist_eLpNorm_sub_le`), expressed in
real integrals. Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions
and conclusion below.
-/
theorem exists_test_sq_sub_le {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : MemLp f 2)
    {ε : ℝ} (hε : 0 < ε) : ∃ u : ScalarCurrentTest d, (∫ x, (f x - u x) ^ 2) ≤ ε ^ 2 := by
  obtain ⟨g, hg1, hg2, hg3⟩ := hf.exist_eLpNorm_sub_le (μ := volume) (by norm_num)
    (by norm_num) hε
  let u : ScalarCurrentTest d :=
    { toFun := g, contDiff' := hg2, hasCompactSupport' := hg1,
      tsupport_subset' := subset_univ _ }
  have hux : ∀ x, u x = g x := fun _ => rfl
  refine ⟨u, ?_⟩
  have hgm : MemLp g 2 := hg2.continuous.memLp_of_hasCompactSupport hg1
  have hm : MemLp (f - g) 2 := hf.sub hgm
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.ofReal_le_ofReal_iff hε.le] at hg3
  have hI : (∫ x, ‖(f - g) x‖ ^ (2 : ENNReal).toReal) = ∫ x, (f x - u x) ^ 2 := by
    congr 1
    ext x
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Pi.sub_apply, Real.norm_eq_abs, sq_abs, hux]
  rw [hI] at hg3
  have hnn : 0 ≤ ∫ x, (f x - u x) ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hs : (∫ x, (f x - u x) ^ 2) ^ ((2 : ENNReal).toReal)⁻¹ =
      Real.sqrt (∫ x, (f x - u x) ^ 2) := by
    rw [Real.sqrt_eq_rpow, ENNReal.toReal_ofNat, one_div]
  rw [hs] at hg3
  calc (∫ x, (f x - u x) ^ 2) = Real.sqrt (∫ x, (f x - u x) ^ 2) ^ 2 :=
        (Real.sq_sqrt hnn).symm
    _ ≤ ε ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hg3 2

end GeometricMeasure
