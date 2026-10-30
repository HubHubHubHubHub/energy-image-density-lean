import GeometricMeasure.Analysis.EllipticEnergy
import GeometricMeasure.Current.TruncatedBessel
import GeometricMeasure.Current.ZeroDimensionalHeat

/-!
# Elliptic Energy

## Main results
Global integration by parts under C¹ and four L² assumptions, energy under C³ and L² through order
three, Young and density. Realization on tests and their convolution, transferred L² bound; controls
and two counterexamples each isolating one assumption.

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
L² membership of the transferred operator for η ≥ 0, including η=0. Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem truncatedSecondTest_memLp_two {η : ℝ} (hη : 0 ≤ η)
    (a b : Fin d) (u : ScalarCurrentTest d) : MemLp (truncatedSecondTest η a b u) 2 :=
  scalarConvolution_test_memLp_two (integrable_truncatedBessel d hη) _

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

/--
Nonzero instance in positive dimension, beyond the case d=0. Source: DPR context, transcription pp.
9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem l2EnergyData_cutoff_one :
    L2EnergyData (interiorCutoffTest 1) ∧ interiorCutoffTest 1 0 = 1 := by
  constructor
  · exact l2EnergyData_test _
  · exact interiorCutoff_one (by norm_num [Metric.mem_closedBall])

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem l2EnergyData_zero (d : ℕ) :
    L2EnergyData (0 : EuclideanSpace ℝ (Fin d) → ℝ) := by
  simpa only [FunLike.coe_zero] using l2EnergyData_test (0 : ScalarCurrentTest d)

/--
At time zero, the L¹ error between the transferred operator and besselSecond is zero. Source: DPR
context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem truncatedSecondTest_zero_error (a b : Fin d) (u : ScalarCurrentTest d) :
    (∫ x, ‖truncatedSecondTest 0 a b u x - besselSecond a b u x‖) = 0 := by
  simp only [truncatedSecondTest_zero_time, sub_self, norm_zero, integral_zero]

/--
Non-vacuity of the potential in dimension zero. Source: DPR context, transcription pp. 9–10. Exact
scope: parameters, assumptions and conclusion below.
-/
theorem truncatedBessel_zero_dimension {η : ℝ} (hη : 0 ≤ η)
    (x : EuclideanSpace ℝ (Fin 0)) : truncatedBessel 0 η x = Real.exp (-η) := by
  unfold truncatedBessel
  calc
    _ = ∫ t in Ioi η, Real.exp (-t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [heatKernel_zero_dimension (lt_of_le_of_lt hη ht), mul_one]
    _ = _ := integral_exp_neg_Ioi η

/--
A single assumption removed: mass one in Young/Markov. All factors remain nonnegative, integrable
and L²; d=0 is allowed by this lemma. Source: DPR context, transcription pp. 9–10. Exact scope:
parameters, assumptions and conclusion below.
-/
theorem counterexample_markov_without_mass_one :
    let k : EuclideanSpace ℝ (Fin 0) → ℝ := fun _ => 2
    let f : EuclideanSpace ℝ (Fin 0) → ℝ := zeroDimTest 1
    Integrable k ∧ (∀ x, 0 ≤ k x) ∧ Integrable f ∧ MemLp f 2 ∧
      (∫ x, k x) = 2 ∧
      (∫ x, f x ^ 2) < ∫ x, scalarConvolution k f x ^ 2 := by
  dsimp only
  have hi : Integrable (fun _ : EuclideanSpace ℝ (Fin 0) => (1 : ℝ)) := by
    exact (integrable_heatKernel 0 1).congr
      (ae_of_all _ (fun x => heatKernel_zero_dimension one_pos x))
  have hm : (∫ _ : EuclideanSpace ℝ (Fin 0), (1 : ℝ)) = 1 := by
    simpa only [heatKernel_zero_dimension one_pos] using integral_heatKernel 0 one_pos
  have hk : Integrable (fun _ : EuclideanSpace ℝ (Fin 0) => (2 : ℝ)) := by
    simpa only [mul_one] using hi.const_mul 2
  have hc (x : EuclideanSpace ℝ (Fin 0)) :
      scalarConvolution (fun _ => (2 : ℝ)) (fun _ => (1 : ℝ)) x = 2 := by
    simp only [scalarConvolution_apply, mul_one]
    calc
      (∫ _ : EuclideanSpace ℝ (Fin 0), (2 : ℝ)) = 2 * (∫ _ : EuclideanSpace ℝ (Fin 0), (1 : ℝ)) := by
        simpa only [mul_one] using integral_const_mul (2 : ℝ) (fun _ : EuclideanSpace ℝ (Fin 0) => (1 : ℝ))
      _ = 2 := by rw [hm, mul_one]
  refine ⟨hk, fun _ => by norm_num, scalarTest_integrable _, scalarTest_memLp_two _, ?_, ?_⟩
  · simpa only [scalarConvolution_apply, mul_one] using hc 0
  · simp only [zeroDimTest, TestFunction.coe_mk, one_pow, hm, hc]
    have he : (∫ _ : EuclideanSpace ℝ (Fin 0), (2 : ℝ)^2) = 4 := by
      have h := integral_const_mul (μ := volume) (4 : ℝ) (fun _ : EuclideanSpace ℝ (Fin 0) => (1 : ℝ))
      simpa only [show (2 : ℝ)^2 = 4 by norm_num, mul_one, hm] using h
    rw [he]
    norm_num

end GeometricMeasure
