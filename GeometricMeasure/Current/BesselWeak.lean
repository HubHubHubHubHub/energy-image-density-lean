import GeometricMeasure.Analysis.CalderonZygmundWeak
import GeometricMeasure.Current.TruncatedKernelCZ

/-!
# Uniform weak estimates for truncated Bessel kernels

## Main results
The truncated kernels and the operators S_ab on tests satisfy a weak (1,1) bound independent of
positive time and of the indices. Integration by parts on tests yields integrability, zero mean and
distributional estimates without differentiating the Bessel kernel.

Reference: De Philippis–Rindler, pp. 9–10, (2.9)–(2.12).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Convolution

namespace GeometricMeasure
open CalderonZygmund
variable {d : ℕ}

/--
The uniform constant determined by the L² and Hörmander estimates. Source: DPR, local transcription
pp. 9–10 (context).
-/
def besselWeakConstant (d : ℕ) : ℝ := weakConstant d 1 (hormanderConstant d)

/--
Nonnegativity of the uniform constant in every dimension. Source: DPR, local transcription pp. 9–10
(context).
-/
theorem besselWeakConstant_nonneg (d : ℕ) : 0 ≤ besselWeakConstant d := by
  unfold besselWeakConstant weakConstant hormanderConstant
  positivity

/--
The weak convolution criterion applied to Kη on all L¹ inputs, uniformly for η>0. Source: DPR, local
transcription pp. 9–10 (context).
-/
theorem truncatedSecondKernel_weak11 {η : ℝ} (hη : 0 < η) (a b : Fin d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Integrable f) {lam : ℝ} (hlam : 0 < lam) :
    volume {x | lam < ‖scalarConvolution (truncatedSecondKernel η a b) f x‖} ≤
      ENNReal.ofReal (besselWeakConstant d * (∫ x, ‖f x‖) / lam) := by
  obtain ⟨hk, hk1, hkB, hL2, hH⟩ := truncatedSecondKernel_cz_hypotheses hη a b
  apply convolution_weak11 (by have := a.isLt; omega : 1 ≤ d) hk hk1 hkB (by norm_num)
    (show 0 ≤ hormanderConstant d by unfold hormanderConstant; positivity)
    (fun g hg hg2 => ?_) hH hf hlam
  simpa only [one_pow, one_mul] using hL2 g hg hg2

end GeometricMeasure

namespace GeometricMeasure
variable {d : ℕ}

/--
Passage to the pointwise limit with the same constant, via tail intersections. Source: DPR, local
transcription pp. 9–10 (context).
-/
theorem weak11_measure_level_le_of_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {q : α → ℝ} {lam : ℝ} {C : ℝ≥0∞}
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (q x)))
    (hb : ∀ n, μ {x | lam < ‖F n x‖} ≤ C) :
    μ {x | lam < ‖q x‖} ≤ C := by
  let E : ℕ → Set α := fun n => ⋂ m ≥ n, {x | lam < ‖F m x‖}
  have hm : Monotone E := by
    intro n m hnm x hx
    simp only [E, mem_iInter, mem_setOf_eq] at *
    exact fun j hj => hx j (hnm.trans hj)
  have hs : {x | lam < ‖q x‖} ⊆ ⋃ n, E n := by
    intro x hx
    have he := ((hlim x).norm).eventually (eventually_gt_nhds hx)
    obtain ⟨n, hn⟩ := eventually_atTop.1 he
    exact mem_iUnion.2 ⟨n, by simpa only [E, mem_iInter, mem_setOf_eq] using hn⟩
  apply (measure_mono hs).trans
  rw [hm.measure_iUnion]
  apply iSup_le
  intro n
  apply (measure_mono ?_).trans (hb n)
  intro x hx
  simp only [E, mem_iInter, mem_setOf_eq] at hx
  exact hx n le_rfl

/--
weak (1,1) bound for S_ab on tests, without loss in the constant. Source: DPR, local transcription
pp. 9–10 (context).
-/
theorem besselSecond_weak11 (a b : Fin d) (u : ScalarCurrentTest d)
    {lam : ℝ} (hlam : 0 < lam) :
    volume {x | lam < ‖besselSecond a b u x‖} ≤
      ENNReal.ofReal (besselWeakConstant d * (∫ x, ‖u x‖) / lam) := by
  have hη : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n => by change 0 < 1 / ((n : ℝ) + 1); positivity)⟩
  apply weak11_measure_level_le_of_tendsto
    (fun x => (truncatedSecondKernel_tendsto a b u x).comp hη)
  intro n
  exact truncatedSecondKernel_weak11 (by positivity) a b (scalarTest_integrable u) hlam

/--
One integration by parts on the smooth factor of an L¹ convolution. Source: DPR, local transcription
pp. 9–10 (context).
-/
theorem integral_convolution_partial_test {K : EuclideanSpace ℝ (Fin d) → ℝ}
    (hK : Integrable K) (u φ : ScalarCurrentTest d) (a : Fin d) :
    (∫ x, scalarConvolution K (cutoffPartialTest u a) x * φ x) =
      - ∫ x, scalarConvolution K u x * cutoffPartialTest φ a x := by
  have hv := l2EnergyData_convolution_test hK u
  have hφ := l2EnergyData_test φ
  have h := integral_coordDeriv_mul (hv.smooth.of_le (by norm_num))
    (φ.contDiff.of_le (by simp)) a hv.l2 hφ.l2 (hv.first a) (hφ.first a)
  simpa only [coordDeriv_convolution_test hK, coordDeriv_test] using h

/--
Commutation of mixed derivatives on tests; connection between the two orders of writing them.
Source: DPR, local transcription pp. 9–10 (context).
-/
theorem cutoffPartialTest_commute (u : ScalarCurrentTest d) (a b : Fin d) :
    cutoffPartialTest (cutoffPartialTest u b) a = cutoffPartialTest (cutoffPartialTest u a) b := by
  have h := coordDeriv_comm ((l2EnergyData_test u).smooth.of_le (by norm_num)) a b
  ext x
  simpa only [coordDeriv_test] using congrFun h x

/--
Two integrations by parts; the reversed derivative order is displayed explicitly. Source: DPR, local
transcription pp. 9–10 (context).
-/
theorem besselSecond_pairing (a b : Fin d) (u φ : ScalarCurrentTest d) :
    (∫ x, besselSecond a b u x * φ x) =
      ∫ x, scalarConvolution (besselKernel d) u x *
        cutoffPartialTest (cutoffPartialTest φ a) b x := by
  unfold besselSecond
  rw [integral_convolution_partial_test (integrable_besselKernel d),
    integral_convolution_partial_test (integrable_besselKernel d), neg_neg]

/-- L¹ bound against a bounded test. Source: DPR, local transcription pp. 9–10 (context). -/
theorem norm_integral_mul_test_le {q : EuclideanSpace ℝ (Fin d) → ℝ}
    (hq : Integrable q) (φ : ScalarCurrentTest d) :
    ‖∫ x, q x * φ x‖ ≤ (∫ x, ‖q x‖) *
      ‖(φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ := by
  calc _ ≤ ∫ x, ‖q x * φ x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖q x‖ * ‖(φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ := by
      apply integral_mono (integrable_mul_scalarTest hq φ).norm (hq.norm.mul_const _)
      intro x
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        ((φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm x)
        (norm_nonneg _)
    _ = _ := integral_mul_const _ _

/--
test estimate, without a norm of the input's derivatives. Source: DPR, local transcription pp. 9–10
(context).
-/
theorem besselSecond_pairing_bound (a b : Fin d) (u φ : ScalarCurrentTest d) :
    ‖∫ x, besselSecond a b u x * φ x‖ ≤ (∫ x, ‖u x‖) *
      ‖(cutoffPartialTest (cutoffPartialTest φ a) b :
        BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ := by
  rw [besselSecond_pairing]
  apply (norm_integral_mul_test_le
    (integrable_scalarConvolution (integrable_besselKernel d) (scalarTest_integrable u)) _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [integral_norm_besselKernel, one_mul] using
    integral_norm_scalarConvolution_le (integrable_besselKernel d) (scalarTest_integrable u)

/-- integrability, cancellation and tests. Source: DPR, local transcription pp. 9–10 (context). -/
theorem besselSecond_integral_test_package (a b : Fin d) (u : ScalarCurrentTest d) :
    Integrable (besselSecond a b u) ∧ (∫ x, besselSecond a b u x) = 0 ∧
    ∀ φ : ScalarCurrentTest d, ‖∫ x, besselSecond a b u x * φ x‖ ≤
      (∫ x, ‖u x‖) * ‖(cutoffPartialTest (cutoffPartialTest φ a) b :
        BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ :=
  ⟨integrable_besselSecond a b u, integral_besselSecond a b u,
    besselSecond_pairing_bound a b u⟩

end GeometricMeasure
