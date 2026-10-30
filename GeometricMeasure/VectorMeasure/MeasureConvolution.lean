import GeometricMeasure.VectorMeasure.Polar
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Measure Convolution

## Main results
Actual positive, Euclidean vector and signed convolutions. Source: DPR arXiv, p. 8, (2.5). The
source measure need not be absolutely continuous. The L¹ bounds use Euclidean variation for vectors
and Jordan variation for signed measures. No direct or transitive import of Current.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology Convolution
namespace GeometricMeasure
variable {d m : ℕ}

/--
DPR arXiv, p. 8 (2.5). Convolution of a finite Euclidean vector measure, via its polar density.
-/
def measureConvolution
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) :=
  convolution (polarDensity N) ρ (ContinuousLinearMap.lsmul ℝ ℝ).flip N.variation

/--
DPR arXiv, p. 8 (2.5). Actual formula as the integral of the polar density and the reflected
translated kernel.
-/
theorem measureConvolution_apply
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    measureConvolution N ρ x = ∫ y, ρ (x - y) • polarDensity N y ∂N.variation := rfl

/-- DPR arXiv, p. 8 (2.5). A smooth compactly supported kernel gives a smooth vector convolution. -/
theorem measureConvolution_smooth
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) : ContDiff ℝ (⊤ : ℕ∞) (measureConvolution N ρ) :=
  hρc.contDiff_convolution_right _ (integrable_polarDensity N).locallyIntegrable hρ

/--
DPR arXiv, p. 8 (2.5). An integrable kernel gives a vector convolution integrable against volume.
-/
theorem measureConvolution_integrable
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : Integrable ρ) :
    Integrable (measureConvolution N ρ) :=
  ((integrable_polarDensity N).convolution_integrand
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hρ).integral_prod_left

/--
DPR arXiv, p. 8 (2.5). Young's inequality between two measures, with the Euclidean variation of the
vector measure; no matrix norm is introduced.
-/
theorem measureConvolution_norm_le
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : Integrable ρ) :
    (∫ x, ‖measureConvolution N ρ x‖) ≤
      N.variation.real univ * ∫ x, ‖ρ x‖ := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  have hi := (integrable_polarDensity N).norm
  have hc := (hi.convolution_integrand L hρ.norm).integral_prod_left
  calc
    _ ≤ ∫ x, convolution (fun y => ‖polarDensity N y‖) (fun y => ‖ρ y‖) L N.variation x := by
      apply integral_mono (measureConvolution_integrable N ρ hρ).norm hc
      intro x
      simpa [measureConvolution_apply, convolution, L, norm_smul, mul_comm] using
        norm_integral_le_integral_norm (fun y => ρ (x - y) • polarDensity N y) (μ := N.variation)
    _ = (∫ y, ‖polarDensity N y‖ ∂N.variation) * ∫ y, ‖ρ y‖ :=
      integral_convolution L hi hρ.norm
    _ = _ := by
      rw [integral_congr_ae (norm_polarDensity_ae N)]
      simp

/--
DPR arXiv, p. 8 (2.5). The L¹ norm of the convolution is at most the total Euclidean variation for a
nonnegative normalized kernel.
-/
theorem measureConvolution_norm_le_variation
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : Integrable ρ)
    (hρpos : ∀ x, 0 ≤ ρ x) (hρmass : ∫ x, ρ x = 1) :
    (∫ x, ‖measureConvolution N ρ x‖) ≤ N.variation.real univ := by
  have h := measureConvolution_norm_le N ρ hρ
  simpa only [Real.norm_of_nonneg (hρpos _), hρmass, mul_one] using h

/--
DPR arXiv, p. 8 (2.5). Positive scalar convolution; no density for the input measure is assumed.
-/
def positiveConvolution (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  convolution (fun _ => (1 : ℝ)) ρ (ContinuousLinearMap.mul ℝ ℝ) (μ : Measure (EuclideanSpace ℝ (Fin d)))

/--
DPR arXiv, p. 8 (2.5). Positive-measure convolution is the integral of the kernel against the source
measure.
-/
theorem positiveConvolution_apply (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    positiveConvolution μ ρ x = ∫ y, ρ (x - y) ∂(μ : Measure (EuclideanSpace ℝ (Fin d))) := by
  simp [positiveConvolution, convolution]

/--
DPR arXiv, p. 8 (2.5). Nonnegativity of convolution for a nonnegative kernel; no normalization is
required.
-/
theorem positiveConvolution_nonneg (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : ∀ x, 0 ≤ ρ x)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ positiveConvolution μ ρ x := by
  rw [positiveConvolution_apply]
  exact integral_nonneg (fun _ => hρ _)

/--
DPR arXiv, p. 8 (2.5). A smooth compactly supported kernel smooths every finite positive measure.
-/
theorem positiveConvolution_smooth (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) : ContDiff ℝ (⊤ : ℕ∞) (positiveConvolution μ ρ) :=
  hρc.contDiff_convolution_right _ (integrable_const (1 : ℝ)).locallyIntegrable hρ

/--
DPR arXiv, p. 8 (2.5). Integrability of convolution of a finite positive measure by an integrable
kernel.
-/
theorem positiveConvolution_integrable (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : Integrable ρ) :
    Integrable (positiveConvolution μ ρ) :=
  ((integrable_const (1 : ℝ) (μ := (μ : Measure (EuclideanSpace ℝ (Fin d))))).convolution_integrand
    (ContinuousLinearMap.mul ℝ ℝ) hρ).integral_prod_left

/-- DPR arXiv, p. 8 (2.5). Exact mass conservation for an integrable kernel of integral 1. -/
theorem positiveConvolution_mass (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : Integrable ρ)
    (hρmass : ∫ x, ρ x = 1) :
    (∫ x, positiveConvolution μ ρ x) = (μ : Measure (EuclideanSpace ℝ (Fin d))).real univ := by
  have h := integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_const (1 : ℝ) (μ := (μ : Measure (EuclideanSpace ℝ (Fin d))))) hρ
  simpa [hρmass, positiveConvolution] using h

/--
DPR arXiv, p. 8 (2.5). A support statement for convolution against an arbitrary measure, not only
Haar measure.
-/
theorem convolution_support_of_measure_support
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (p : EuclideanSpace ℝ (Fin d) → V) (ρ : EuclideanSpace ℝ (Fin d) → ℝ)
    (L : V →L[ℝ] ℝ →L[ℝ] W) (R r : ℝ)
    (hμ : μ (closedBall (0 : EuclideanSpace ℝ (Fin d)) R)ᶜ = 0)
    (hρ : tsupport ρ ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) r) :
    tsupport (convolution p ρ L μ) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + r) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra h
  have hz : convolution p ρ L μ x = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [mem_ae_iff.mpr hμ] with y hy
    have hxy : x - y ∉ closedBall (0 : EuclideanSpace ℝ (Fin d)) r := by
      intro hxy
      apply h
      simp only [mem_closedBall, dist_zero_right] at hy hxy ⊢
      have ht := norm_add_le (x - y) y
      rw [sub_add_cancel] at ht
      linarith
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hxy (hρ hs)), map_zero]
    rfl
  exact hx hz

/--
DPR arXiv, p. 8 (2.5). If the source variation is carried by B̄(0,R) and the kernel is supported in
B̄(0,r), the support of vector convolution is contained in B̄(0,R+r).
-/
theorem measureConvolution_support
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (R r : ℝ)
    (hN : N.variation (closedBall (0 : EuclideanSpace ℝ (Fin d)) R)ᶜ = 0)
    (hρ : tsupport ρ ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) r) :
    tsupport (measureConvolution N ρ) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + r) :=
  convolution_support_of_measure_support N.variation _ ρ _ R r hN hρ

/--
DPR arXiv, p. 8 (2.5). If the positive source measure is carried by B̄(0,R) and the kernel is
supported in B̄(0,r), the support of their convolution is contained in B̄(0,R+r).
-/
theorem positiveConvolution_support
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (R r : ℝ)
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin d))) (closedBall (0 : EuclideanSpace ℝ (Fin d)) R)ᶜ = 0)
    (hρ : tsupport ρ ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) r) :
    tsupport (positiveConvolution μ ρ) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + r) :=
  convolution_support_of_measure_support (μ : Measure (EuclideanSpace ℝ (Fin d))) _ ρ _ R r hμ hρ

/--
DPR arXiv, p. 8 (2.5). Scalar signed convolution in the Jordan representation used for the matrix
polar blow-up data.
-/
def signedConvolution (q : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  positiveConvolution ⟨q.toJordanDecomposition.posPart, inferInstance⟩ ρ -
    positiveConvolution ⟨q.toJordanDecomposition.negPart, inferInstance⟩ ρ

/--
DPR arXiv, p. 8 (2.5). Smoothness of signed convolution obtained by subtracting the two Jordan
parts.
-/
theorem signedConvolution_smooth (q : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) : ContDiff ℝ (⊤ : ℕ∞) (signedConvolution q ρ) :=
  (positiveConvolution_smooth _ ρ hρ hρc).sub (positiveConvolution_smooth _ ρ hρ hρc)

/-- DPR arXiv, p. 8 (2.5). Integrability of signed convolution by an integrable kernel. -/
theorem signedConvolution_integrable (q : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : Integrable ρ) :
    Integrable (signedConvolution q ρ) :=
  (positiveConvolution_integrable _ ρ hρ).sub (positiveConvolution_integrable _ ρ hρ)

/--
DPR arXiv, p. 8 (2.5). The L¹ norm of signed convolution is at most the source's Jordan
variation for a nonnegative normalized kernel.
-/
theorem signedConvolution_norm_le_variation (q : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : Integrable ρ)
    (hpos : ∀ y, 0 ≤ ρ y) (hmass : ∫ y, ρ y = 1) :
    (∫ y, ‖signedConvolution q ρ y‖) ≤ q.totalVariation.real univ := by
  let μp : FiniteMeasure (EuclideanSpace ℝ (Fin d)) := ⟨q.toJordanDecomposition.posPart, inferInstance⟩
  let μn : FiniteMeasure (EuclideanSpace ℝ (Fin d)) := ⟨q.toJordanDecomposition.negPart, inferInstance⟩
  have hp := positiveConvolution_integrable μp ρ hρ
  have hn := positiveConvolution_integrable μn ρ hρ
  calc
    _ ≤ ∫ y, positiveConvolution μp ρ y + positiveConvolution μn ρ y := by
      apply integral_mono (signedConvolution_integrable q ρ hρ).norm (hp.add hn)
      intro y
      exact (norm_sub_le _ _).trans_eq (by
        rw [Real.norm_of_nonneg (positiveConvolution_nonneg μp ρ hpos y),
          Real.norm_of_nonneg (positiveConvolution_nonneg μn ρ hpos y)]
        rfl)
    _ = (μp : Measure (EuclideanSpace ℝ (Fin d))).real univ +
        (μn : Measure (EuclideanSpace ℝ (Fin d))).real univ := by
      rw [integral_add hp hn, positiveConvolution_mass μp ρ hρ hmass,
        positiveConvolution_mass μn ρ hρ hmass]
    _ = _ := by
      simp only [SignedMeasure.totalVariation, measureReal_def, Measure.add_apply]
      exact (ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)).symm

/--
DPR arXiv, p. 8 (2.5). Signed convolution is supported in the closed ball of radius R+r, under both
support assumptions.
-/
theorem signedConvolution_support (q : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (R r : ℝ)
    (hq : q.totalVariation (closedBall (0 : EuclideanSpace ℝ (Fin d)) R)ᶜ = 0)
    (hρ : tsupport ρ ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) r) :
    tsupport (signedConvolution q ρ) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + r) := by
  rw [SignedMeasure.totalVariation, Measure.add_apply] at hq
  rcases add_eq_zero.mp hq with ⟨hp, hn⟩
  exact (tsupport_sub _ _).trans (union_subset
    (positiveConvolution_support ⟨q.toJordanDecomposition.posPart, inferInstance⟩ ρ R r hp hρ)
    (positiveConvolution_support ⟨q.toJordanDecomposition.negPart, inferInstance⟩ ρ R r hn hρ))

/--
DPR arXiv, p. 9 (2.9). Arbitrarily changing normalized nonnegative kernels preserve the vanishing L1
estimate.
-/
theorem measureConvolution_L1_tendsto_zero
    (Ns : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ρ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hρ : ∀ n, Integrable (ρ n)) (hpos : ∀ n y, 0 ≤ ρ n y)
    (hmass : ∀ n, ∫ y, ρ n y = 1)
    (hN : Tendsto (fun n => (Ns n).variation univ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, ‖measureConvolution (Ns n) (ρ n) y‖) atTop (𝓝 0) := by
  have hr : Tendsto (fun n => (Ns n).variation.real univ) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal (by simp)).comp hN
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr
    (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (fun n => measureConvolution_norm_le_variation (Ns n) (ρ n) (hρ n) (hpos n) (hmass n))

/--
DPR arXiv, p. 9 (2.9). A uniform variation bound controls all convolutions by nonnegative normalized
kernels.
-/
theorem measureConvolution_L1_uniform_bound
    (Ns : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ρ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hρ : ∀ n, Integrable (ρ n)) (hpos : ∀ n y, 0 ≤ ρ n y)
    (hmass : ∀ n, ∫ y, ρ n y = 1) (C : ℝ)
    (hN : ∀ n, (Ns n).variation.real univ ≤ C) :
    ∀ n, (∫ y, ‖measureConvolution (Ns n) (ρ n) y‖) ≤ C :=
  fun n => (measureConvolution_norm_le_variation (Ns n) (ρ n) (hρ n) (hpos n) (hmass n)).trans (hN n)

/--
DPR arXiv, p. 8 (2.5). Fubini adjoint formula for an even kernel and a bounded continuous scalar
test.
-/
theorem positiveConvolution_pairing
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : Integrable ρ)
    (heven : ∀ y, ρ (-y) = ρ y)
    (φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) :
    (∫ x, φ x * positiveConvolution μ ρ x) =
      ∫ y, convolution ρ φ (ContinuousLinearMap.mul ℝ ℝ) volume y ∂(μ : Measure (EuclideanSpace ℝ (Fin d))) := by
  have hi : Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ρ (p.1 - p.2)) (volume.prod (μ : Measure (EuclideanSpace ℝ (Fin d)))) := by
    simpa using (integrable_const (1 : ℝ) (μ := (μ : Measure (EuclideanSpace ℝ (Fin d))))).convolution_integrand
      (ContinuousLinearMap.mul ℝ ℝ) hρ
  have hi' := hi.bdd_mul (f := fun p => φ p.1)
    (φ.continuous.comp continuous_fst).aestronglyMeasurable
    (Eventually.of_forall (fun p => φ.norm_coe_le_norm p.1))
  simp only [positiveConvolution_apply, ← integral_const_mul]
  rw [integral_integral_swap hi']
  apply integral_congr_ae
  filter_upwards with y
  calc
    (∫ x, φ x * ρ (x - y)) = ∫ t, φ (y - t) * ρ ((y - t) - y) :=
      (integral_sub_left_eq_self (fun x => φ x * ρ (x - y)) volume y).symm
    _ = _ := by
      simp only [sub_sub_cancel_left, heven, convolution, ContinuousLinearMap.mul_apply', mul_comm]

end GeometricMeasure
