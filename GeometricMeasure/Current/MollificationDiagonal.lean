import GeometricMeasure.VectorMeasure.MeasureConvolution
import GeometricMeasure.Current.Compactness
import GeometricMeasure.Current.LinearCombinations

/-!
# Mollification Diagonal

## Main results
Approximation of the identity and diagonal selection for actual convolutions. Source: DPR arXiv, p.
8, (2.5). Semicontinuity is applied on smooth compactly supported tests; no density of the limit is
assumed. Signed variation is Jordan variation, without a factor 1/2. The density lemmas are placed
here because their reference proofs use the current mass formula.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology Convolution
namespace GeometricMeasure
variable {d m : ℕ}

/-- DPR arXiv, p. 8 (2.5). Finite-valued selection from a lower semicontinuity inequality. -/
theorem exists_index_tv_approx (a : ℝ≥0∞) (_ha : a ≠ ⊤) (u : ℕ → ℝ≥0∞)
    (hu : ∀ k, u k ≠ ⊤) (hl : a ≤ liminf u atTop) {δ : ℝ} (hδ : 0 < δ)
    (j : ℕ) : ∃ k, j ≤ k ∧ a.toReal ≤ (u k).toReal + δ := by
  by_cases hsmall : a.toReal ≤ δ
  · exact ⟨j, le_rfl, hsmall.trans (le_add_of_nonneg_left ENNReal.toReal_nonneg)⟩
  have hpos : 0 ≤ a.toReal - δ := by linarith
  by_contra h
  have hb : ∀ᶠ k in atTop, u k ≤ ENNReal.ofReal (a.toReal - δ) := by
    filter_upwards [eventually_ge_atTop j] with k hk
    have hn : ¬ a.toReal ≤ (u k).toReal + δ := fun hn => h ⟨k, hk, hn⟩
    rw [← ENNReal.ofReal_toReal (hu k)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hh := hl.trans (liminf_le_of_frequently_le hb.frequently)
  have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal hpos] at hh'
  linarith

/--
DPR arXiv, p. 8 (2.5). Diagonal selection for actual signed measures; the sole analytic hypothesis
is test convergence of the differences. This theorem does not assert that a convolution has that
property.
-/
theorem signed_tv_diagonal {d : ℕ}
    (D : ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (A : ℕ → ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hweak : ∀ j, ∀ φ : ScalarCurrentTest d,
      Tendsto (fun k => signedTestCurrent (A j k) φ) atTop (𝓝 (signedTestCurrent (D j) φ)))
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) :
    ∃ k : ℕ → ℕ, (∀ j, j ≤ k j) ∧
      ∀ j, (D j).totalVariation.real univ ≤ (A j (k j)).totalVariation.real univ + δ j := by
  have hf (S : SignedMeasure (EuclideanSpace ℝ (Fin d))) : S.totalVariation univ ≠ ⊤ := by
    haveI : IsFiniteMeasure S.totalVariation := by
      unfold SignedMeasure.totalVariation
      infer_instance
    exact measure_ne_top _ _
  have hex (j : ℕ) := exists_index_tv_approx ((D j).totalVariation univ) (hf (D j))
    (fun k => (A j k).totalVariation univ) (fun k => hf (A j k))
    (totalVariation_le_liminf_of_scalarTest_tendsto (A j) (D j) (hweak j) isOpen_univ)
    (hδ j) j
  choose k hk ht using hex
  exact ⟨k, hk, ht⟩

/--
DPR arXiv, p. 8 (2.5). Diagonal tolerance and kernel radius, both equal to 1/(j+1). The indexing
starts at j = 0.
-/
def diagonalError (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

/-- DPR arXiv, p. 8 (2.5). The tolerance and radius 1/(j+1) are strictly positive at each index. -/
theorem diagonalError_pos (j : ℕ) : 0 < diagonalError j := by
  unfold diagonalError
  positivity

/-- DPR arXiv, p. 8 (2.5). The tolerance and radius 1/(j+1) tend to zero. -/
theorem diagonalError_tendsto : Tendsto diagonalError atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/--
DPR arXiv, p. 8 (2.5). The selected scale still tends to zero, with any prescribed upper-bound
sequence.
-/
theorem diagonal_scale_tendsto (ε r : ℕ → ℝ)
    (hε : ∀ j, 0 ≤ ε j) (hbound : ∀ j, ε j ≤ r j)
    (hr : Tendsto r atTop (𝓝 0)) : Tendsto ε atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr hε hbound

/--
DPR arXiv, p. 8 (2.5). Once the smoothed distances tend to zero, the original distances do too.
-/
theorem tv_tendsto_of_diagonal (a b δ : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hab : ∀ j, a j ≤ b j + δ j)
    (hb : Tendsto b atTop (𝓝 0)) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  have h := hb.add hδ
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h ha hab

/--
DPR arXiv, p. 8 (2.5). Non-vacuous constant family for the analytic premise of the diagonal theorem.
-/
theorem signed_tv_diagonal_constant {d : ℕ}
    (D : ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d))) :
    ∃ k : ℕ → ℕ, (∀ j, j ≤ k j) ∧
      ∀ j, (D j).totalVariation.real univ ≤ (D j).totalVariation.real univ + diagonalError j := by
  exact signed_tv_diagonal D (fun j _ => D j) (fun _ _ => tendsto_const_nhds)
    diagonalError diagonalError_pos

/--
DPR arXiv, p. 9 (2.9). Pairing of an integrable signed density against a bounded continuous test,
via Jordan.
-/
theorem signedMeasurePairing_density
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Integrable f μ)
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) :
    signedMeasurePairing (μ.withDensityᵥ f) g = ∫ y, g y * f y ∂μ := by
  haveI := isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral
  haveI := isFiniteMeasure_withDensity_ofReal hf.neg.hasFiniteIntegral
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hf,
    signedMeasurePairing_sub]
  rw [integral_withDensity_eq_integral_toReal_smul₀
      (f := fun y => ENNReal.ofReal (f y)) hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul₀
      (f := fun y => ENNReal.ofReal (-f y)) hf.neg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  rw [← integral_sub]
  · apply integral_congr_ae
    filter_upwards with y
    simp only [← sub_mul, max_zero_sub_max_neg_zero_eq_self, mul_comm]
  · simpa only [mul_comm] using hf.pos_part.bdd_mul g.continuous.aestronglyMeasurable
      (Eventually.of_forall g.norm_coe_le_norm)
  · simpa only [Pi.neg_apply, mul_comm] using hf.neg.pos_part.bdd_mul g.continuous.aestronglyMeasurable
      (Eventually.of_forall g.norm_coe_le_norm)

/--
DPR arXiv, p. 9 (2.9). Global scalar variation bound, proved through the supremum over smooth
current tests.
-/
theorem signedDensity_tv_le
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Integrable f μ) :
    (SignedMeasure.totalVariation (μ.withDensityᵥ f)).real univ ≤ ∫ y, ‖f y‖ ∂μ := by
  have h : (SignedMeasure.totalVariation (μ.withDensityᵥ f)) univ ≤ ENNReal.ofReal (∫ y, ‖f y‖ ∂μ) := by
    rw [← signedTestCurrent_mass_eq_totalVariation _ isOpen_univ]
    apply testFunctionalMassOn_le
    intro φ _ hn
    rw [← signedMeasurePairing_currentTest, signedMeasurePairing_density μ f hf]
    apply ENNReal.ofReal_le_ofReal
    apply integral_mono
      (hf.bdd_mul φ.continuous.aestronglyMeasurable (Eventually.of_forall hn)) hf.norm
    intro y
    calc
      φ y * f y ≤ ‖φ y * f y‖ := le_abs_self _
      _ = ‖φ y‖ * ‖f y‖ := norm_mul _ _
      _ ≤ 1 * ‖f y‖ := mul_le_mul_of_nonneg_right (hn y) (norm_nonneg _)
      _ = _ := one_mul _
  simpa only [measureReal_def, ENNReal.toReal_ofReal (integral_nonneg (fun _ => norm_nonneg _))] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h

/--
DPR arXiv, p. 9 (2.9). Scalar density vanishes off K, hence its signed variation vanishes there.
-/
theorem signedDensity_support
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Integrable f μ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsClosed K)
    (hz : ∀ᵐ y ∂μ, y ∉ K → f y = 0) :
    (SignedMeasure.totalVariation (μ.withDensityᵥ f)) Kᶜ = 0 := by
  apply le_antisymm _ bot_le
  rw [← signedTestCurrent_mass_eq_totalVariation _ hK.isOpen_compl]
  apply testFunctionalMassOn_le
  intro φ hs _
  rw [← signedMeasurePairing_currentTest, signedMeasurePairing_density μ f hf]
  have heq : (∫ y, φ y * f y ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hz] with y hy
    by_cases h : y ∈ K
    · have hp : y ∉ tsupport φ := fun hp => hs hp h
      simp [image_eq_zero_of_notMem_tsupport hp]
    · simp [hy h]
  simp [heq]

/--
DPR arXiv, p. 8 (2.5). A concrete sequence of nonnegative smooth normalized kernels, of radius
1/(k+1).
-/
def standardMollifierBump (d k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) where
  rIn := diagonalError k / 2
  rOut := diagonalError k
  rIn_pos := half_pos (diagonalError_pos k)
  rIn_lt_rOut := half_lt_self (diagonalError_pos k)

/--
DPR arXiv, p. 8 (2.5). Smooth nonnegative normalized kernel obtained from the bump function of
radius 1/(k+1).
-/
def standardMollifier (d k : ℕ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  (standardMollifierBump d k).normed volume

/--
DPR arXiv, p. 8 (2.5). Nonnegativity, mass 1, smoothness, compact support and integrability of the
actual kernel, including in dimension zero.
-/
theorem standardMollifier_properties (d k : ℕ) :
    (∀ y, 0 ≤ standardMollifier d k y) ∧
    (∫ y, standardMollifier d k y) = 1 ∧
    ContDiff ℝ (⊤ : ℕ∞) (standardMollifier d k) ∧
    HasCompactSupport (standardMollifier d k) ∧
    Integrable (standardMollifier d k) :=
  ⟨(standardMollifierBump d k).nonneg_normed,
    (standardMollifierBump d k).integral_normed,
    (standardMollifierBump d k).contDiff_normed,
    (standardMollifierBump d k).hasCompactSupport_normed,
    (standardMollifierBump d k).integrable_normed⟩

/--
DPR arXiv, p. 8 (2.5). Actual weak convergence on every scalar current test for the mollified
positive measure.
-/
theorem standardMollifier_test_tendsto
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d))) (φ : ScalarCurrentTest d) :
    Tendsto (fun k => ∫ x, φ x * positiveConvolution μ (standardMollifier d k) x)
      atTop (𝓝 (∫ x, φ x ∂(μ : Measure (EuclideanSpace ℝ (Fin d))))) := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  have heq (k : ℕ) := positiveConvolution_pairing μ (standardMollifier d k)
    (standardMollifier_properties d k).2.2.2.2
    (standardMollifierBump d k).normed_neg (φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
  suffices h : Tendsto (fun k => ∫ y, convolution (standardMollifier d k) φ L volume y
      ∂(μ : Measure (EuclideanSpace ℝ (Fin d)))) atTop
      (𝓝 (∫ y, φ y ∂(μ : Measure (EuclideanSpace ℝ (Fin d))))) by
    apply h.congr'
    filter_upwards with k
    exact (heq k).symm
  apply tendsto_integral_of_dominated_convergence
    (fun _ => ‖(φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖)
  · intro k
    exact (φ.hasCompactSupport.continuous_convolution_right L
      (standardMollifier_properties d k).2.2.2.2.locallyIntegrable φ.continuous).aestronglyMeasurable
  · exact integrable_const _
  · intro k
    filter_upwards with y
    have hi := (standardMollifier_properties d k).2.2.2.2
    calc
      ‖convolution (standardMollifier d k) φ L volume y‖ ≤
          ∫ t, ‖standardMollifier d k t * φ (y - t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, standardMollifier d k t * ‖(φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ := by
        apply integral_mono
        · exact (φ.hasCompactSupport.convolutionExists_right L hi.locallyIntegrable φ.continuous y).norm
        · exact hi.mul_const _
        · intro t
          dsimp only
          rw [norm_mul, Real.norm_of_nonneg ((standardMollifier_properties d k).1 t)]
          exact mul_le_mul_of_nonneg_left
            ((φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm _) ((standardMollifier_properties d k).1 t)
      _ = _ := by rw [integral_mul_const, (standardMollifier_properties d k).2.1, one_mul]
  · filter_upwards with y
    exact (ContDiffBump.convolution_tendsto_right_of_continuous
      (φ := fun k => standardMollifierBump d k) diagonalError_tendsto φ.continuous y)

/--
DPR arXiv, p. 8 (2.5). Mollification of a positive measure, viewed as a signed measure: the real
density positiveConvolution with respect to volume. This name does not denote convolution of an
arbitrary signed measure.
-/
def signedMollification (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d))) (k : ℕ) :
    SignedMeasure (EuclideanSpace ℝ (Fin d)) :=
  volume.withDensityᵥ (positiveConvolution μ (standardMollifier d k))

/--
DPR arXiv, p. 8 (2.5). The current of a finite positive measure viewed as signed is its integral
against the test.
-/
theorem signedTestCurrent_toSignedMeasure
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] (φ : ScalarCurrentTest d) :
    signedTestCurrent μ.toSignedMeasure φ = ∫ y, φ y ∂μ := by
  have h := signedMeasurePairing_sub μ (0 : Measure (EuclideanSpace ℝ (Fin d)))
    (φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
  simp only [Measure.toSignedMeasure_zero, sub_zero, integral_zero_measure,
    signedMeasurePairing_currentTest] at h
  exact h

/--
DPR arXiv, p. 8 (2.5). The actual mollifications converge to the source on every smooth compactly
supported scalar test.
-/
theorem signedMollification_test_tendsto
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d))) (φ : ScalarCurrentTest d) :
    Tendsto (fun k => signedTestCurrent (signedMollification μ k) φ) atTop
      (𝓝 (signedTestCurrent (μ : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure φ)) := by
  rw [signedTestCurrent_toSignedMeasure]
  have h := standardMollifier_test_tendsto μ φ
  apply h.congr'
  filter_upwards with k
  rw [signedMollification, ← signedMeasurePairing_currentTest,
    signedMeasurePairing_density _ _ (positiveConvolution_integrable μ _
      (standardMollifier_properties d k).2.2.2.2)]
  rfl

/--
DPR arXiv, p. 8 (2.5). A diagonal sequence for the actual convolutions, without an
absolute-continuity assumption on w.
-/
theorem positive_mollification_tv_diagonal
    (μs : ℕ → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (w : FiniteMeasure (EuclideanSpace ℝ (Fin d))) :
    ∃ k : ℕ → ℕ, (∀ j, j ≤ k j) ∧
      (∀ j, 0 < diagonalError (k j) ∧ diagonalError (k j) ≤ diagonalError j) ∧
      Tendsto (fun j => diagonalError (k j)) atTop (𝓝 0) ∧
      ∀ j, ((μs j : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure -
          (w : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure).totalVariation.real univ ≤
        (signedMollification (μs j) (k j) -
          (w : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure).totalVariation.real univ + diagonalError j := by
  let D := fun j => (μs j : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure -
    (w : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure
  let A := fun j k => signedMollification (μs j) k -
    (w : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure
  have hw : ∀ j, ∀ φ : ScalarCurrentTest d,
      Tendsto (fun k => signedTestCurrent (A j k) φ) atTop (𝓝 (signedTestCurrent (D j) φ)) := by
    intro j φ
    simp only [A, D, sub_eq_add_neg, signedTestCurrent_add, signedTestCurrent_neg,
      add_apply, neg_apply]
    exact (signedMollification_test_tendsto (μs j) φ).add_const _
  obtain ⟨k, hk, ht⟩ := signed_tv_diagonal D A hw diagonalError diagonalError_pos
  have hb (j : ℕ) : diagonalError (k j) ≤ diagonalError j := by
    unfold diagonalError
    gcongr
    exact hk j
  exact ⟨k, hk, fun j => ⟨diagonalError_pos _, hb j⟩,
    diagonal_scale_tendsto _ _ (fun j => (diagonalError_pos _).le) hb diagonalError_tendsto, ht⟩

/--
DPR arXiv, p. 8 (2.5). Every smooth compactly supported scalar test is Lipschitz, with the uniform
norm of its derivative as constant.
-/
theorem scalarCurrentTest_lipschitz (φ : ScalarCurrentTest d) :
    LipschitzWith ‖(currentTestDerivative φ : BoundedCovectorField d d)‖₊ φ := by
  apply lipschitzWith_of_nnnorm_fderiv_le (φ.contDiff.differentiable (by simp))
  intro y
  exact_mod_cast (currentTestDerivative φ : BoundedCovectorField d d).norm_coe_le_norm y

/-- DPR arXiv, p. 8 (2.5). The uniform mollification error of a test is at most Lip(φ)/(k+1). -/
theorem mollifier_test_uniform_error (φ : ScalarCurrentTest d) (k : ℕ)
    (y : EuclideanSpace ℝ (Fin d)) :
    |convolution (standardMollifier d k) φ (ContinuousLinearMap.mul ℝ ℝ) volume y - φ y| ≤
      ‖(currentTestDerivative φ : BoundedCovectorField d d)‖ * diagonalError k := by
  have h := (standardMollifierBump d k).dist_normed_convolution_le (μ := volume)
    φ.continuous.aestronglyMeasurable (x₀ := y)
    (ε := ‖(currentTestDerivative φ : BoundedCovectorField d d)‖ * diagonalError k)
    (fun z hz => ((scalarCurrentTest_lipschitz φ).dist_le_mul z y).trans
      (mul_le_mul_of_nonneg_left (le_of_lt hz) (norm_nonneg _)))
  exact h

/-- DPR arXiv, p. 8 (2.5). Uniform, quantitative error against a smooth compact test. -/
theorem positive_mollifier_test_error
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d))) (φ : ScalarCurrentTest d) (k : ℕ) :
    |(∫ x, φ x * positiveConvolution μ (standardMollifier d k) x) -
      ∫ y, φ y ∂(μ : Measure (EuclideanSpace ℝ (Fin d)))| ≤
      (‖(currentTestDerivative φ : BoundedCovectorField d d)‖ * diagonalError k) *
        (μ : Measure (EuclideanSpace ℝ (Fin d))).real univ := by
  have heq := positiveConvolution_pairing μ _ (standardMollifier_properties d k).2.2.2.2
    (standardMollifierBump d k).normed_neg (φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
  change (∫ x, φ x * positiveConvolution μ (standardMollifier d k) x) =
    ∫ y, convolution (standardMollifier d k) φ (ContinuousLinearMap.mul ℝ ℝ) volume y
      ∂(μ : Measure (EuclideanSpace ℝ (Fin d))) at heq
  rw [heq]
  let f := convolution (standardMollifier d k) φ (ContinuousLinearMap.mul ℝ ℝ) volume
  have hc : Continuous f := φ.hasCompactSupport.continuous_convolution_right _
    (standardMollifier_properties d k).2.2.2.2.locallyIntegrable φ.continuous
  have hi : Integrable f (μ : Measure (EuclideanSpace ℝ (Fin d))) :=
    hc.integrable_of_hasCompactSupport ((standardMollifier_properties d k).2.2.2.1.convolution _ φ.hasCompactSupport)
  change |(∫ y, f y ∂(μ : Measure (EuclideanSpace ℝ (Fin d)))) - (∫ y, φ y ∂(μ : Measure (EuclideanSpace ℝ (Fin d))))| ≤ _
  rw [← integral_sub hi (φ.integrable (locallyIntegrableOn_const (1 : ℝ))), ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ (Fin d),
        ‖(currentTestDerivative φ : BoundedCovectorField d d)‖ * diagonalError k ∂(μ : Measure (EuclideanSpace ℝ (Fin d))) :=
      integral_mono (hi.sub (φ.integrable (locallyIntegrableOn_const (1 : ℝ)))).norm
        (integrable_const _) (fun y => mollifier_test_uniform_error φ k y)
    _ = _ := by simp [mul_comm]

/--
DPR arXiv, p. 8 (2.5). Variable scales preserve convergence on all smooth compact tests, for bounded
masses.
-/
theorem variable_mollifier_test_tendsto
    (μs : ℕ → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d))) (hμ : Tendsto μs atTop (𝓝 μ))
    (k : ℕ → ℕ) (hk : Tendsto (fun j => diagonalError (k j)) atTop (𝓝 0))
    (C : ℝ) (hC : ∀ j, (μs j : Measure (EuclideanSpace ℝ (Fin d))).real univ ≤ C)
    (φ : ScalarCurrentTest d) :
    Tendsto (fun j => ∫ y, φ y * positiveConvolution (μs j) (standardMollifier d (k j)) y)
      atTop (𝓝 (∫ y, φ y ∂(μ : Measure (EuclideanSpace ℝ (Fin d))))) := by
  have hbase := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
    (φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
  change Tendsto (fun j => ∫ y, φ y ∂(μs j : Measure (EuclideanSpace ℝ (Fin d)))) atTop
    (𝓝 (∫ y, φ y ∂(μ : Measure (EuclideanSpace ℝ (Fin d))))) at hbase
  have ht := (hk.const_mul ‖(currentTestDerivative φ : BoundedCovectorField d d)‖).mul_const C
  simp only [mul_zero, zero_mul] at ht
  have herr : Tendsto (fun j => (∫ y, φ y * positiveConvolution (μs j) (standardMollifier d (k j)) y) -
      ∫ y, φ y ∂(μs j : Measure (EuclideanSpace ℝ (Fin d)))) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ ht
    intro j
    rw [Real.norm_eq_abs]
    exact (positive_mollifier_test_error (μs j) φ (k j)).trans
      (mul_le_mul_of_nonneg_left (hC j) (mul_nonneg (norm_nonneg (currentTestDerivative φ : BoundedCovectorField d d)) (diagonalError_pos _).le))
  have hh := herr.add hbase
  simp only [zero_add, sub_add_cancel] at hh
  exact hh

/--
DPR arXiv, p. 8 (2.5). Standard normalized kernel viewed as a global smooth compactly supported
scalar test.
-/
def standardMollifierTest (d k : ℕ) : ScalarCurrentTest d where
  toFun := standardMollifier d k
  contDiff' := (standardMollifier_properties d k).2.2.1
  hasCompactSupport' := (standardMollifier_properties d k).2.2.2.1
  tsupport_subset' := subset_univ _

/--
DPR arXiv, p. 8 (2.5). All standard kernels have their topological support in the closed unit ball.
-/
theorem standardMollifier_support_unit (d k : ℕ) :
    tsupport (standardMollifier d k) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  rw [standardMollifier, ContDiffBump.tsupport_normed_eq]
  apply closedBall_subset_closedBall
  change 1 / ((k : ℝ) + 1) ≤ 1
  rw [div_le_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) k]

end GeometricMeasure
