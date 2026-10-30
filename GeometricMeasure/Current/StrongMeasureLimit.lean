import GeometricMeasure.Current.BesselWeakPackage
import GeometricMeasure.Analysis.PositivityVitali

/-!
# Weak limits, densities and total variation convergence

## Main results
Uniqueness identifies the weak limit with its signed density. A stated total variation diagonal
bound then yields total variation convergence. Positivity and zero-mean estimates are specialized to
Euclidean balls; the density itself need not be assumed positive.

Reference: De Philippis–Rindler, arXiv p. 8, (2.3), (2.5).
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace GeometricMeasure.StrongConstancy
variable {d : ℕ}

/-- L¹ convergence implies convergence against every scalar current test. -/
theorem test_pairing_of_l1 {z : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hz : ∀ n, Integrable (z n)) (hh : Integrable h)
    (hc : Tendsto (fun n => ∫ x, ‖z n x - h x‖) atTop (𝓝 0))
    (φ : ScalarCurrentTest d) :
    Tendsto (fun n => ∫ x, φ x * z n x) atTop (𝓝 (∫ x, φ x * h x)) := by
  apply (tendsto_sub_nhds_zero_iff).1
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have he n : (∫ x, φ x * z n x) - (∫ x, φ x * h x) =
      ∫ x, (z n x - h x) * φ x := by
    rw [← integral_sub]
    · congr 1
      funext x
      ring
    · simpa only [mul_comm] using integrable_mul_scalarTest (hz n) φ
    · simpa only [mul_comm] using integrable_mul_scalarTest hh φ
  simp_rw [he]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_integral_mul_test_le ((hz n).sub hh) φ)
  simpa only [Pi.sub_apply, zero_mul] using hc.mul_const
    ‖(φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖

/--
Uniqueness of the smooth-test limit identifies the signed measure with the integrable density h.
Positivity of h is not assumed. Reference: De Philippis–Rindler, arXiv p. 8, (2.3).
-/
theorem density_of_test_limit {z : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hz : ∀ n, Integrable (z n)) (hh : Integrable h)
    (hc : Tendsto (fun n => ∫ x, ‖z n x - h x‖) atTop (𝓝 0))
    (w : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hw : ∀ φ : ScalarCurrentTest d,
      Tendsto (fun n => ∫ x, φ x * z n x) atTop (𝓝 (signedTestCurrent w φ))) :
    w = volume.withDensityᵥ h := by
  apply signedTestCurrent_injective
  ext φ
  rw [← signedMeasurePairing_currentTest (volume.withDensityᵥ h),
    signedMeasurePairing_density volume h hh]
  exact tendsto_nhds_unique (hw φ) (test_pairing_of_l1 hz hh hc φ)

/-- Identifying a positive finite measure with a signed density implies absolute continuity. -/
theorem absolutelyContinuous_of_signed_density
    (w : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure w]
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : Integrable h)
    (he : w.toSignedMeasure = volume.withDensityᵥ h) : w ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hnull
  have hz : w.real s = 0 := by
    rw [← Measure.toSignedMeasure_apply_measurable hs, he, withDensityᵥ_apply hh hs,
      Measure.restrict_zero_set hnull, integral_zero_measure]
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top w s)

/-- The TV norm of a difference of integrable densities is bounded by its L¹ norm. -/
theorem density_difference_tv_le {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Integrable f) (hg : Integrable g) :
    (SignedMeasure.totalVariation (volume.withDensityᵥ f - volume.withDensityᵥ g)).real univ ≤
      ∫ x, ‖f x - g x‖ := by
  rw [← withDensityᵥ_sub hf hg]
  exact signedDensity_tv_le volume _ (hf.sub hg)

/--
L¹ convergence of densities and smooth-test convergence identify the signed limit as h dx. With the
stated total variation diagonal bound and vanishing error, the given signed measures converge to
this limit in total variation. Reference: De Philippis–Rindler, arXiv p. 8, (2.3), (2.5).
-/
theorem totalVariation_of_diagonal
    (w : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (wseq : ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {z : ℕ → EuclideanSpace ℝ (Fin d) → ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hz : ∀ n, Integrable (z n)) (hh : Integrable h)
    (hc : Tendsto (fun n => ∫ x, ‖z n x - h x‖) atTop (𝓝 0))
    (hw : ∀ φ : ScalarCurrentTest d,
      Tendsto (fun n => ∫ x, φ x * z n x) atTop (𝓝 (signedTestCurrent w φ)))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hdiag : ∀ n, (wseq n - w).totalVariation.real univ ≤
      (SignedMeasure.totalVariation (volume.withDensityᵥ (z n) - w)).real univ + δ n) :
    w = volume.withDensityᵥ h ∧
      Tendsto (fun n => (wseq n - w).totalVariation.real univ) atTop (𝓝 0) := by
  have he := density_of_test_limit hz hh hc w hw
  refine ⟨he, tv_tendsto_of_diagonal _ _ δ (fun _ => ENNReal.toReal_nonneg) ?_ hc hδ⟩
  intro n
  apply (hdiag n).trans
  rw [he]
  exact add_le_add (density_difference_tv_le (hz n) hh) le_rfl

/-- Global TV convergence implies convergence of the total variation on each fixed set. -/
theorem totalVariation_on_set_tendsto
    (wseq : ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (w : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hc : Tendsto (fun n => (wseq n - w).totalVariation.real univ) atTop (𝓝 0))
    (s : Set (EuclideanSpace ℝ (Fin d))) :
    Tendsto (fun n => (wseq n - w).totalVariation.real s) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ hc
  intro n
  haveI : IsFiniteMeasure (wseq n - w).totalVariation := by
    unfold SignedMeasure.totalVariation
    infer_instance
  exact measureReal_mono (subset_univ s)

/--
On Euclidean space, integrable zero-mean tₙ with tₙ + hₙ ≥ 0, hₙ → g in L¹, and negative parts
tending to zero in measure on every ball satisfy tₙ → 0 and tₙ + hₙ → g in L¹. Every dimension is
allowed. Reference: De Philippis–Rindler, arXiv p. 13, Lemma 2.2.
-/
theorem positivity_zero_mass_balls
    {t h : ℕ → EuclideanSpace ℝ (Fin d) → ℝ} {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (ht : ∀ n, Integrable (t n)) (hh : ∀ n, Integrable (h n)) (hg : Integrable g)
    (hz : ∀ n, ∀ᵐ x ∂volume, 0 ≤ t n x + h n x)
    (hmass : ∀ n, (∫ x, t n x) = 0)
    (hc : Tendsto (fun n => ∫ x, ‖h n x - g x‖) atTop (𝓝 0))
    (hlevel : ∀ R δ : ℝ, 0 < δ → Tendsto
      (fun n => volume {x | x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) R ∧
        δ < max 0 (-t n x)}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖t n x‖) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ x, ‖t n x + h n x - g x‖) atTop (𝓝 0) := by
  apply positivity_zero_mass ht hh hg hz hmass hc
    (fun k : ℕ => ball (0 : EuclideanSpace ℝ (Fin d)) k)
    (fun _ => measurableSet_ball) (fun _ => measure_ball_lt_top.ne)
    (fun _ _ h => ball_subset_ball (by exact_mod_cast h)) (iUnion_ball_nat 0)
  intro k δ hδ
  have he n : (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) (k : ℝ)))
      {x | δ < max 0 (-t n x)} =
      volume {x | x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) k ∧ δ < max 0 (-t n x)} := by
    rw [Measure.restrict_apply' measurableSet_ball]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, and_comm]
  simpa only [he] using hlevel k δ hδ

end GeometricMeasure.StrongConstancy

/-!
## Signed measures and their total variation

A signed measure on a measurable set is bounded above by its Jordan total variation. This estimate
supports the singularity contradiction for the blow-up limit. Reference: De Philippis–Rindler, arXiv
p. 8, after (2.2)–(2.3).
-/
namespace GeometricMeasure

/-- A signed measure on each measurable set is bounded above by its Jordan total variation. -/
theorem StrongConstancy.signedMeasure_apply_le_totalVariation {α : Type*} [MeasurableSpace α]
    (s : SignedMeasure α) {A : Set α} (hA : MeasurableSet A) :
    s A ≤ s.totalVariation.real A := by
  conv_lhs => rw [← s.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hA]
  simp only [SignedMeasure.totalVariation, measureReal_def, Measure.add_apply]
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  linarith [ENNReal.toReal_nonneg (a := s.toJordanDecomposition.negPart A)]

end GeometricMeasure
