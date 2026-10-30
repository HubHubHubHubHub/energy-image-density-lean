import GeometricMeasure.VectorMeasure.Polar
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Localization

## Main results
Localization of positive, Euclidean and signed measures. Source: DPR arXiv, p. 9, (2.9). The
positive cutoff uses ofReal; its integral formula requires a nonnegative weight. The pairing
interfaces, are in Current.LocalizedMollification; tested densities are in
Current.MollificationDiagonal. This module does not depend on any Current module.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology
namespace GeometricMeasure
variable {d m : ℕ}

/--
DPR arXiv, p. 9 (2.9). Positive localization by the ofReal density of the bounded continuous weight.
Negative values are clipped; the integral formula requires nonnegativity.
-/
def localPositive (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d))) :
    FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
  ⟨(μ : Measure (EuclideanSpace ℝ (Fin d))).withDensity (fun y => ENNReal.ofReal (χ y)), isFiniteMeasure_withDensity_ofReal (χ.integrable _).hasFiniteIntegral⟩

/-- DPR arXiv, p. 9 (2.9). Integral formula for positive localization with a nonnegative weight. -/
theorem integral_localPositive (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (hχ : ∀ y, 0 ≤ χ y) (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ y, f y ∂(localPositive χ μ : Measure (EuclideanSpace ℝ (Fin d))) = ∫ y, χ y * f y ∂(μ : Measure (EuclideanSpace ℝ (Fin d))) := by
  change (∫ y, f y ∂(μ : Measure (EuclideanSpace ℝ (Fin d))).withDensity _) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun y => ENNReal.ofReal (χ y))
    (ENNReal.measurable_ofReal.comp χ.continuous.measurable)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hχ _), smul_eq_mul]

/--
DPR arXiv, p. 9 (2.9). Continuity of localization by a nonnegative weight in the FiniteMeasure
topology.
-/
theorem localPositive_tendsto (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (hχ : ∀ y, 0 ≤ χ y) (μs : ℕ → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d))) (h : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n => localPositive χ (μs n)) atTop (𝓝 (localPositive χ μ)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  simp only [integral_localPositive χ hχ]
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp h (χ * f)

/--
DPR arXiv, p. 9 (2.9). A weight bounded above by 1 gives a measure dominated by the source measure.
-/
theorem localPositive_le (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (hχ : ∀ y, χ y ≤ 1) (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d))) :
    (localPositive χ μ : Measure (EuclideanSpace ℝ (Fin d))) ≤ (μ : Measure (EuclideanSpace ℝ (Fin d))) := by
  change (μ : Measure (EuclideanSpace ℝ (Fin d))).withDensity _ ≤ _
  calc
    _ ≤ (μ : Measure (EuclideanSpace ℝ (Fin d))).withDensity 1 := withDensity_mono
      (Eventually.of_forall (fun y => ENNReal.ofReal_le_one.mpr (hχ y)))
    _ = _ := withDensity_one

/--
DPR arXiv, p. 9 (2.9). The localized measure vanishes outside the topological support of the weight.
-/
theorem localPositive_support (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d))) :
    (localPositive χ μ : Measure (EuclideanSpace ℝ (Fin d))) (tsupport χ)ᶜ = 0 := by
  rw [show (localPositive χ μ : Measure (EuclideanSpace ℝ (Fin d))) = (μ : Measure (EuclideanSpace ℝ (Fin d))).withDensity
    (fun y => ENNReal.ofReal (χ y)) from rfl, withDensity_apply _ (isClosed_tsupport χ).isOpen_compl.measurableSet]
  apply setLIntegral_eq_zero (isClosed_tsupport χ).isOpen_compl.measurableSet
  intro y hy
  simp [image_eq_zero_of_notMem_tsupport hy]

/--
DPR arXiv, p. 9 (2.9). Vector localization χN by the density χ times the polar, against Euclidean
variation.
-/
def localVector (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m))) :
    VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)) :=
  N.variation.withDensityᵥ (fun y => χ y • polarDensity N y)

/--
DPR arXiv, p. 9 (2.9). Integrability of the density actually defining the localized vector measure.
-/
theorem localVector_integrable (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m))) :
    Integrable (fun y => χ y • polarDensity N y) N.variation := by
  exact (integrable_polarDensity N).bdd_smul (φ := fun y => χ y) ‖χ‖
    χ.continuous.aestronglyMeasurable (Eventually.of_forall χ.norm_coe_le_norm)

/--
DPR arXiv, p. 9 (2.9). Bound on the localized variation by any uniform majorant of the absolute
value of the weight.
-/
theorem localVector_variation_le (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    {C : ℝ} (hC : ∀ y, ‖χ y‖ ≤ C) :
    (localVector χ N).variation ≤ ENNReal.ofReal C • N.variation := by
  rw [localVector, Measure.variation_withDensityᵥ (localVector_integrable χ N)]
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [norm_polarDensity_ae N] with y hy
  rw [← ofReal_norm, norm_smul, hy, mul_one]
  exact ENNReal.ofReal_le_ofReal (hC y)

/--
DPR arXiv, p. 9 (2.9). The localized Euclidean variation vanishes outside the topological support of
the weight.
-/
theorem localVector_support (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m))) :
    (localVector χ N).variation (tsupport χ)ᶜ = 0 := by
  rw [localVector, Measure.variation_withDensityᵥ (localVector_integrable χ N),
    withDensity_apply _ (isClosed_tsupport χ).isOpen_compl.measurableSet]
  apply setLIntegral_eq_zero (isClosed_tsupport χ).isOpen_compl.measurableSet
  intro y hy
  simp [image_eq_zero_of_notMem_tsupport hy]

/--
DPR arXiv, p. 9 (2.9). Total variation tending to zero still does so after localization by a fixed
weight.
-/
theorem localVector_variation_tendsto_zero
    (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (Ns : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (h : Tendsto (fun n => (Ns n).variation univ) atTop (𝓝 0)) :
    Tendsto (fun n => (localVector χ (Ns n)).variation univ) atTop (𝓝 0) := by
  have hc := ENNReal.Tendsto.const_mul h (Or.inr ENNReal.ofReal_ne_top)
    (a := ENNReal.ofReal ‖χ‖)
  rw [mul_zero] at hc
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
    (fun _ => zero_le) (fun n => by
      simpa only [Measure.smul_apply, smul_eq_mul] using
        localVector_variation_le χ (Ns n) χ.norm_coe_le_norm univ)

/--
DPR arXiv, p. 9 (2.9). Scalar multiplication of a signed measure via its two positive Jordan parts.
-/
def localSigned (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (q : SignedMeasure (EuclideanSpace ℝ (Fin d))) : SignedMeasure (EuclideanSpace ℝ (Fin d)) :=
  q.toJordanDecomposition.posPart.withDensityᵥ (fun y => χ y) -
    q.toJordanDecomposition.negPart.withDensityᵥ (fun y => χ y)

end GeometricMeasure
