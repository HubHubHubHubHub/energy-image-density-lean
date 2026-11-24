import GeometricMeasure.VectorMeasure.Polar
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Weak convergence of vector measures

This file contains the definitions and results of the development of
`GeometricMeasure.VectorMeasure.WeakConvergence` that the main statements of the library (the head
theorems listed in the README of the repository) use.
`GeometricMeasure.VectorMeasure.WeakConvergence` imports it and continues the development.

## Main definitions

* `BoundedCovectorField`: Bounded continuous covector fields on `EuclideanSpace ℝ (Fin d)`, with
  values in the dual of `EuclideanSpace ℝ (Fin m)`.
* `vectorMeasurePairing`: The pairing `∫ x, ω x (polarDensity M x) ∂M.variation` of a vector measure
  with a bounded covector field.

## Main statements

* `integrable_vectorMeasurePairing`: For a bounded continuous covector field `ω`, the function `x ↦
  ω x (polarDensity M x)` is integrable with respect to `M.variation`.
* `vectorMeasurePairing_withDensityᵥ`: For `f` integrable with respect to `ν`, the pairing of
  `ν.withDensityᵥ f` with a bounded covector field `ω` equals `∫ x, ω x (f x) ∂ν`.
-/
noncomputable section
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ} {m : ℕ}

/-- Bounded continuous covector fields on `EuclideanSpace ℝ (Fin d)`, with values in the dual of
`EuclideanSpace ℝ (Fin m)`. -/
abbrev BoundedCovectorField (d : ℕ) (m : ℕ) :=
  BoundedContinuousFunction (EuclideanSpace ℝ (Fin d))
    (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)

/-- The pairing `∫ x, ω x (polarDensity M x) ∂M.variation` of a vector measure with a bounded
covector field. -/
def vectorMeasurePairing
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ω : BoundedCovectorField d m) : ℝ :=
  ∫ x, ω x (polarDensity M x) ∂M.variation

theorem integrable_boundedCovector_apply
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    {f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m)}
    (hf : Integrable f ν) (ω : BoundedCovectorField d m) :
    Integrable (fun x => ω x (f x)) ν := by
  apply (hf.norm.const_mul ‖ω‖).mono'
  · exact (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)).aestronglyMeasurable_comp₂ ω.continuous.aestronglyMeasurable hf.aestronglyMeasurable
  · filter_upwards with x
    exact ((ω x).le_opNorm (f x)).trans
      (mul_le_mul_of_nonneg_right (ω.norm_coe_le_norm x) (norm_nonneg _))

theorem integrable_vectorMeasurePairing
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ω : BoundedCovectorField d m) :
    Integrable (fun x => ω x (polarDensity M x)) M.variation :=
  integrable_boundedCovector_apply _ (integrable_polarDensity M) ω

theorem vectorMeasurePairing_withDensityᵥ
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    {f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m)}
    (hf : Integrable f ν) (ω : BoundedCovectorField d m) :
    vectorMeasurePairing (ν.withDensityᵥ f) ω = ∫ x, ω x (f x) ∂ν := by
  unfold vectorMeasurePairing
  rw [integral_congr_ae ((polar_eq_normalize ν hf).mono (fun x hx => congrArg (ω x) hx)),
    Measure.variation_withDensityᵥ hf,
    integral_withDensity_eq_integral_toReal_smul₀ hf.aestronglyMeasurable.enorm
      (Filter.Eventually.of_forall (fun x => enorm_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : f x = 0
  · simp [hx]
  · simp only [map_smul, toReal_enorm, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_mul]

end GeometricMeasure

