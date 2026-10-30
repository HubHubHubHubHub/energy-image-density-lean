import GeometricMeasure.VectorMeasure.Polar
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.Order.LiminfLimsup

/-! Weak convergence through bounded covector fields and positive coordinates. -/
noncomputable section
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ} {m : ℕ}

abbrev BoundedCovectorField (d : ℕ) (m : ℕ) :=
  BoundedContinuousFunction (EuclideanSpace ℝ (Fin d))
    (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)

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

def VectorMeasureWeaklyTendsto
    (Ms : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m))) : Prop :=
  ∀ ω : BoundedCovectorField d m,
    Tendsto (fun n => vectorMeasurePairing (Ms n) ω) atTop (𝓝 (vectorMeasurePairing M ω))

def coordinatePositiveMeasure
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (i : Fin m) : Measure (EuclideanSpace ℝ (Fin d)) :=
  M.variation.withDensity (fun x => ENNReal.ofReal (polarDensity M x i))

def coordinateNegativeMeasure
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (i : Fin m) : Measure (EuclideanSpace ℝ (Fin d)) :=
  M.variation.withDensity (fun x => ENNReal.ofReal (-polarDensity M x i))

theorem coordinatePositiveMeasure_le_variation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (i : Fin m) : coordinatePositiveMeasure M i ≤ M.variation := by
  change M.variation.withDensity _ ≤ M.variation
  calc
    _ ≤ M.variation.withDensity 1 := ?_
    _ = _ := withDensity_one
  apply withDensity_mono
  filter_upwards [norm_polarDensity_ae M] with x hx
  have h := (PiLp.norm_apply_le (polarDensity M x) i).trans_eq hx
  exact ENNReal.ofReal_le_one.mpr ((le_abs_self _).trans h)

theorem coordinateNegativeMeasure_le_variation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (i : Fin m) : coordinateNegativeMeasure M i ≤ M.variation := by
  change M.variation.withDensity _ ≤ M.variation
  calc
    _ ≤ M.variation.withDensity 1 := ?_
    _ = _ := withDensity_one
  apply withDensity_mono
  filter_upwards [norm_polarDensity_ae M] with x hx
  have h := (PiLp.norm_apply_le (polarDensity M x) i).trans_eq hx
  exact ENNReal.ofReal_le_one.mpr ((neg_le_abs _).trans h)

instance isFiniteMeasure_coordinatePositiveMeasure
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (i : Fin m) : IsFiniteMeasure (coordinatePositiveMeasure M i) :=
  isFiniteMeasure_of_le _ (coordinatePositiveMeasure_le_variation M i)

instance isFiniteMeasure_coordinateNegativeMeasure
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (i : Fin m) : IsFiniteMeasure (coordinateNegativeMeasure M i) :=
  isFiniteMeasure_of_le _ (coordinateNegativeMeasure_le_variation M i)

theorem coord_eq_coordinateParts
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (i : Fin m) :
    coord M i = (coordinatePositiveMeasure M i).toSignedMeasure -
      (coordinateNegativeMeasure M i).toSignedMeasure := by
  have hi := (integrable_polarDensity M).eval_piLp i
  have hcoord : coord M i = M.variation.withDensityᵥ (fun x => polarDensity M x i) := by
    apply VectorMeasure.ext
    intro s hs
    rw [coord_apply, withDensityᵥ_apply hi hs]
    have hm := congrArg (fun N : VectorMeasure _ _ => N s) (withDensityᵥ_polarDensity M)
    rw [withDensityᵥ_apply (integrable_polarDensity M) hs] at hm
    rw [← hm]
    exact eval_integral_piLp (fun j => ((integrable_polarDensity M).eval_piLp j).restrict) i
  rw [hcoord, withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hi]
  rfl

end GeometricMeasure

