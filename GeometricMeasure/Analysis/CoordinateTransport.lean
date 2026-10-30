import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Coordinate Transport

## Main results
Transport between coordinate space `Fin n → ℝ` and Euclidean space `EuclideanSpace ℝ (Fin n)`
(measure theory and differential calculus, Mathlib only). The transport is `WithLp.toLp 2`, namely
`(PiLp.continuousLinearEquiv 2 ℝ _).symm`, the underlying function of
`ErrorCalculus.ErrorStructure.euclideanEquiv n`. It preserves volume
(`EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`) and transports spans (linear
equivalence), smooth compactly supported tests and the derivative (`comp_right_fderiv`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff

namespace GeometricMeasure
variable {n : ℕ}

/-- The transport `WithLp.toLp 2` is a measurable embedding. -/
theorem measurableEmbedding_coordinateToLp :
    MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
  (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding

/-- The inverse transport `WithLp.ofLp` is measurable. -/
theorem measurable_coordinateOfLp :
    Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) :=
  (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurable

/--
volume on `Fin n → ℝ` (product) versus Euclidean volume: if the image of ν under `WithLp.toLp 2` is
absolutely continuous with respect to Euclidean volume, then ν is absolutely continuous with
respect to product volume on `Fin n → ℝ`. No assumption on ν.
-/
theorem absolutelyContinuous_volume_of_map_coordinateToLp (ν : Measure (Fin n → ℝ))
    (h : ν.map (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ≪ volume) :
    ν ≪ volume := by
  have h2 := h.map (measurable_coordinateOfLp (n := n))
  have hν : (ν.map (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))).map
      (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) = ν :=
    MeasurableEquiv.map_symm_map (MeasurableEquiv.toLp 2 (Fin n → ℝ))
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin n))).map
      (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) = volume :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).map_eq
  rwa [hν, hvol] at h2

/--
Transport of a full span: if the vᵢ span `Fin n → ℝ`, their images `WithLp.toLp 2 (vᵢ)` span
Euclidean space.
-/
theorem span_range_coordinateToLp_eq_top {ι : Type*} (v : ι → (Fin n → ℝ))
    (h : Submodule.span ℝ (range v) = ⊤) :
    Submodule.span ℝ (range fun i => (WithLp.toLp 2 (v i) : EuclideanSpace ℝ (Fin n))) = ⊤ := by
  set e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  have hr : (range fun i => (WithLp.toLp 2 (v i) : EuclideanSpace ℝ (Fin n))) =
      (e.toLinearEquiv.toLinearMap : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) '' range v := by
    rw [← range_comp]
    rfl
  rw [hr, Submodule.span_image, h, Submodule.map_top, LinearEquiv.range]

/-- Converse: if the images span Euclidean space, the vᵢ span `Fin n → ℝ`. -/
theorem span_range_eq_top_of_coordinateToLp {ι : Type*} (v : ι → (Fin n → ℝ))
    (h : Submodule.span ℝ (range fun i => (WithLp.toLp 2 (v i) : EuclideanSpace ℝ (Fin n))) = ⊤) :
    Submodule.span ℝ (range v) = ⊤ := by
  set e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have hr : range v = (e.toLinearEquiv.toLinearMap : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin n → ℝ)) ''
      range (fun i => (WithLp.toLp 2 (v i) : EuclideanSpace ℝ (Fin n))) := by
    rw [← range_comp]
    rfl
  rw [hr, Submodule.span_image, h, Submodule.map_top, LinearEquiv.range]

/--
For a linear form L on `Fin n → ℝ`, Σⱼ L(Pi.single j 1) · vⱼ = L v (expansion in the canonical
basis).
-/
theorem sum_apply_single_mul (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    ∑ j, L (Pi.single j 1) * v j = L v := by
  conv_rhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hj : (Pi.single j (v j) : Fin n → ℝ) = v j • (Pi.single j 1 : Fin n → ℝ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hj, map_smul, smul_eq_mul, mul_comm]

/--
tests: a Euclidean test ψ, smooth of order `(⊤ : ℕ∞)` and compactly supported, becomes ψ ∘ toLp on
`Fin n → ℝ`, smooth of order `∞` (the order) and compactly supported.
-/
theorem contDiff_hasCompactSupport_comp_coordinateToLp
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hs : HasCompactSupport ψ) :
    ContDiff ℝ ∞ (fun y : Fin n → ℝ => ψ (WithLp.toLp 2 y)) ∧
      HasCompactSupport (fun y : Fin n → ℝ => ψ (WithLp.toLp 2 y)) := by
  set e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  refine ⟨hψ.comp e.contDiff, ?_⟩
  have h := hs.comp_homeomorph e.toHomeomorph
  exact h

/--
chain rule for linear transport: the differential of ψ ∘ toLp at y applied to w is the differential
of ψ at toLp y applied to toLp w.
-/
theorem fderiv_comp_coordinateToLp (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (y w : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => ψ (WithLp.toLp 2 y)) y w =
      fderiv ℝ ψ (WithLp.toLp 2 y) (WithLp.toLp 2 w) := by
  set e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  have h := e.comp_right_fderiv (f := ψ) (x := y)
  exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L w) h

end GeometricMeasure
