import ErrorCalculus.Dirichlet.DePhilippisRindlerHypothesis
import GeometricMeasure.Current.CoordinateNormalFamily

/-!
# Coordinate normal currents and the finite DPR interface

## Main results
The polar norms and normality predicates of `ErrorCalculus` agree with the coordinate interfaces of
`GeometricMeasure`. The finite normal-family theorem yields `DePhilippisRindler n`, retaining
finiteness of the dominated measure and all normal-current hypotheses.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff

namespace DprBridge

/-- The polar norm is exactly the transported Euclidean coordinate norm. -/
theorem polarNorm_eq_coordinate {n : ℕ} (x : Fin n → ℝ) :
    ErrorCalculus.polarNorm x =
      ‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm x‖ := rfl

/-- normality unfolds with no change in sign or order of regularity. -/
theorem isNormal_iff_coordinate {n : ℕ} (T : ErrorCalculus.PolarCurrent n) :
    T.IsNormal ↔ ∃ σp σm : Measure (Fin n → ℝ), IsFiniteMeasure σp ∧ IsFiniteMeasure σm ∧
      ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ y, ∑ j, fderiv ℝ φ y (Pi.single j 1) * T.direction y j ∂T.mass) =
          -(∫ y, φ y ∂σp) + ∫ y, φ y ∂σm := Iff.rfl

/--
Exact equivalence of the propositions, by projections and reconstruction. Finiteness of ν is
retained for fidelity to the interface.
-/
theorem coordinate_iff_dePhilippisRindler (n : ℕ) :
    GeometricMeasure.CoordinateDePhilippisRindler n ↔ ErrorCalculus.DePhilippisRindler n := by
  constructor
  · intro h T hT ν hν hac hspan
    exact h (fun i => (T i).mass) (fun i => (T i).finite_mass)
      (fun i => (T i).direction) (fun i => (T i).measurable_direction)
      (fun i => (T i).norm_direction) hT ν hν hac hspan
  · intro h mass hfin direction hdir hnorm hnormal ν hν hac hspan
    exact h (fun i => ⟨mass i, hfin i, direction i, hdir i, hnorm i⟩)
      hnormal ν hν hac hspan

/--
De Philippis–Rindler Corollary 1.12 in finite polar form: finite normal currents whose directions
span almost everywhere force absolute continuity of the finite dominated measure. The coordinate
normal-family theorem supplies the result in every dimension.
De Philippis–Rindler, Theorem 1.1 and Corollary 1.13, give the underlying structure results.
-/
theorem dePhilippisRindler (n : ℕ) : ErrorCalculus.DePhilippisRindler n :=
  (coordinate_iff_dePhilippisRindler n).mp (GeometricMeasure.coordinateDePhilippisRindler n)

end DprBridge
