import ErrorCalculus.Dirichlet.ConditionalMatrixLemma
import ErrorCalculus.Dirichlet.DePhilippisRindlerHypothesis
import ErrorCalculus.Dirichlet.GeneratorComposition.Basic
import ErrorCalculus.Dirichlet.LowerSemicontinuous.Basic
import ErrorCalculus.Dirichlet.PolarCurrentNormal
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Energy image density under the De Philippis–Rindler hypothesis

This file contains the results of the development of `ErrorCalculus.Dirichlet.EIDConditional` that
the main statements of the library (the head theorems listed in the README of the repository) use.
`ErrorCalculus.Dirichlet.EIDConditional` imports it and continues the development.

## Main statements

* `absolutelyContinuous_withDensity_of_ae_ne_zero`: Positivity of a density under ν suffices to
  dominate ν by the weighted reference measure.
* `span_polarDirections_of_det_ne_zero`: Row normalization preserves full span.
-/
noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus

/-- Positivity of a density under ν suffices to dominate ν by the weighted reference measure. -/
theorem absolutelyContinuous_withDensity_of_ae_ne_zero {α : Type*} [MeasurableSpace α]
    {ν η : Measure α} (hν : ν ≪ η) {p : α → ENNReal} (hp : Measurable p)
    (hpos : ∀ᵐ y ∂ν, p y ≠ 0) : ν ≪ η.withDensity p := by
  intro B hB
  have he : ∀ᵐ y ∂η, p y ≠ 0 → y ∉ B :=
    (ae_withDensity_iff hp).mp (measure_eq_zero_iff_ae_notMem.mp hB)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hν.ae_le he, hpos] with y hy hp
  exact hy hp

/-- Row normalization preserves full span. Zero rows cause no difficulty in this algebraic step. -/
theorem span_polarDirections_of_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hdet : A.det ≠ 0) (w : Fin n → (Fin n → ℝ) → (Fin n → ℝ))
    (y : Fin n → ℝ) (hw : ∀ i, w i y = A i) :
    Submodule.span ℝ (Set.range (fun i => polarDirection (w i) i y)) = ⊤ := by
  have ht : Submodule.span ℝ (Set.range A.row) = ⊤ := by
    rw [← range_vecMulLinear, LinearMap.range_eq_top]
    exact Matrix.vecMul_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  apply le_antisymm le_top
  rw [← ht]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have he : A.row i = polarNorm (w i y) • polarDirection (w i) i y := by
    ext j
    exact (congrFun (hw i) j).symm.trans (polarNorm_mul_direction (w i) i j y).symm
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end ErrorCalculus
