import ErrorCalculus.Dirichlet.ExtensionLp
import ErrorCalculus.Dirichlet.EIDVectorChain
import ErrorCalculus.Dirichlet.GeneratorWeights.Basic
import ErrorCalculus.Dirichlet.LowerSemicontinuous.Basic
import ErrorCalculus.Dirichlet.SemigroupResolvent
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Composition with smooth functions in the generator domain

This file contains the definitions and results of the development of
`ErrorCalculus.Dirichlet.GeneratorComposition` that the main statements of the library (the head
theorems listed in the README of the repository) use. `ErrorCalculus.Dirichlet.GeneratorComposition`
imports it and continues the development.

## Main definitions

* `IsC2LipschitzGrad`: A C² function on finite coordinate space that is L-Lipschitz and whose
  partial derivatives are all L′-Lipschitz.
* `partialDeriv`: Coordinate derivative, with the finite product carrying its usual sup norm.

## Main statements

* `norm_partialDeriv_le`: Every partial derivative of an `L`-Lipschitz function on `Fin n → ℝ` has
  norm at most `L` at every point.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace ErrorCalculus

/-- Coordinate derivative, with the finite product carrying its usual sup norm. -/
def partialDeriv {n : ℕ} (F : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ F x (Pi.single i 1)

/--
A C² function on finite coordinate space that is L-Lipschitz and whose partial derivatives are all
L′-Lipschitz.
-/
structure IsC2LipschitzGrad {n : ℕ} (F : (Fin n → ℝ) → ℝ) (L L' : ℝ≥0) : Prop where
  contDiff : ContDiff ℝ 2 F
  lipschitz : LipschitzWith L F
  partial_lipschitz : ∀ i, LipschitzWith L' (partialDeriv F i)

theorem norm_partialDeriv_le {n : ℕ} {F : (Fin n → ℝ) → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (i : Fin n) (x : Fin n → ℝ) : ‖partialDeriv F i x‖ ≤ L := by
  calc
    _ ≤ ‖fderiv ℝ F x‖ * ‖Pi.single i (1 : ℝ)‖ := (fderiv ℝ F x).le_opNorm _
    _ ≤ (L : ℝ) * 1 := mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hF)
      (by simp [Pi.norm_single]) (norm_nonneg _) L.coe_nonneg
    _ = _ := mul_one _
end ErrorCalculus
