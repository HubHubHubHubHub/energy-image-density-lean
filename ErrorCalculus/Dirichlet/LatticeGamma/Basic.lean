import ErrorCalculus.Dirichlet.BoundedDenseStrong.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Lattice operations and the carré du champ

This file contains the results of the development of `ErrorCalculus.Dirichlet.LatticeGamma` that the
main statements of the library (the head theorems listed in the README of the repository) use.
`ErrorCalculus.Dirichlet.LatticeGamma` imports it and continues the development.

## Main statements

* `ErrorStructure.lipschitz_abs`: The absolute value on `ℝ` is `1`-Lipschitz.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus.ErrorStructure

theorem lipschitz_abs : LipschitzWith 1 (abs : ℝ → ℝ) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y

end ErrorCalculus.ErrorStructure
