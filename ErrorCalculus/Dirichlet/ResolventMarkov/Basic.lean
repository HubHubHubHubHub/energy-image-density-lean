import ErrorCalculus.Dirichlet.ApproximatingForm
import ErrorCalculus.Dirichlet.Calculus
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Rademacher

/-!
# The Markov property of the resolvent

This file contains the definitions and results of the development of
`ErrorCalculus.Dirichlet.ResolventMarkov` that the main statements of the library (the head theorems
listed in the README of the repository) use. `ErrorCalculus.Dirichlet.ResolventMarkov` imports it
and continues the development.

## Main definitions

* `ErrorStructure.resolvent`: The resolvent of the closed energy form of an error structure.
-/
noncomputable section
open MeasureTheory
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- The resolvent of the closed energy form of an error structure. -/
def resolvent (β : ℝ) (hβ : 0 < β) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  S.energy.resolvent S.energy_closed β hβ

end ErrorCalculus.ErrorStructure
