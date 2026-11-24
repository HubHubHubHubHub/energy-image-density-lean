import ErrorCalculus.Dirichlet.ApproximatingForm
import ErrorCalculus.Dirichlet.ErrorStructure
import ErrorCalculus.Dirichlet.SemigroupGenerator.Basic
import ErrorCalculus.Dirichlet.SemigroupResolvent
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The energy quotient along the semigroup

This file contains the results of the development of
`ErrorCalculus.Dirichlet.SemigroupEnergyQuotient` that the main statements of the library (the head
theorems listed in the README of the repository) use.
`ErrorCalculus.Dirichlet.SemigroupEnergyQuotient` imports it and continues the development.

## Main statements

* `QuadForm.betaResolvent_mem_generatorDom`: The approximants belong to the generator domain, not
  just the form domain.
-/
noncomputable section
open Filter Topology Set MeasureTheory
namespace ErrorCalculus

namespace QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (Q : QuadForm H) (hQ : Q.IsClosed) (hd : Dense (Q.dom : Set H))

/-- The approximants belong to the generator domain, not just the form domain. -/
theorem betaResolvent_mem_generatorDom (b : ℝ) (hb : 0 < b) (u : H) :
    (Q.betaResolventDom hQ b hb u : H) ∈ (Q.formResolvent hQ hd).dom := by
  rw [Q.formResolvent_dom hQ hd hb]
  exact ⟨b • u, by simp⟩

end QuadForm
end ErrorCalculus
