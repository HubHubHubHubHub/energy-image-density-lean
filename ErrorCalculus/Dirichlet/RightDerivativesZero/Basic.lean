import ErrorCalculus.Dirichlet.EntropyDecay.Basic

/-!
# Right derivatives at the initial time

This file contains the definitions and results of the development of
`ErrorCalculus.Dirichlet.RightDerivativesZero` that the main statements of the library (the head
theorems listed in the README of the repository) use. `ErrorCalculus.Dirichlet.RightDerivativesZero`
imports it and continues the development.

## Main definitions

* `ErrorStructure.generatorForm`: The form-domain representative of a generator-domain element.
-/
noncomputable section
open MeasureTheory Filter Topology Set
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- The form-domain representative of a generator-domain element. -/
def generatorForm (u : S.generatorDom) : S.dom :=
  ⟨u, S.energy.formResolvent_dom_le S.energy_closed S.dense u.property⟩

end ErrorCalculus.ErrorStructure
