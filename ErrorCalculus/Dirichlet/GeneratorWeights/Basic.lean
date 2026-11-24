import ErrorCalculus.Dirichlet.ProductRule
import ErrorCalculus.Dirichlet.SemigroupGenerator.Basic
import ErrorCalculus.Dirichlet.EIDVectorChain
import ErrorCalculus.Dirichlet.SemigroupResolvent
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The generator of an error structure and divergences

This file contains the definitions and results of the development of
`ErrorCalculus.Dirichlet.GeneratorWeights` that the main statements of the library (the head
theorems listed in the README of the repository) use. `ErrorCalculus.Dirichlet.GeneratorWeights`
imports it and continues the development.

## Main definitions

* `ErrorStructure.generatorResolvent`: The contraction resolvent of the closed, densely defined
  energy form of `S`.
* `ErrorStructure.generatorDom`: The domain of the generator of `S`, that is, the domain of
  `S.generatorResolvent`.
* `ErrorStructure.generator`: The generator of `S`, that is, the generator of
  `S.generatorResolvent`.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- The contraction resolvent of the closed, densely defined energy form of `S`. -/
abbrev generatorResolvent := S.energy.formResolvent S.energy_closed S.dense
/-- The domain of the generator of `S`, that is, the domain of `S.generatorResolvent`. -/
abbrev generatorDom := S.generatorResolvent.dom
/-- The generator of `S`, that is, the generator of `S.generatorResolvent`. -/
abbrev generator := S.generatorResolvent.generator

end ErrorCalculus.ErrorStructure
