import ErrorCalculus.Dirichlet.SemigroupEnergyQuotient.Basic
import ErrorCalculus.Dirichlet.BoundedDenseStrong.Basic
import ErrorCalculus.Dirichlet.ImageStructure
import ErrorCalculus.Dirichlet.ResolventMarkov.Basic
import Foundations.Sections.Defs
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Exponential entropy decay from a logarithmic Sobolev inequality

This file contains the results of the development of `ErrorCalculus.Dirichlet.EntropyDecay` that the
main statements of the library (the head theorems listed in the README of the repository) use.
`ErrorCalculus.Dirichlet.EntropyDecay` imports it and continues the development.

## Main statements

* `ErrorStructure.tendsto_betaResolvent`: For positive parameters `b i` tending to infinity along
  `l`, `b i • S.resolvent (b i) _ f` tends to `f` in `L²`.
-/
noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace ErrorCalculus
open QuadForm

namespace ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

theorem tendsto_betaResolvent {ι : Type*} {l : Filter ι} (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) (ht : Tendsto b l atTop) (f : Lp ℝ 2 μ) :
    Tendsto (fun i => b i • S.resolvent (b i) (hb i) f) l (𝓝 f) :=
  S.energy.tendsto_beta_resolvent S.energy_closed S.dense b hb ht f

end ErrorStructure

end ErrorCalculus
