import DprBridge.Coordinate
import ErrorCalculus.Dirichlet.EIDConditionalGeneral
import ErrorCalculus.Dirichlet.EntropyDecay.Basic
import ErrorCalculus.Dirichlet.ResolventMarkov.Basic
import ErrorCalculus.Dirichlet.SemigroupResolvent
import Foundations.Sections.Defs
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
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
# Energy image density for error structures

This file proves the energy image density property (EID) for every error structure on a
probability space, in every dimension, by discharging the De Philippis–Rindler hypothesis of
`ErrorCalculus.ErrorStructure.eid_of_DPR` with `dePhilippisRindler`.

## Main statements

* `eid_unconditional`: for every error structure `S` on a probability space and every
  `f : Fin n → S.dom`, the measure `S.eidMeasure f` (the pushforward of `μ` restricted to
  `{det Γ[f] > 0}`) is absolutely continuous with respect to Lebesgue measure.
-/
noncomputable section
open MeasureTheory Filter Topology Matrix ErrorCalculus
open scoped InnerProductSpace
namespace DprBridge
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {n : ℕ}

/--
EID for every error structure on a probability space, in every dimension: the pushforward of μ
restricted to {det Γ[f] > 0} is absolutely continuous with respect to Lebesgue measure. Specialize
`ErrorCalculus.ErrorStructure.eid_of_DPR` by discharging DPR, without modifying the definitions of
`ErrorStructure` or `eidMeasure`. This result discharges the explicit EID hypotheses of the
variants, products and monotone limit; no new specialization is added.
-/
theorem eid_unconditional (f : Fin n → S.dom)  :
    S.eidMeasure f ≪ volume :=
  ErrorCalculus.ErrorStructure.eid_of_DPR S f (dePhilippisRindler n)

end DprBridge
