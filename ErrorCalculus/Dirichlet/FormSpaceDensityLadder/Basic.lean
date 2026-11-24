import ErrorCalculus.Dirichlet.RightDerivativesZero.Basic
import ErrorCalculus.Dirichlet.BoundedDenseStrong.Basic
import ErrorCalculus.Dirichlet.LatticeGamma.Basic
import ErrorCalculus.Dirichlet.EntropyDecay.Basic

/-!
# Form-space approximation and closedness of logarithmic Sobolev inequalities

This file contains the definitions and results of the development of
`ErrorCalculus.Dirichlet.FormSpaceDensityLadder` that the main statements of the library (the head
theorems listed in the README of the repository) use.
`ErrorCalculus.Dirichlet.FormSpaceDensityLadder` imports it and continues the development.

## Main definitions

* `ErrorStructure.betaResolventGenerator`: For `0 < β`, the class `β • S.resolvent β hβ u`, as an
  element of the domain of the generator.

## Main statements

* `ErrorStructure.tendsto_betaResolvent_formSpace_seq`: Every positive sequence of resolvent
  parameters tending to infinity gives form convergence.
-/
noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- For `0 < β`, the class `β • S.resolvent β hβ u`, as an element of the domain of the generator.
-/
def betaResolventGenerator (β : ℝ) (hβ : 0 < β) (u : Lp ℝ 2 μ) : S.generatorDom :=
  ⟨β • S.resolvent β hβ u,
    S.energy.betaResolvent_mem_generatorDom S.energy_closed S.dense β hβ u⟩

theorem energy_betaResolvent_le (β : ℝ) (hβ : 0 < β) (u : S.dom) :
    S.energy.E (S.generatorForm (S.betaResolventGenerator β hβ u))
      (S.generatorForm (S.betaResolventGenerator β hβ u)) ≤ S.energy.E u u :=
  (S.energy.energy_beta_resolvent_le_approxForm S.energy_closed β hβ (u : Lp ℝ 2 μ)).trans
    (S.energy.approxForm_le_energy S.energy_closed β hβ u)

/-- Every positive sequence of resolvent parameters tending to infinity gives form convergence. -/
theorem tendsto_betaResolvent_formSpace_seq (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (ht : Tendsto b atTop atTop) (u : S.dom) :
    Tendsto (fun n => S.energy.formToDomain.symm
      (S.generatorForm (S.betaResolventGenerator (b n) (hb n) u))) atTop
      (𝓝 (S.energy.formToDomain.symm u)) :=
  S.energy_closed.tendsto_formSpace_of_energy_le (S.tendsto_betaResolvent b hb ht u)
    (fun n => S.energy_betaResolvent_le (b n) (hb n) u)

end ErrorCalculus.ErrorStructure
