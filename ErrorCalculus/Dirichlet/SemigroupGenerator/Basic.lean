import ErrorCalculus.Dirichlet.ErrorStructure
import ErrorCalculus.Dirichlet.SemigroupResolvent
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Energy and the generator of the semigroup

This file contains the results of the development of `ErrorCalculus.Dirichlet.SemigroupGenerator`
that the main statements of the library (the head theorems listed in the README of the repository)
use. `ErrorCalculus.Dirichlet.SemigroupGenerator` imports it and continues the development.

## Main statements

* `QuadForm.energy_eq_neg_inner_generator`: The form agrees with minus its generator on the
  generator domain.
-/
noncomputable section
open Filter Topology
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (Q : QuadForm H) (hQ : Q.IsClosed) (hd : Dense (Q.dom : Set H))

/-- The form agrees with minus its generator on the generator domain. -/
theorem energy_eq_neg_inner_generator (u : (Q.formResolvent hQ hd).dom) (v : Q.dom) :
    Q.E ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩ v =
      -inner ℝ ((Q.formResolvent hQ hd).generator u) (v : H) := by
  let f := (u : H) - (Q.formResolvent hQ hd).generator u
  have hu : Q.resolvent hQ 1 zero_lt_one f = (u : H) := by
    simpa only [Q.formResolvent_G hQ hd zero_lt_one, one_smul] using
      (Q.formResolvent hQ hd).G_generator zero_lt_one u
  have hu' : Q.resolventDom hQ 1 zero_lt_one f =
      ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩ := Subtype.ext hu
  have he := Q.resolvent_spec hQ 1 zero_lt_one f v
  rw [hu', hu] at he
  simp only [f, inner_sub_left, one_mul] at he
  linarith

end ErrorCalculus.QuadForm
