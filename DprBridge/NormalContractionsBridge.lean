import DprBridge.ChainRuleBridge

/-!
# Normal contractions for Eriksson-Bique–Murugan Dirichlet structures

## Main results
* `missingNormalContractions`: every normal contraction acts on the domain of a Dirichlet structure
  in the sense of Eriksson-Bique–Murugan, Definition 1.1, and does not increase the energy.
* `EBMDirichletStructure.exists_mem_of_lipschitzWith`: the Lipschitz functional calculus in one
  variable, with the energy bound `K ^ 2 * E(u, u)`.
* `missingGammaExistence`: every such structure has a carré du champ in the sense of
  Eriksson-Bique–Murugan.

Each result instantiates `ErrorCalculus.LocalDirichletForm.toDirichletForm` and
`ErrorCalculus.LocalDirichletForm.exists_mem_of_lipschitzWith` at the local form `ofEBM D`, or uses
`nonempty_ebmCarreDuChamp`.

The structures considered are **local** forms on a **probability** space, with `1 ∈ F` and
`E(1, 1) = 0`. The proofs use axioms (ii)–(iv) and (vi) of Definition 1.1 (closedness, unit
contraction, constants, strong locality), not the unit contraction (iii) alone; axioms (i) and (v)
are not used. The general case of a closed form without locality (Bouleau–Hirsch 1991,
Proposition I.3.3.1; Fukushima 1980, Theorem 1.4.1) is not formalised here.

Together with `missingBHFunctionalCalculus`, `missingLeibniz` and `missingBoundedProducts` from
`DprBridge.ChainRuleBridge`, each of the five `Missing…` contracts of
`DprBridge.TextStatementsContracts` is proved by a theorem of the same name.

## References
* Bouleau–Hirsch 1991, Proposition I.3.3.1 (p. 14) with p = 1, Example 3.1 (pp. 14–15),
  Proposition I.4.1.3 (p. 17).
* Fukushima 1980, Theorem 1.4.1.
* Eriksson-Bique–Murugan, arXiv:2510.13659v1, Definition 1.1 (pp. 1–2) and the carré du champ
  (p. 2).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ErrorCalculus ErrorCalculus.LocalDirichletForm
open scoped NNReal ENNReal

namespace DprBridge.TextStatements

section Structure
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/--
Normal contractions act on Eriksson-Bique–Murugan Dirichlet structures. For every structure `D` of
Definition 1.1, every `1`-Lipschitz `F : ℝ → ℝ` with `F 0 = 0`, every `u ∈ F` and every class
`w ∈ L²(μ)` equal almost everywhere to `F ∘ u`, we have `w ∈ F` and `E(w, w) ≤ E(u, u)`
(Bouleau–Hirsch 1991, Proposition I.3.3.1 with p = 1 and Example 3.1, through locality;
Fukushima 1980, Theorem 1.4.1 (e)). The proof uses axioms (ii)–(iv) and (vi) of Definition 1.1.
-/
theorem missingNormalContractions : MissingNormalContractions (μ := μ) :=
  fun D => (ofEBM D).toDirichletForm.contraction

/--
Lipschitz functional calculus in one variable for an Eriksson-Bique–Murugan Dirichlet structure.
For a `K`-Lipschitz `F : ℝ → ℝ` (with no condition on `F 0`), `u ∈ F` and every class
`w ∈ L²(μ)` equal almost everywhere to `F ∘ u`, we have `w ∈ F` and `E(w, w) ≤ K ^ 2 * E(u, u)`
(Bouleau–Hirsch 1991, Proposition I.3.3.1 and Example 3.1, under (M): `1 ∈ F`, `E(1, 1) = 0`).
-/
theorem EBMDirichletStructure.exists_mem_of_lipschitzWith (D : EBMDirichletStructure μ)
    {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) (u : D.F) (w : Lp ℝ 2 μ)
    (hw : ⇑w =ᵐ[μ] fun x => F ((u : Lp ℝ 2 μ) x)) :
    ∃ hw' : w ∈ D.F, D.E ⟨w, hw'⟩ ⟨w, hw'⟩ ≤ (K : ℝ) ^ 2 * D.E u u :=
  (ofEBM D).exists_mem_of_lipschitzWith hF u w hw

/--
Every Eriksson-Bique–Murugan Dirichlet structure on a probability space has a carré du champ in the
sense of Eriksson-Bique–Murugan, p. 2 (after Bouleau–Hirsch 1991, Proposition I.4.1.3, p. 17):
axiom (v) gives property (R), hence an operator `Γ`, and `γ = Γ / 2`.
-/
theorem missingGammaExistence : MissingGammaExistence (μ := μ) :=
  nonempty_ebmCarreDuChamp

/-- The five `Missing…` contracts are proved, each by a theorem of the same name. -/
example : MissingNormalContractions (μ := μ) ∧ MissingGammaExistence (μ := μ) ∧
    MissingBHFunctionalCalculus (μ := μ) ∧ MissingLeibniz (μ := μ) ∧
    MissingBoundedProducts (μ := μ) :=
  ⟨missingNormalContractions, missingGammaExistence, missingBHFunctionalCalculus, missingLeibniz,
    missingBoundedProducts⟩

end Structure

/-- Non-vacuity on the one-dimensional Ornstein–Uhlenbeck structure `ebmOU`. -/
example : ∀ {F : ℝ → ℝ}, LipschitzWith 1 F → F 0 = 0 → ∀ (u : ebmOU.F)
    (w : Lp ℝ 2 (ProbabilityTheory.gaussianReal 0 1)),
    (⇑w =ᵐ[ProbabilityTheory.gaussianReal 0 1] fun x =>
      F ((u : Lp ℝ 2 (ProbabilityTheory.gaussianReal 0 1)) x)) →
      ∃ hw : w ∈ ebmOU.F, ebmOU.E ⟨w, hw⟩ ⟨w, hw⟩ ≤ ebmOU.E u u :=
  missingNormalContractions ebmOU

end DprBridge.TextStatements
