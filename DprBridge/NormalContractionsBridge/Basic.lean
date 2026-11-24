import DprBridge.ChainRuleBridge.Basic

/-!
# Normal contractions for Eriksson-Bique–Murugan Dirichlet structures

This file contains the results of the development of `DprBridge.NormalContractionsBridge` that the
main statements of the library (the head theorems listed in the README of the repository) use.
`DprBridge.NormalContractionsBridge` imports it and continues the development.

## Main statements

* `TextStatements.missingNormalContractions`: Normal contractions act on Eriksson-Bique–Murugan
  Dirichlet structures.

## References

* Bouleau–Hirsch 1991, Proposition I.3.3.1 (p. 14) with p = 1, Example 3.1 (pp. 14–15),
  Proposition I.4.1.3 (p. 17).
* Fukushima 1980, Theorem 1.4.1.
* Eriksson-Bique–Murugan, arXiv:2510.13659v1, Definition 1.1 (pp. 1–2) and the carré du champ
  (p. 2).
-/
noncomputable section
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

end Structure

end DprBridge.TextStatements
