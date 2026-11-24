import DprBridge.TextStatements.Basic

/-!
# Products, functional calculus and carré-du-champ predicates

This file contains the definitions and results of the development of
`DprBridge.TextStatementsContracts` that the main statements of the library (the head theorems
listed in the README of the repository) use. `DprBridge.TextStatementsContracts` imports it and
continues the development.

## Main definitions

* `TextStatements.MissingNormalContractions`: Proved contract: see `missingNormalContractions`.
-/
noncomputable section
open MeasureTheory Filter Topology ErrorCalculus
open scoped NNReal ENNReal

namespace DprBridge.TextStatements

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/--
Proved contract: see `missingNormalContractions`. BH 1991 prop. I.3.3.1, univariate version: the
single unit contraction of EBM def. 1.1 (iii) implies all normal contractions (F is 1-Lipschitz,
F(0) = 0).
-/
def MissingNormalContractions : Prop :=
  ∀ (D : EBMDirichletStructure μ) {F : ℝ → ℝ}, LipschitzWith 1 F → F 0 = 0 →
    ∀ (u : D.F) (w : Lp ℝ 2 μ),
      (⇑w =ᵐ[μ] fun x => F ((u : Lp ℝ 2 μ) x)) →
      ∃ hw : w ∈ D.F, D.E ⟨w, hw⟩ ⟨w, hw⟩ ≤ D.E u u

end DprBridge.TextStatements
