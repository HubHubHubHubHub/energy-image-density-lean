import DprBridge.GenericCarreDuChamp
import ErrorCalculus.Dirichlet.LocalCarreDuChampChainRule
import DprBridge.TextStatementsContracts.Basic

/-!
# Chain, clamp and Leibniz rules from `ErrorCalculus`

This file contains the definitions and results of the development of `DprBridge.ChainRuleBridge`
that the main statements of the library (the head theorems listed in the README of the repository)
use, together with the other results of the sections they belong to. `DprBridge.ChainRuleBridge`
imports it and continues the development.

## Main definitions

* `TextStatements.ebmErrorStructure`: discharge the `BHFunctionalCalculus γ` hypothesis of
  `toErrorStructure` using (`bhFunctionalCalculus`).

## Main statements

* `TextStatements.bhFunctionalCalculusStatement`: discharge the `ChainRuleStatement` hypothesis of
  `bhFunctionalCalculusStatement_of_chainRuleStatement` (bridge) using (`chainRuleStatement`).
* `TextStatements.ebmEIDMeasure_eq_ebmErrorStructure`: discharge the `BHFunctionalCalculus γ`
  hypothesis of `ebmEIDMeasure_eq` using `bhFunctionalCalculus`.
* `TextStatements.ebm_theorem_1_7`: discharge the `BHFunctionalCalculus γ` hypothesis of
  `ebm_theorem_1_7_of_bhFunctionalCalculus` using `bhFunctionalCalculus`.
-/
noncomputable section
open MeasureTheory Filter Topology ErrorCalculus ErrorCalculus.LocalDirichletForm
open scoped NNReal ENNReal

namespace DprBridge.TextStatements

/-! ## A. Main result: unconditional `BHFunctionalCalculus` -/

/--
discharge the `ChainRuleStatement` hypothesis of
`bhFunctionalCalculusStatement_of_chainRuleStatement` (bridge) using (`chainRuleStatement`). For
every probability space `(X : Type)`, every Dirichlet structure `D` of Eriksson-Bique–Murugan def.
1.1 (pp. 1–2) and every carre du champ operator `γ` of `D` in EBM's sense (p. 2), the named
hypothesis `BHFunctionalCalculus γ` holds: ℰ(f, f) = ∫ γ(f, f) dμ for f ∈ ℱ, and, for m > 0, u ∈ ℱᵐ,
G : ℝᵐ → ℝ of class C¹ and Lipschitz, every class w ∈ L²(μ) equal a.e. to G ∘ u lies in ℱ and γ(w,
v) = Σᵢ ∂ᵢG(u) γ(uᵢ, v) a.e. for every v ∈ ℱ (BH 1991, prop. I.6.1.1, th. I.6.1.2, cor. I.6.1.3, pp.
36–37, with γ = Γ/2; invoked by EBM rem. 2.23).
-/
theorem bhFunctionalCalculusStatement : BHFunctionalCalculusStatement :=
  bhFunctionalCalculusStatement_of_chainRuleStatement chainRuleStatement

section Structure
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {D : EBMDirichletStructure μ}

/--
The per-structure form of `bhFunctionalCalculusStatement`, for a type `X` in any universe; discharge
the hypothesis of the reduction `bhFunctionalCalculus_iff` (bridge) using (`CarreDuChamp.chainRule`
applied to the transported data `γ.toCarreDuChamp` of the local form `ofEBM D`). For every structure
`D` of EBM def. 1.1 on a probability space and every carre du champ operator `γ` of `D` (EBM p. 2),
`BHFunctionalCalculus γ` holds (BH 1991, prop. I.6.1.1, th. I.6.1.2, cor. I.6.1.3).
-/
theorem bhFunctionalCalculus (γ : EBMCarreDuChamp D) : BHFunctionalCalculus γ :=
  (bhFunctionalCalculus_iff γ).2 γ.toCarreDuChamp.chainRule

/-! ## B. Unconditional corollaries (`DprBridge.TextStatements`) -/

/--
discharge the `BHFunctionalCalculus γ` hypothesis of `toErrorStructure` using
(`bhFunctionalCalculus`). The error structure associated with every structure of EBM def. 1.1
equipped with a carre du champ operator `γ`: domain ℱ, Γ = 2γ.
-/
def ebmErrorStructure (γ : EBMCarreDuChamp D) : ErrorStructure X μ :=
  toErrorStructure γ (bhFunctionalCalculus γ)

/--
discharge the `BHFunctionalCalculus γ` hypothesis of `ebmEIDMeasure_eq` using
`bhFunctionalCalculus`. For every n and every f ∈ ℱⁿ, the measure f_*(𝟙_{det γ(f) > 0} · μ) of
EBM def. 1.4 (p. 2) equals `eidMeasure f` of the error structure `ebmErrorStructure γ`.
-/
theorem ebmEIDMeasure_eq_ebmErrorStructure (γ : EBMCarreDuChamp D) {n : ℕ} (f : Fin n → D.F) :
    (μ.withDensity ({x | 0 < (ebmGammaMatrix γ f x).det}.indicator 1)).map
      (fun x i => (f i : Lp ℝ 2 μ) x) = (ebmErrorStructure γ).eidMeasure f :=
  ebmEIDMeasure_eq γ (bhFunctionalCalculus γ) f

/--
discharge the `BHFunctionalCalculus γ` hypothesis of `ebm_theorem_1_7_of_bhFunctionalCalculus` using
`bhFunctionalCalculus`. **EBM Theorem 1.7 (p. 3), with no added hypothesis**: for every
Dirichlet structure of def. 1.1 on a probability space, every associated carre du champ operator γ,
every n ∈
ℕ and every φ ∈ ℱⁿ, φ_*(𝟙_{det γ(φ) > 0} · μ) ≪ ℒⁿ (`EBMEIDProperty`, def. 1.4). The printed f_* is
read as φ_*.
-/
theorem ebm_theorem_1_7 (γ : EBMCarreDuChamp D) : EBMEIDProperty γ :=
  ebm_theorem_1_7_of_bhFunctionalCalculus γ (bhFunctionalCalculus γ)

end Structure

end DprBridge.TextStatements
