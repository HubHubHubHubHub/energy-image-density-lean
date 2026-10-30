import DprBridge.GenericCarreDuChamp
import DprBridge.TextStatementsContracts
import ErrorCalculus.Dirichlet.LocalCarreDuChampChainRule

/-!
# Chain Rule Bridge

## Main results
Connect `DprBridge` to the multivariate chain rule proved in
(`ErrorCalculus.LocalDirichletForm.CarreDuChamp.chainRule`, `chainRuleStatement`) and the clamp and
Leibniz rules proved in (`clampRule`, `leibnizRule`, `clampRuleStatement`, `leibnizRuleStatement`).
Each declaration instantiates proved results through the (bridge) reductions in
`DprBridge.GenericCarreDuChamp` (`bhFunctionalCalculus_iff`,
`bhFunctionalCalculusStatement_of_chainRuleStatement`, `gammaClampStatement_of_clampRuleStatement`,
`gammaLeibnizStatement_of_leibnizRuleStatement`).

* Bouleau–Hirsch 1991: prop. I.6.1.1, th. I.6.1.2, cor. I.6.1.3 (pp. 36–37); (EID), ch. V (p. 185);
cor. II.5.2.3 (p. 109).
* Eriksson-Bique–Murugan, arXiv:2510.13659v1: def. 1.1 (pp. 1–2), (1.2)–(1.3) (p. 2), def. 1.4 (p.
2), conj. 1.6 and th. 1.7 (p. 3); rem. 2.23 (p. 16).

## Main results
* **Main result**: `bhFunctionalCalculusStatement : BHFunctionalCalculusStatement` (types `X :
Type`), and its per-structure form `bhFunctionalCalculus` (`X` in any universe).
* Unconditional corollaries of bridge statements that assumed `BHFunctionalCalculus`,
`ClampRuleStatement` or `LeibnizRuleStatement` (`DprBridge.TextStatements`,
`DprBridge.TextStatementsControls`, `DprBridge.GenericCarreDuChamp`).
* Additional results: the same instantiations discharge the predicates
`MissingBHFunctionalCalculus`, `MissingLeibniz` and `MissingBoundedProducts`.

The chain rule for arbitrary Lipschitz F is outside this module. The sigma-finite setting (the
printed BH conjecture without (M)) is proved in `DprBridge.BH1991PrintedProof`. The contracts
`MissingNormalContractions` and `MissingGammaExistence` are proved in
`DprBridge/NormalContractionsBridge.lean` (`missingNormalContractions`, `missingGammaExistence`).
-/

noncomputable section
set_option autoImplicit false
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

/--
discharge the `BHFunctionalCalculus γ` hypothesis of
`bh_eid_conjecture_PM_of_bhFunctionalCalculus` using `bhFunctionalCalculus`. The BH 1991 EID
conjecture (Notes, p. 302), restricted to structures
of EBM def. 1.1, i.e. under (P) (probability) and (M) (𝟙 ∈ ℱ), with no added hypothesis: for every n
∈ ℕ* and every u ∈ ℱⁿ, u_*((det Γ(u, u*)) · μ) ≪ λₙ with Γ = 2γ (BH 1991, (EID) p. 185, conclusion
of cor. II.5.2.3 p. 109).
-/
theorem bh_eid_conjecture_PM (γ : EBMCarreDuChamp D) : BH1991EIDProperty γ :=
  bh_eid_conjecture_PM_of_bhFunctionalCalculus γ (bhFunctionalCalculus γ)

/-! ## C. Unconditional corollaries (`DprBridge.TextStatementsControls`) -/

/--
discharge the `BHFunctionalCalculus γ` hypothesis of `boundedProducts_of_calculus` using
`bhFunctionalCalculus`. A structure of EBM def. 1.1 equipped with a carre du champ operator γ has
bounded products (`BoundedProducts D`: for f, g ∈ ℱ ∩ L^∞, there exists p ∈ ℱ equal a.e. to f g; BH
1991 I.3.3.2).
-/
theorem boundedProducts_of_ebmCarreDuChamp (γ : EBMCarreDuChamp D) : BoundedProducts D :=
  boundedProducts_of_calculus γ (bhFunctionalCalculus γ)

/--
discharge the `BHFunctionalCalculus γ` hypothesis of `bh_det_nonneg` using `bhFunctionalCalculus`.
For every n and every f ∈ ℱⁿ, the determinant of the BH 1991 matrix Γ(f, f*) = [2 γ(fᵢ, fⱼ)] ((EID),
p. 185) is nonnegative μ-a.e.
-/
theorem bhGammaMatrix_det_nonneg (γ : EBMCarreDuChamp D) {n : ℕ} (f : Fin n → D.F) :
    ∀ᵐ x ∂μ, 0 ≤ (bhGammaMatrix γ f x).det :=
  bh_det_nonneg γ (bhFunctionalCalculus γ) f

/-! ## D. Additional results: predicates discharged by instantiation -/

/--
The predicate `MissingBHFunctionalCalculus` is proved using (`bhFunctionalCalculus`): on a fixed
probability space, every structure of EBM def. 1.1 equipped with a carre du champ operator γ
satisfies `BHFunctionalCalculus γ` (BH 1991, prop. I.6.1.1, th. I.6.1.2, cor. I.6.1.3).
-/
theorem missingBHFunctionalCalculus : MissingBHFunctionalCalculus (μ := μ) :=
  fun _ γ => bhFunctionalCalculus γ

/--
The predicate `MissingLeibniz` is proved using (`CarreDuChamp.leibnizRule`) applied to the
transported data `γ.toCarreDuChamp`: for essentially bounded f, g ∈ ℱ, p ∈ ℱ equal a.e. to f g and v
∈ ℱ, γ(p, v) = f γ(g, v) + g γ(f, v) a.e. (BH 1991, cor. I.6.1.3, case F(s, t) = s t).
-/
theorem missingLeibniz : MissingLeibniz (μ := μ) :=
  fun _ γ f g p v hf hg hp => γ.toCarreDuChamp.leibnizRule f g p v hf hg hp

/--
The predicate `MissingBoundedProducts` is proved using the existence of γ
(`nonempty_ebmCarreDuChamp`, bridge) and `boundedProducts_of_ebmCarreDuChamp` : every structure of
EBM def. 1.1 on a probability space has bounded products (BH 1991 I.3.3.2).
-/
theorem missingBoundedProducts : MissingBoundedProducts (μ := μ) :=
  fun D => (nonempty_ebmCarreDuChamp D).elim boundedProducts_of_ebmCarreDuChamp

end Structure

/-! ## E. Unconditional corollaries of the quantified statements (types `X : Type`) -/

/--
discharge the quantified hypothesis (`BHFunctionalCalculus γ` for every structure) of
`ebm_conjecture_1_6_of_bhFunctionalCalculus` using (`bhFunctionalCalculus`).
**EBM Conjecture 1.6 (p. 3)**, asserted by th. 1.7: every Dirichlet structure of def. 1.1 on a
probability space `(X : Type)`, with any associated carre du champ operator, has the EID property
of def. 1.4.
-/
theorem ebm_conjecture_1_6 : EBMConjecture_1_6 :=
  ebm_conjecture_1_6_of_bhFunctionalCalculus fun _ _ _ _ _ γ => bhFunctionalCalculus γ

/--
discharge the `ClampRuleStatement` hypothesis of `gammaClampStatement_of_clampRuleStatement`
(bridge) using (`clampRuleStatement`). `GammaClampStatement`: for every structure of EBM def. 1.1 on
a probability space `(X : Type)`, every γ, u, v, w ∈ ℱ and a, b ∈ ℝ, if w = a ∨ (u ∧ b) a.e., then
γ(w, v) = 1_{]a, b[}(u) γ(u, v) a.e. (BH 1991, th. I.6.1.2).
-/
theorem gammaClampStatement : GammaClampStatement :=
  gammaClampStatement_of_clampRuleStatement clampRuleStatement

/--
discharge the `LeibnizRuleStatement` hypothesis of `gammaLeibnizStatement_of_leibnizRuleStatement`
(bridge) using (`leibnizRuleStatement`). `GammaLeibnizStatement`: for every structure of EBM def.
1.1 on a probability space `(X : Type)`, every γ, essentially bounded f, g ∈ ℱ, p ∈ ℱ equal a.e. to
f g and v ∈ ℱ, γ(p, v) = f γ(g, v) + g γ(f, v) a.e. (BH 1991, cor. I.6.1.3).
-/
theorem gammaLeibnizStatement : GammaLeibnizStatement :=
  gammaLeibnizStatement_of_leibnizRuleStatement leibnizRuleStatement

/-! ## F. Non-vacuity (controls beyond constants) -/

/--
Non-vacuity of the main result: the one-dimensional Ornstein–Uhlenbeck instance (`ebmOU`), with its
γ = ½ Γ.
-/
example : BHFunctionalCalculus (toEBMCarreDuChamp ouStructure) :=
  bhFunctionalCalculusStatement (ProbabilityTheory.gaussianReal 0 1) ebmOU
    (toEBMCarreDuChamp ouStructure)

/--
Non-vacuity, using the existence of γ (bridge): on `ebmOU`, a carre du champ operator exists and
satisfies the named hypothesis and EBM th. 1.7.
-/
example : ∃ γ : EBMCarreDuChamp ebmOU, BHFunctionalCalculus γ ∧ EBMEIDProperty γ := by
  obtain ⟨γ⟩ := nonempty_ebmCarreDuChamp ebmOU
  exact ⟨γ, bhFunctionalCalculus γ, ebm_theorem_1_7 γ⟩

end DprBridge.TextStatements
