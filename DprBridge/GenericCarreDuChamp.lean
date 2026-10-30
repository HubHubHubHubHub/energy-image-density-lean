import DprBridge.TextStatements
import ErrorCalculus.Dirichlet.LocalCarreDuChampLevels

/-!
# Carré-du-champ adapters for EBM Dirichlet structures

* Eriksson-Bique–Murugan, arXiv:2510.13659v1: def. 1.1 (pp. 1–2), (1.2) (p. 2), rem. 2.23 (p. 16).
* Bouleau–Hirsch 1991: def. I.4.1.2 and prop. I.4.1.3 (p. 17); th. I.5.2.3 (p. 32); prop. I.6.1.1,
th. I.6.1.2, cor. I.6.1.3 (pp. 36–37).

## Main results
 The six `Prop` contracts (`TestFunctionStatement` … `BHFunctionalCalculusStatement`); `ofEBM`
 (every structure of def. 1.1 is a `LocalDirichletForm`); transport of the carre du champ in both
 directions; **existence of γ from the EBM structure** (`gammaExistenceStatement`,
 `nonempty_ebmCarreDuChamp`: (v) ⟹ (R), then ⟹ Γ, γ = Γ/2), satisfying the predicate
 `MissingGammaExistence`; uniqueness of γ; the reductions `BHFunctionalCalculus γ ↔ ChainRule` and
 `ChainRuleStatement ⟹ BHFunctionalCalculusStatement`.

The generic chain, clamp and Leibniz rules give `BHFunctionalCalculusStatement`,
`GammaClampStatement` and `GammaLeibnizStatement` in `DprBridge.ChainRuleBridge`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace DprBridge.TextStatements
open ErrorCalculus

/-!
The first three predicates express separation by test functions, locality and level cancellation;
they are proved in this module. The clamp, Leibniz and functional-calculus predicates follow from
the generic local Dirichlet-form results through `DprBridge.ChainRuleBridge`.
-/

/--
density of bounded test functions in ℱ: k ∈ L¹ and ∫ h k dμ = 0 for every h ∈ ℱ ∩ L^∞ ⇒ k = 0 a.e.
-/
def TestFunctionStatement : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (D : EBMDirichletStructure μ) (k : Lp ℝ 1 μ),
    (∀ h : D.F, AEBounded (μ := μ) ((h : Lp ℝ 2 μ) : X → ℝ) →
      ∫ x, (h : Lp ℝ 2 μ) x * k x ∂μ = 0) → ⇑k =ᵐ[μ] 0

/-- locality of γ, (f + a) g = 0 a.e. ⇒ γ(f, g) = 0 a.e. -/
def GammaLocalityStatement : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (D : EBMDirichletStructure μ) (γ : EBMCarreDuChamp D) (f g : D.F) (a : ℝ),
    (∀ᵐ x ∂μ, ((f : Lp ℝ 2 μ) x + a) * (g : Lp ℝ 2 μ) x = 0) → ⇑(γ.γ f g) =ᵐ[μ] 0

/--
The carré du champ γ(u, u) vanishes almost everywhere on every level set {u = c}. Reference:
Bouleau–Hirsch, th. I.5.2.3, the atomlessness statement σ^u({c}) = 0.
-/
def GammaLevelSetStatement : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (D : EBMDirichletStructure μ) (γ : EBMCarreDuChamp D) (u : D.F) (c : ℝ),
    ∀ᵐ x ∂μ, (u : Lp ℝ 2 μ) x = c → γ.γ u u x = 0

/--
The chain rule for γ under clamping, γ(a ∨ (u ∧ b), v) = 1_{a < u < b} γ(u, v) a.e. Reduced to
`ClampRuleStatement` by `gammaClampStatement_of_clampRuleStatement`; proved in
(`DprBridge.TextStatements.gammaClampStatement`).
-/
def GammaClampStatement : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (D : EBMDirichletStructure μ) (γ : EBMCarreDuChamp D) (u v w : D.F) (a b : ℝ),
    (⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun x => max a (min ((u : Lp ℝ 2 μ) x) b)) →
      ⇑(γ.γ w v) =ᵐ[μ] fun x => (Set.Ioo a b).indicator 1 ((u : Lp ℝ 2 μ) x) * γ.γ u v x

/--
The Leibniz rule for f, g ∈ ℱ ∩ L^∞. Reduced to `LeibnizRuleStatement` by
`gammaLeibnizStatement_of_leibnizRuleStatement`; proved in
(`DprBridge.TextStatements.gammaLeibnizStatement`).
-/
def GammaLeibnizStatement : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (D : EBMDirichletStructure μ) (γ : EBMCarreDuChamp D) (f g p v : D.F),
    AEBounded (μ := μ) ((f : Lp ℝ 2 μ) : X → ℝ) → AEBounded (μ := μ) ((g : Lp ℝ 2 μ) : X → ℝ) →
    (⇑(p : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (g : Lp ℝ 2 μ) x) →
    ⇑(γ.γ p v) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * γ.γ g v x + (g : Lp ℝ 2 μ) x * γ.γ f v x

/--
The named functional-calculus hypothesis holds for every structure of def. 1.1 equipped with its γ
(the predicate `MissingBHFunctionalCalculus`; BH 1991 prop. I.6.1.1, th. I.6.1.2, cor. I.6.1.3,
invoked by EBM rem. 2.23). Clause (b) is reduced to `ChainRuleStatement` here
(`bhFunctionalCalculusStatement_of_chainRuleStatement`) and proved in
(`DprBridge.TextStatements.bhFunctionalCalculusStatement`).
-/
def BHFunctionalCalculusStatement : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (D : EBMDirichletStructure μ) (γ : EBMCarreDuChamp D), BHFunctionalCalculus γ

end DprBridge.TextStatements


/-!
## P. EBM adapters (in `K_pont_dpr`, outside `ErrorCalculus`)

The declarations below concern the EBM encodings `EBMDirichletStructure`, `EBMCarreDuChamp` and
`BHFunctionalCalculus` (imported from `DprBridge.TextStatements`) and the six `Prop` contracts
above. They recover the EBM results as corollaries of the generic versions
(`ErrorCalculus.Dirichlet.LocalCarreDuChamp` and `LocalCarreDuChampLevels`), and also prove the
existence of γ from axiom (v).
-/

namespace ErrorCalculus
namespace LocalDirichletForm
open DprBridge.TextStatements
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/--
connection to Eriksson-Bique–Murugan def. 1.1 (pp. 1–2): every Dirichlet structure of def. 1.1
defines, axiom by axiom, a `LocalDirichletForm` with the same domain ℱ and form ℰ; closedness
follows from `isClosed_of_formComplete`; axiom (v) is not used.
-/
def ofEBM (D : EBMDirichletStructure μ) : LocalDirichletForm μ where
  form := { dom := D.F, E := D.E, symm := D.symm, nonneg := D.nonneg }
  dense := D.dense
  closed := isClosed_of_formComplete _ D.complete
  markov := D.markov
  one_mem := D.one_mem
  energy_one := D.energy_one
  strongLocality := D.strongLocality

/-- The ℰ₁ norm of `ofEBM D` is the norm in `EBMCarreDuChamp`, √(ℰ(f, f) + ‖f‖²). -/
theorem formNorm_ofEBM (D : EBMDirichletStructure μ) (f : D.F) :
    (ofEBM D).form.formNorm f = Real.sqrt (D.E f f + ‖(f : Lp ℝ 2 μ)‖ ^ 2) := by
  have h := (ofEBM D).form.formNorm_sq f
  have h0 : 0 ≤ (ofEBM D).form.formNorm f := norm_nonneg _
  rw [← Real.sqrt_sq h0, h]
  congr 1
  exact add_comm _ _

/--
existence of γ from EBM axiom (v) (the predicate `MissingGammaExistence` ): the form `ofEBM D`
admits a carre du champ in the sense of BH 1991 def. I.4.1.2 (p. 17), with H = 𝔻 ∩ L^∞ and f̃ = 2
γ(f, f) from (v).
-/
theorem admitsCarreDuChamp_ofEBM (D : EBMDirichletStructure μ) :
    (ofEBM D).toDirichletForm.AdmitsCarreDuChamp := by
  refine ⟨(ofEBM D).toDirichletForm.bddSpace, le_rfl, (ofEBM D).toDirichletForm.dense_bddSpace,
    fun x hx => ?_⟩
  obtain ⟨γff, hγ⟩ := D.carreDuChamp ((ofEBM D).form.formToDomain x)
    ((ofEBM D).aeBounded_of_mem_bddSpace hx)
  refine ⟨(2 : ℝ) • γff, fun z hz => ?_⟩
  have h := hγ ((ofEBM D).form.formToDomain z) ((ofEBM D).aeBounded_of_mem_bddSpace hz)
    ((ofEBM D).form.formToDomain ((ofEBM D).toDirichletForm.mulS x z))
    ((ofEBM D).form.formToDomain ((ofEBM D).toDirichletForm.mulS x x))
    ((ofEBM D).toDirichletForm.coeFn_toLp_mulS hx hz) (by
      filter_upwards [(ofEBM D).toDirichletForm.coeFn_toLp_mulS hx hx] with ω h
      rw [sq]
      exact h)
  have h' : (ofEBM D).form.E ((ofEBM D).form.formToDomain ((ofEBM D).toDirichletForm.mulS x z))
      ((ofEBM D).form.formToDomain x) - (1 / 2 : ℝ) * (ofEBM D).form.E
        ((ofEBM D).form.formToDomain z)
        ((ofEBM D).form.formToDomain ((ofEBM D).toDirichletForm.mulS x x)) =
      ∫ ω, (((ofEBM D).form.formToDomain z : D.F) : Lp ℝ 2 μ) ω * γff ω ∂μ := h
  have hR : ∫ ω, (((ofEBM D).form.formToDomain z : D.F) : Lp ℝ 2 μ) ω * ((2 : ℝ) • γff) ω ∂μ =
      2 * ∫ ω, (((ofEBM D).form.formToDomain z : D.F) : Lp ℝ 2 μ) ω * γff ω ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul (2 : ℝ) γff] with ω hω
    rw [hω, Pi.smul_apply, smul_eq_mul]
    ring
  have key : 2 * (ofEBM D).form.E ((ofEBM D).form.formToDomain ((ofEBM D).toDirichletForm.mulS x z))
      ((ofEBM D).form.formToDomain x) - (ofEBM D).form.E ((ofEBM D).form.formToDomain z)
        ((ofEBM D).form.formToDomain ((ofEBM D).toDirichletForm.mulS x x)) =
      ∫ ω, (((ofEBM D).form.formToDomain z : D.F) : Lp ℝ 2 μ) ω * ((2 : ℝ) • γff) ω ∂μ := by
    rw [hR]
    linarith
  rw [(ofEBM D).ener_toDirichletForm, (ofEBM D).ener_toDirichletForm]
  exact key

end LocalDirichletForm
end ErrorCalculus

namespace DprBridge.TextStatements
open ErrorCalculus ErrorCalculus.LocalDirichletForm
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/--
field-by-field transport: the EBM carre du champ (`EBMCarreDuChamp`) is generic data for the local
form `ofEBM D`.
-/
def EBMCarreDuChamp.toCarreDuChamp {D : EBMDirichletStructure μ} (γ : EBMCarreDuChamp D) :
    (ofEBM D).CarreDuChamp where
  gamma := γ.γ
  symm := γ.symm
  nonneg := γ.nonneg
  continuous := by
    obtain ⟨C, hC⟩ := γ.continuous
    exact ⟨C, fun f g => by rw [formNorm_ofEBM, formNorm_ofEBM]; exact hC f g⟩
  product := γ.product

/-- inverse transport: generic data for `ofEBM D` is a carre du champ in EBM's sense. -/
def ebmCarreDuChampOfCarreDuChamp {D : EBMDirichletStructure μ} (G : (ofEBM D).CarreDuChamp) :
    EBMCarreDuChamp D where
  γ := G.gamma
  symm := G.symm
  nonneg := G.nonneg
  continuous := by
    obtain ⟨C, hC⟩ := G.continuous
    exact ⟨C, fun f g => by
      have h := hC f g
      rwa [formNorm_ofEBM, formNorm_ofEBM] at h⟩
  product := G.product

/--
Every Dirichlet structure of Eriksson-Bique–Murugan Definition 1.1 admits a carré du champ
operator in their sense, p. 2.
-/
def GammaExistenceStatement : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (D : EBMDirichletStructure μ), Nonempty (EBMCarreDuChamp D)

/--
The statement `GammaExistenceStatement` is proved: (v) gives (R) (`admitsCarreDuChamp_ofEBM`), gives
Γ (`bh_4_1_3`, via `nonempty_carreDuChamp_iff`), and γ = Γ/2 is transported (existence of γ: (v) ⟹
(R), then ⟹ Γ, γ = Γ/2; BH 1991 def. I.4.1.2 and prop. I.4.1.3, p. 17).
-/
theorem gammaExistenceStatement : GammaExistenceStatement := by
  intro X _ μ _ D
  obtain ⟨G⟩ := ((ofEBM D).nonempty_carreDuChamp_iff).2 (admitsCarreDuChamp_ofEBM D)
  exact ⟨ebmCarreDuChampOfCarreDuChamp G⟩

/--
The per-structure form of `gammaExistenceStatement`, for a type X in any universe. Every
Dirichlet structure of Eriksson-Bique–Murugan def. 1.1 (pp. 1–2) has a carre du champ operator in
EBM's sense,
p. 2 (by BH 1991 prop. I.4.1.3); existence of γ: (v) ⟹ (R) (`admitsCarreDuChamp_ofEBM`), then ⟹ Γ
(`nonempty_carreDuChamp_iff`), γ = Γ/2 (`ebmCarreDuChampOfCarreDuChamp`). In particular, the
predicate `MissingGammaExistence` is satisfied.
-/
theorem nonempty_ebmCarreDuChamp (D : EBMDirichletStructure μ) : Nonempty (EBMCarreDuChamp D) := by
  obtain ⟨G⟩ := ((ofEBM D).nonempty_carreDuChamp_iff).2 (admitsCarreDuChamp_ofEBM D)
  exact ⟨ebmCarreDuChampOfCarreDuChamp G⟩

/--
uniqueness of the EBM carre du champ, reused from through the generic data
(`CarreDuChamp.gamma_eq`).
-/
theorem EBMCarreDuChamp.gamma_eq {D : EBMDirichletStructure μ} (γ γ' : EBMCarreDuChamp D) :
    γ.γ = γ'.γ :=
  CarreDuChamp.gamma_eq γ.toCarreDuChamp γ'.toCarreDuChamp

/--
reduction of the named functional-calculus hypothesis: since its first clause is the generic result
`CarreDuChamp.energy_eq_integral`, `BHFunctionalCalculus γ` is equivalent to the generic `ChainRule`
contract for the transported data.
-/
theorem bhFunctionalCalculus_iff {D : EBMDirichletStructure μ} (γ : EBMCarreDuChamp D) :
    BHFunctionalCalculus γ ↔ γ.toCarreDuChamp.ChainRule :=
  ⟨fun h => h.2, fun h => ⟨fun f => γ.toCarreDuChamp.energy_eq_integral f, h⟩⟩

/-- `TestFunctionStatement`, a corollary of `ae_eq_zero_of_integral_mul_eq_zero` for `ofEBM D`. -/
theorem testFunctionStatement : TestFunctionStatement := by
  intro X _ μ _ D k hk
  exact (ofEBM D).ae_eq_zero_of_integral_mul_eq_zero k fun h ⟨C, hC⟩ =>
    hk h ⟨C, by filter_upwards [hC] with x hx; rwa [Real.norm_eq_abs]⟩

/-- `GammaLocalityStatement`, a corollary of `CarreDuChamp.gamma_eq_zero_of_mul`. -/
theorem gammaLocalityStatement : GammaLocalityStatement := by
  intro X _ μ _ D γ f g a h
  have h0 : γ.γ f g = 0 := γ.toCarreDuChamp.gamma_eq_zero_of_mul f g a h
  rw [h0]
  exact Lp.coeFn_zero ℝ 1 μ

/-- `GammaLevelSetStatement`, a corollary of `CarreDuChamp.ae_gamma_self_eq_zero_of_eq`. -/
theorem gammaLevelSetStatement : GammaLevelSetStatement := by
  intro X _ μ _ D γ u c
  exact γ.toCarreDuChamp.ae_gamma_self_eq_zero_of_eq u c

/-- The generic contract `ClampRuleStatement` implies `GammaClampStatement`. -/
theorem gammaClampStatement_of_clampRuleStatement (h : ClampRuleStatement) :
    GammaClampStatement := by
  intro X _ μ _ D γ u v w a b hw
  exact h μ (ofEBM D) γ.toCarreDuChamp u v w a b hw

/-- The generic contract `LeibnizRuleStatement` implies `GammaLeibnizStatement`. -/
theorem gammaLeibnizStatement_of_leibnizRuleStatement (h : LeibnizRuleStatement) :
    GammaLeibnizStatement := by
  intro X _ μ _ D γ f g p v hf hg hp
  exact h μ (ofEBM D) γ.toCarreDuChamp f g p v hf hg hp

/--
The generic contract `ChainRuleStatement` (clause (b), arbitrary local form) implies
`BHFunctionalCalculusStatement`.
-/
theorem bhFunctionalCalculusStatement_of_chainRuleStatement (h : ChainRuleStatement) :
    BHFunctionalCalculusStatement := by
  intro X _ μ _ D γ
  exact (bhFunctionalCalculus_iff γ).2 (h μ (ofEBM D) γ.toCarreDuChamp)

end DprBridge.TextStatements
