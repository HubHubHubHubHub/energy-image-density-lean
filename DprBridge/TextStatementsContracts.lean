import DprBridge.TextStatements

/-!
# Products, functional calculus and carré-du-champ predicates

## Main results
The bounded-product theorem and determinant nonnegativity connect the EBM Dirichlet structure to the
BH functional calculus. The predicates for normal contractions, a carré du champ, functional
calculus, products and Leibniz rules state the mathematical assumptions used by these connections.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ErrorCalculus
open scoped NNReal ENNReal

namespace DprBridge.TextStatements

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/--
The products fh, f², gh, fg presupposed by EBM def. 1.1 (v) and (1.2) (BH 1991 I.3.3.2, the algebra
𝔻 ∩ L^∞) exist in the domain of an `ErrorStructure` (`boundedMul`, `coeFn_boundedMul`), with no
added hypothesis.
-/
theorem products_exist (S : ErrorStructure X μ) (f g : S.dom)
    (hf : AEBounded (μ := μ) (f : Lp ℝ 2 μ))
    (hg : AEBounded (μ := μ) (g : Lp ℝ 2 μ)) :
    ∃ p : S.dom, ⇑(p : Lp ℝ 2 μ) =ᵐ[μ]
      fun x => (f : Lp ℝ 2 μ) x * (g : Lp ℝ 2 μ) x :=
  ⟨S.boundedMul f g hf hg, S.coeFn_boundedMul f g hf hg⟩

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

/--
Proved contract: see `missingGammaExistence`. EBM p. 2 following BH 1991 prop. I.4.1.3:
every structure of EBM def. 1.1 has a carre du champ operator in the sense of `EBMCarreDuChamp`.
-/
def MissingGammaExistence : Prop :=
  ∀ (D : EBMDirichletStructure μ), Nonempty (EBMCarreDuChamp D)

/--
Proved contract: see `missingBHFunctionalCalculus`. BH 1991 prop. I.6.1.1, th. I.6.1.2, cor.
I.6.1.3, invoked by EBM rem. 2.23: every structure of def. 1.1 equipped with its γ satisfies
`BHFunctionalCalculus`, making EBM th. 1.7 unconditional.
-/
def MissingBHFunctionalCalculus : Prop :=
  ∀ (D : EBMDirichletStructure μ) (γ : EBMCarreDuChamp D), BHFunctionalCalculus γ

/--
The algebra ℱ ∩ L^∞ presupposed by EBM def. 1.1 (v) and (1.2) (BH 1991 I.3.3.2), written with
existence of products.
-/
def BoundedProducts (D : EBMDirichletStructure μ) : Prop :=
  ∀ f g : D.F, AEBounded (μ := μ) (f : Lp ℝ 2 μ) →
    AEBounded (μ := μ) (g : Lp ℝ 2 μ) → ∃ p : D.F,
      ⇑(p : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (g : Lp ℝ 2 μ) x

/--
conditionally on the named hypothesis `BHFunctionalCalculus` (BH 1991 I.6.1.1–I.6.1.3): a structure
of EBM def. 1.1 equipped with γ has bounded products (via the reconstructed error structure
`toErrorStructure`).
-/
theorem boundedProducts_of_calculus {D : EBMDirichletStructure μ}
    (γ : EBMCarreDuChamp D) (h : BHFunctionalCalculus γ) : BoundedProducts D :=
  products_exist (toErrorStructure γ h)

/--
Proved contract: see `missingBoundedProducts`. BH 1991 I.3.3.2: every structure of EBM def. 1.1 has
bounded products.
-/
def MissingBoundedProducts : Prop :=
  ∀ (D : EBMDirichletStructure μ), BoundedProducts D

/--
The Leibniz rule for γ on bounded domain elements. It is proved by `missingLeibniz` using locality;
the carré-du-champ identity (1.2) alone does not suffice. Reference: Bouleau–Hirsch (1991), ch. I,
§§ 5–6.
-/
def MissingLeibniz : Prop :=
  ∀ (D : EBMDirichletStructure μ) (γ : EBMCarreDuChamp D) (f g p v : D.F),
    AEBounded (μ := μ) (f : Lp ℝ 2 μ) → AEBounded (μ := μ) (g : Lp ℝ 2 μ) →
    (⇑(p : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (g : Lp ℝ 2 μ) x) →
    ⇑(γ.γ p v) =ᵐ[μ] fun x =>
      (f : Lp ℝ 2 μ) x * γ.γ g v x + (g : Lp ℝ 2 μ) x * γ.γ f v x

/--
conditionally on the named hypothesis `BHFunctionalCalculus` (BH 1991 I.6.1.1–I.6.1.3): the
determinant of the BH 1991 matrix Γ(u, u*) (EID, p. 185) is nonnegative a.e.; `ENNReal.ofReal`
therefore does not hide a negative part of the determinant.
-/
theorem bh_det_nonneg {D : EBMDirichletStructure μ} (γ : EBMCarreDuChamp D)
    (h : BHFunctionalCalculus γ) {n : ℕ} (f : Fin n → D.F) :
    ∀ᵐ x ∂μ, 0 ≤ (bhGammaMatrix γ f x).det := by
  have hae : ∀ᵐ x ∂μ, ∀ i j,
      (toErrorStructure γ h).Γ (f i) (f j) x = 2 * γ.γ (f i) (f j) x := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    filter_upwards [Lp.coeFn_smul (2 : ℝ) (γ.γ (f i) (f j))] with x hx
    change ((2 : ℝ) • γ.γ (f i) (f j)) x = _
    rw [hx, Pi.smul_apply, smul_eq_mul]
  filter_upwards [(toErrorStructure γ h).gammaMatrix_posSemidef_ae f, hae] with x hp he
  have hm : (Matrix.of fun i j => (toErrorStructure γ h).Γ (f i) (f j) x) =
      bhGammaMatrix γ f x := by
    ext i j
    exact he i j
  rw [hm] at hp
  exact hp.det_nonneg

end DprBridge.TextStatements
