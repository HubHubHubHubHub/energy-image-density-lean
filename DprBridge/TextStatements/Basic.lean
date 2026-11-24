import DprBridge.Coordinate
import ErrorCalculus.Dirichlet.ProductRule
import DprBridge.EID.Basic
import ErrorCalculus.Dirichlet.ExtensionGammaBounds.Basic

/-!
# EID formulations for probability-space Dirichlet structures

This file contains the definitions and results of the development of `DprBridge.TextStatements` that
the main statements of the library (the head theorems listed in the README of the repository) use,
together with the other results of the sections they belong to. `DprBridge.TextStatements` imports
it and continues the development.

## Main definitions

* `TextStatements.toErrorStructure`: The error structure associated with a structure of def. 1.1
  equipped with its γ, under the named hypothesis `BHFunctionalCalculus`: domain ℱ, Γ = 2γ.
* `TextStatements.FormComplete`: The domain `F` is complete for `ℰ₁ = E + ‖·‖²`: every `ℰ₁`-Cauchy
  sequence in `F` converges in `ℰ₁` to some `v : F`.
* `TextStatements.EBMDirichletStructure`: (X, 𝒳, μ) is a PROBABILITY space (the printed text). ℱ ⊂
  L²(μ), ℰ : ℱ × ℱ → ℝ is bilinear.
* `TextStatements.EBMCarreDuChamp`: A carré du champ of an EBM Dirichlet structure: a symmetric
  bilinear `γ` into `L¹(μ)`, nonnegative on the diagonal, `ℰ₁`-continuous, satisfying the product
  rule (1.2) on bounded elements.
* `TextStatements.ebmGammaMatrix`: The matrix with `(i, j)` entry `γ.γ (f i) (f j) x`, the EBM carré
  du champ matrix `γ(f)` evaluated at `x`.
* `TextStatements.EBMEIDProperty`: For every `n` and `f : Fin n → D.F`, the image under `x ↦ (f i
  x)ᵢ` of `μ` restricted to `{x | 0 < (ebmGammaMatrix γ f x).det}` is `≪ volume`.
* `TextStatements.EBMConjecture_1_6`: Every EBM Dirichlet structure on a probability space, with any
  associated carré du champ `γ`, has the energy image density property `EBMEIDProperty γ`.
* `TextStatements.BHFunctionalCalculus`: Named hypothesis: adapted consequences of BH 1991 prop.
  I.6.1.1, th. I.6.1.2 and cor. I.6.1.3 (pp. 36–37), rewritten with γ = Γ/2: ℰ(f, f) = ∫ γ(f, f) dμ
  for f ∈ ℱ; and, for m > 0, u ∈ ℱᵐ, G of class C¹ and Lipschitz, every class w of G ∘ u lies in ℱ
  and γ(w, v) = Σᵢ ∂ᵢG(u) γ(uᵢ, v) a.e. for every v ∈ ℱ.
* `TextStatements.toErrorData`: The associated error data: domain ℱ, Γ = 2γ.

## Main statements

* `TextStatements.ebm_conjecture_1_6_of_bhFunctionalCalculus`: If every EBM Dirichlet structure with
  its carré du champ satisfies `BHFunctionalCalculus γ`, then `EBMConjecture_1_6` holds.
* `TextStatements.formComplete_of_isClosed`: The library's `QuadForm.IsClosed` property implies
  completeness for ℰ₁ (`FormComplete`).
-/
noncomputable section
open MeasureTheory Filter Topology ErrorCalculus
open scoped NNReal ENNReal

namespace DprBridge.TextStatements

/-! ## A. Closedness (EBM (ii)) and closedness of `QuadForm` -/

section Closed
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/--
EBM def. 1.1 (ii), second half: ℱ is complete for the norm of
ℰ₁(f, g) = ℰ(f, g) + ⟨f, g⟩_{L²(μ)}; every ℰ₁-Cauchy sequence converges in ℰ₁ to a point of ℱ.
-/
def FormComplete (F : Submodule ℝ (Lp ℝ 2 μ)) (E : F →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Prop :=
  ∀ u : ℕ → F, (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      E (u m - u n) (u m - u n) + ‖((u m - u n : F) : Lp ℝ 2 μ)‖ ^ 2 < ε) →
    ∃ v : F, Tendsto (fun n => E (u n - v) (u n - v) + ‖((u n - v : F) : Lp ℝ 2 μ)‖ ^ 2)
      atTop (𝓝 0)

/-- Completeness for ℰ₁ (`FormComplete`) implies the library's `QuadForm.IsClosed` property. -/
theorem isClosed_of_formComplete (Q : QuadForm (Lp ℝ 2 μ)) (h : FormComplete Q.dom Q.E) :
    Q.IsClosed := by
  intro u hu v hv
  rw [Q.isCauchy_iff] at hu
  obtain ⟨hL, hE⟩ := hu
  have hc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      Q.E (u m - u n) (u m - u n) + ‖((u m - u n : Q.dom) : Lp ℝ 2 μ)‖ ^ 2 < ε := by
    intro ε hε
    have hr : 0 < Real.sqrt (ε / 2) := Real.sqrt_pos.2 (by linarith)
    have hr2 : Real.sqrt (ε / 2) ^ 2 = ε / 2 := Real.sq_sqrt (by linarith)
    obtain ⟨N₁, hN₁⟩ := hE _ hr
    obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.1 hL _ hr
    refine ⟨max N₁ N₂, fun m hm n hn => ?_⟩
    have h1 := hN₁ m (le_of_max_le_left hm) n (le_of_max_le_left hn)
    have h2 := hN₂ m (le_of_max_le_right hm) n (le_of_max_le_right hn)
    rw [dist_eq_norm, ← Submodule.coe_sub] at h2
    have hs : Q.seminorm (u m - u n) ^ 2 = Q.E (u m - u n) (u m - u n) := by
      rw [QuadForm.seminorm, Real.sq_sqrt (Q.nonneg _)]
    have h0 : 0 ≤ Q.seminorm (u m - u n) := Real.sqrt_nonneg _
    have h3 : 0 ≤ ‖((u m - u n : Q.dom) : Lp ℝ 2 μ)‖ := norm_nonneg _
    nlinarith
  obtain ⟨v', hv'⟩ := h u hc
  have hn : Tendsto (fun n => ‖((u n - v' : Q.dom) : Lp ℝ 2 μ)‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) (fun n => le_add_of_nonneg_left (Q.nonneg _)) hv'
  have hn' : Tendsto (fun n => ‖(u n : Lp ℝ 2 μ) - v'‖) atTop (𝓝 0) := by
    have hs := hn.sqrt
    rw [Real.sqrt_zero] at hs
    refine hs.congr fun n => ?_
    rw [Real.sqrt_sq (norm_nonneg _), Submodule.coe_sub]
  have hlim : Tendsto (fun n => (u n : Lp ℝ 2 μ)) atTop (𝓝 (v' : Lp ℝ 2 μ)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hn'
  have hvv : v = v' := tendsto_nhds_unique hv hlim
  subst hvv
  refine ⟨v'.2, ?_⟩
  simp only [Subtype.coe_eta]
  exact squeeze_zero (fun n => Q.nonneg _) (fun n => le_add_of_nonneg_right (sq_nonneg _)) hv'

/-- The library's `QuadForm.IsClosed` property implies completeness for ℰ₁ (`FormComplete`). -/
theorem formComplete_of_isClosed (Q : QuadForm (Lp ℝ 2 μ)) (h : Q.IsClosed) :
    FormComplete Q.dom Q.E := by
  intro u hu
  have hL : CauchySeq (fun n => (u n : Lp ℝ 2 μ)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hu (ε ^ 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    have h0 := Q.nonneg (u m - u n)
    have h3 : 0 ≤ ‖((u m - u n : Q.dom) : Lp ℝ 2 μ)‖ := norm_nonneg _
    rw [dist_eq_norm, ← Submodule.coe_sub]
    nlinarith
  have hc : Q.IsCauchy u := by
    rw [Q.isCauchy_iff]
    refine ⟨hL, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := hu (ε ^ 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    rw [QuadForm.seminorm, Real.sqrt_lt' hε]
    nlinarith [sq_nonneg ‖((u m - u n : Q.dom) : Lp ℝ 2 μ)‖]
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hL
  obtain ⟨hvd, hE⟩ := h u hc v hv
  refine ⟨⟨v, hvd⟩, ?_⟩
  have h2 : Tendsto (fun n => ‖((u n - ⟨v, hvd⟩ : Q.dom) : Lp ℝ 2 μ)‖ ^ 2) atTop (𝓝 0) := by
    have hp := (tendsto_iff_norm_sub_tendsto_zero.1 hv).pow 2
    rw [zero_pow two_ne_zero] at hp
    refine hp.congr fun n => ?_
    rw [Submodule.coe_sub]
  simpa using hE.add h2

end Closed

/-! ## B. EBM definition 1.1, (1.2)–(1.3), definition 1.4, conjecture 1.6 -/

section EBM
variable {X : Type*} [MeasurableSpace X]

/--
EBM encoding, definition 1.1 (pp. 1–2), axiom by axiom. (X, 𝒳, μ) is a PROBABILITY space
(the printed text). ℱ ⊂ L²(μ), ℰ : ℱ × ℱ → ℝ is bilinear;
(i) ℱ is dense in L²(μ), ℰ(f, f) ≥ 0;
(ii) ℱ is a Hilbert space for ℰ₁ = ℰ + ⟨·,·⟩_{L²}: ℰ is symmetric and ℱ is complete for ℰ₁;
(iii) f ∈ ℱ ⇒ f̃ = 0 ∨ (f ∧ 1) ∈ ℱ and ℰ(f̃, f̃) ≤ ℰ(f, f);
(iv) 𝟙 ∈ ℱ and ℰ(𝟙, 𝟙) = 0;
(v) for f ∈ ℱ ∩ L^∞ there exists γ(f, f) ∈ L¹ such that, for h ∈ ℱ ∩ L^∞,
 ℰ(fh, f) − ½ ℰ(h, f²) = ∫ h γ(f, f) dμ (presuppositional reading: the equality is
 required for all elements p, q of ℱ representing fh and f²; their existence is a separate
 obligation);
(vi) f, g ∈ ℱ, a ∈ ℝ, (f + a) g = 0 μ-a.e. ⇒ ℰ(f, g) = 0.
-/
structure EBMDirichletStructure (μ : Measure X) [IsProbabilityMeasure μ] where
  /-- The domain ℱ, a subspace of L²(X, μ). -/
  F : Submodule ℝ (Lp ℝ 2 μ)
  /-- The form ℰ, bilinear on ℱ. -/
  E : F →ₗ[ℝ] F →ₗ[ℝ] ℝ
  /-- (i) ℱ is dense in L²(μ). -/
  dense : Dense (F : Set (Lp ℝ 2 μ))
  /-- (i) ℰ(f, f) ≥ 0. -/
  nonneg : ∀ f : F, 0 ≤ E f f
  /-- (ii) ℰ₁ is an inner product: ℰ is symmetric. -/
  symm : ∀ f g : F, E f g = E g f
  /-- (ii) ℱ is complete for ℰ₁. -/
  complete : FormComplete F E
  /-- (iii) The Markov property. -/
  markov : ∀ f : F, ∃ g : F,
    (⇑(g : Lp ℝ 2 μ) =ᵐ[μ] fun x => max 0 (min ((f : Lp ℝ 2 μ) x) 1)) ∧ E g g ≤ E f f
  /-- (iv) 𝟙 ∈ ℱ. -/
  one_mem : Lp.const 2 μ (1 : ℝ) ∈ F
  /-- (iv) ℰ(𝟙, 𝟙) = 0. -/
  energy_one : E ⟨Lp.const 2 μ (1 : ℝ), one_mem⟩ ⟨Lp.const 2 μ (1 : ℝ), one_mem⟩ = 0
  /-- (v) Existence of the carre du champ operator on ℱ ∩ L^∞. -/
  carreDuChamp : ∀ f : F, AEBounded (μ := μ) ((f : Lp ℝ 2 μ) : X → ℝ) → ∃ γff : Lp ℝ 1 μ,
    ∀ h : F, AEBounded (μ := μ) ((h : Lp ℝ 2 μ) : X → ℝ) → ∀ p q : F,
      (⇑(p : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (h : Lp ℝ 2 μ) x) →
      (⇑(q : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x ^ 2) →
      E p f - (1 / 2 : ℝ) * E h q = ∫ x, (h : Lp ℝ 2 μ) x * γff x ∂μ
  /-- (vi) Strong locality. -/
  strongLocality : ∀ f g : F, ∀ a : ℝ,
    (∀ᵐ x ∂μ, ((f : Lp ℝ 2 μ) x + a) * (g : Lp ℝ 2 μ) x = 0) → E f g = 0

/--
EBM p. 2, following BH 1991 prop. I.4.1.3 (p. 17): the associated carre du champ operator,
γ : ℱ × ℱ → L¹(μ), bilinear, symmetric, nonnegative (γ(f, f) ≥ 0 a.e.), continuous for the ℰ₁
norm (bound by a constant C), and satisfying (1.2): for f, g, h ∈ ℱ ∩ L^∞,
½ ℰ(fh, g) + ½ ℰ(gh, f) − ½ ℰ(h, fg) = ∫ h γ(f, g) dμ (for all p, q, r ∈ ℱ representing
fh, gh, fg).
-/
structure EBMCarreDuChamp {μ : Measure X} [IsProbabilityMeasure μ]
    (D : EBMDirichletStructure μ) where
  /-- The operator γ. -/
  γ : D.F →ₗ[ℝ] D.F →ₗ[ℝ] Lp ℝ 1 μ
  /-- The operator γ is symmetric. -/
  symm : ∀ f g : D.F, γ f g = γ g f
  /-- The operator γ is nonnegative on the diagonal. -/
  nonneg : ∀ f : D.F, 0 ≤ᵐ[μ] ⇑(γ f f)
  /-- The operator γ is continuous from (ℱ, ℰ₁) × (ℱ, ℰ₁) to L¹(μ). -/
  continuous : ∃ C : ℝ, ∀ f g : D.F, ‖γ f g‖ ≤
    C * Real.sqrt (D.E f f + ‖(f : Lp ℝ 2 μ)‖ ^ 2) * Real.sqrt (D.E g g + ‖(g : Lp ℝ 2 μ)‖ ^ 2)
  /-- (1.2). -/
  product : ∀ f g h : D.F, AEBounded (μ := μ) ((f : Lp ℝ 2 μ) : X → ℝ) →
    AEBounded (μ := μ) ((g : Lp ℝ 2 μ) : X → ℝ) → AEBounded (μ := μ) ((h : Lp ℝ 2 μ) : X → ℝ) →
    ∀ p q r : D.F,
    (⇑(p : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (h : Lp ℝ 2 μ) x) →
    (⇑(q : Lp ℝ 2 μ) =ᵐ[μ] fun x => (g : Lp ℝ 2 μ) x * (h : Lp ℝ 2 μ) x) →
    (⇑(r : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (g : Lp ℝ 2 μ) x) →
    (1 / 2 : ℝ) * D.E p g + (1 / 2 : ℝ) * D.E q f - (1 / 2 : ℝ) * D.E h r =
      ∫ x, (h : Lp ℝ 2 μ) x * γ f g x ∂μ

variable {μ : Measure X} [IsProbabilityMeasure μ] {D : EBMDirichletStructure μ}

/-- EBM (1.3): the carre du champ matrix γ(f) = [γ(fᵢ, fⱼ)], evaluated at x. -/
def ebmGammaMatrix (γ : EBMCarreDuChamp D) {n : ℕ} (f : Fin n → D.F) (x : X) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => γ.γ (f i) (f j) x

/--
EBM definition 1.4 (p. 2): the energy image density property: for every n ∈ ℕ and every f ∈ ℱⁿ,
f_*(𝟙_{det γ(f) > 0} · μ) ≪ ℒⁿ.
-/
def EBMEIDProperty (γ : EBMCarreDuChamp D) : Prop :=
  ∀ n : ℕ, ∀ f : Fin n → D.F,
    (μ.withDensity ({x | 0 < (ebmGammaMatrix γ f x).det}.indicator 1)).map
      (fun x i => (f i : Lp ℝ 2 μ) x) ≪ volume

end EBM

/--
EBM conjecture 1.6 (p. 3), asserted by Theorem 1.7: every Dirichlet structure (def.
1.1), with its associated carre du champ operator, has the EID property.
-/
def EBMConjecture_1_6 : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (D : EBMDirichletStructure μ) (γ : EBMCarreDuChamp D), EBMEIDProperty γ

/-! ## C. Conclusions of BH 1991 I.6.1 (named hypothesis) -/

section Calculus
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {D : EBMDirichletStructure μ}

/--
Named hypothesis: adapted consequences of BH 1991 prop. I.6.1.1, th. I.6.1.2 and cor. I.6.1.3
(pp. 36–37), rewritten with γ = Γ/2:
ℰ(f, f) = ∫ γ(f, f) dμ for f ∈ ℱ; and, for m > 0, u ∈ ℱᵐ, G of class C¹ and Lipschitz,
every class w of G ∘ u lies in ℱ and γ(w, v) = Σᵢ ∂ᵢG(u) γ(uᵢ, v) a.e. for every v ∈ ℱ.
-/
def BHFunctionalCalculus (γ : EBMCarreDuChamp D) : Prop :=
  (∀ f : D.F, D.E f f = ∫ x, γ.γ f f x ∂μ) ∧
  ∀ (m : ℕ), 0 < m → ∀ (u : Fin m → D.F) (G : (Fin m → ℝ) → ℝ) (L : ℝ≥0),
    ContDiff ℝ 1 G → LipschitzWith L G →
    ∀ w : Lp ℝ 2 μ, (⇑w =ᵐ[μ] fun x => G (fun i => (u i : Lp ℝ 2 μ) x)) →
      ∃ hw : w ∈ D.F, ∀ v : D.F, ⇑(γ.γ ⟨w, hw⟩ v) =ᵐ[μ] fun x =>
        ∑ i, fderiv ℝ G (fun j => (u j : Lp ℝ 2 μ) x) (Pi.single i 1) * γ.γ (u i) v x

variable (γ : EBMCarreDuChamp D)

/-- Polarization: if ℰ(f, f) = ∫ γ(f, f) for every f ∈ ℱ, then ℰ(f, g) = ∫ γ(f, g). -/
theorem energy_eq_integral (h : ∀ f : D.F, D.E f f = ∫ x, γ.γ f f x ∂μ) (u v : D.F) :
    D.E u v = ∫ x, γ.γ u v x ∂μ := by
  have I : ∀ g : Lp ℝ 1 μ, ∫ x, g x ∂μ = integralL1 g := fun g => rfl
  have h1 := h (u + v)
  have hu := h u
  have hv := h v
  simp only [I, map_add, LinearMap.add_apply] at h1 hu hv ⊢
  rw [D.symm v u, γ.symm v u] at h1
  linarith

/-- The associated error data: domain ℱ, Γ = 2γ. -/
def toErrorData : ErrorData X μ where
  dom := D.F
  Γ := (2 : ℝ) • γ.γ
  Γ_symm u v := by
    change (2 : ℝ) • γ.γ u v = (2 : ℝ) • γ.γ v u
    rw [γ.symm]
  Γ_nonneg u := by
    filter_upwards [γ.nonneg u, Lp.coeFn_smul (2 : ℝ) (γ.γ u u)] with x hx hs
    change (0 : ℝ) ≤ ((2 : ℝ) • γ.γ u u) x
    rw [hs, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg zero_le_two hx

/-- The energy ½ ∫ Γ of the associated data is ℰ, assuming ℰ(f, f) = ∫ γ(f, f). -/
theorem toErrorData_energy_E (h : ∀ f : D.F, D.E f f = ∫ x, γ.γ f f x ∂μ) (u v : D.F) :
    (toErrorData γ).energy.E u v = D.E u v := by
  rw [ErrorData.energy_apply, energy_eq_integral γ h u v]
  change (1 / 2 : ℝ) * integralL1 ((2 : ℝ) • γ.γ u v) = integralL1 (γ.γ u v)
  rw [map_smul, smul_eq_mul]
  ring

/-- The energy of the associated data is closed, assuming ℰ(f, f) = ∫ γ(f, f). -/
theorem toErrorData_energy_isClosed (h : ∀ f : D.F, D.E f f = ∫ x, γ.γ f f x ∂μ) :
    (toErrorData γ).energy.IsClosed := by
  apply isClosed_of_formComplete
  have hEq : (toErrorData γ).energy.E = D.E :=
    LinearMap.ext₂ fun u v => toErrorData_energy_E γ h u v
  rw [hEq]
  exact D.complete

/--
The error structure associated with a structure of def. 1.1 equipped with its γ, under the named
hypothesis `BHFunctionalCalculus`: domain ℱ, Γ = 2γ.
-/
def toErrorStructure (h : BHFunctionalCalculus γ) : ErrorStructure X μ where
  toErrorData := toErrorData γ
  dense := D.dense
  «calc» m hm u G L hC hL w hw := by
    obtain ⟨hd, hch⟩ := h.2 m hm u G L hC hL w hw
    refine ⟨hd, fun v => ?_⟩
    filter_upwards [hch v, Lp.coeFn_smul (2 : ℝ) (γ.γ ⟨w, hd⟩ v),
      ae_all_iff.2 fun i => Lp.coeFn_smul (2 : ℝ) (γ.γ (u i) v)] with x h1 h2 h3
    change ((2 : ℝ) • γ.γ ⟨w, hd⟩ v) x = ∑ i, fderiv ℝ G (fun j => (u j : Lp ℝ 2 μ) x)
      (Pi.single i 1) * ((2 : ℝ) • γ.γ (u i) v) x
    rw [h2, Pi.smul_apply, smul_eq_mul, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h3 i, Pi.smul_apply, smul_eq_mul]
    ring
  energy_closed := toErrorData_energy_isClosed γ h.1
  one_mem := D.one_mem

/-- Measurability of the determinant of a matrix of measurable functions. -/
theorem measurable_det_of_measurable {n : ℕ} {b : Fin n → Fin n → X → ℝ}
    (hb : ∀ i j, Measurable (b i j)) : Measurable fun x => (Matrix.of fun i j => b i j x).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  exact Finset.measurable_sum _ fun σ _ =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => hb (σ i) i)

/-- The measure of EBM def. 1.4 equals `eidMeasure` of the associated error structure. -/
theorem ebmEIDMeasure_eq (h : BHFunctionalCalculus γ) {n : ℕ} (f : Fin n → D.F) :
    (μ.withDensity ({x | 0 < (ebmGammaMatrix γ f x).det}.indicator 1)).map
      (fun x i => (f i : Lp ℝ 2 μ) x) = (toErrorStructure γ h).eidMeasure f := by
  have hmeas : Measurable fun x => (ebmGammaMatrix γ f x).det :=
    measurable_det_of_measurable fun i j => (Lp.stronglyMeasurable _).measurable
  rw [withDensity_indicator_one (measurableSet_lt measurable_const hmeas)]
  have hae : ∀ᵐ x ∂μ, ∀ i j, (toErrorStructure γ h).Γ (f i) (f j) x = 2 * γ.γ (f i) (f j) x := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    filter_upwards [Lp.coeFn_smul (2 : ℝ) (γ.γ (f i) (f j))] with x hx
    change ((2 : ℝ) • γ.γ (f i) (f j)) x = _
    rw [hx, Pi.smul_apply, smul_eq_mul]
  have hset : {x | 0 < (ebmGammaMatrix γ f x).det} =ᵐ[μ]
      {ω | 0 < (Matrix.of fun i j => (toErrorStructure γ h).Γ (f i) (f j) ω).det} := by
    refine Filter.eventuallyEq_set.2 (hae.mono fun x hx => ?_)
    have hm : (Matrix.of fun i j => (toErrorStructure γ h).Γ (f i) (f j) x) =
        (2 : ℝ) • ebmGammaMatrix γ f x := by
      ext i j
      simp [ebmGammaMatrix, hx i j]
    simp only [Set.mem_setOf_eq, hm, Matrix.det_smul, Fintype.card_fin]
    exact (mul_pos_iff_of_pos_left (by positivity)).symm
  rw [Measure.restrict_congr_set hset]
  exact Measure.map_congr (ae_restrict_of_ae ((toErrorStructure γ h).coeFn_representativeVec f))

/--
EBM Theorem 1.7 (p. 3), under the named hypothesis `BHFunctionalCalculus` (the conclusions of
BH I.6.1.1–I.6.1.3): for every n ∈ ℕ and every φ ∈ ℱⁿ, φ_*(𝟙_{det γ(φ) > 0} · μ) ≪ ℒⁿ.
Only the following parts of def. 1.1 are used: density (i), symmetry and completeness (ii),
𝟙 ∈ ℱ (iv); and, for γ, symmetry and positivity.
-/
theorem ebm_theorem_1_7_of_bhFunctionalCalculus (h : BHFunctionalCalculus γ) :
    EBMEIDProperty γ := by
  intro n f
  rw [ebmEIDMeasure_eq γ h f]
  exact DprBridge.eid_unconditional (toErrorStructure γ h) f

end Calculus

/--
EBM conjecture 1.6, reduced to the named hypothesis: if every structure of def. 1.1
equipped with its γ satisfies the conclusions of BH I.6.1.1–I.6.1.3, each has the EID property.
-/
theorem ebm_conjecture_1_6_of_bhFunctionalCalculus
    (h : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
      (D : EBMDirichletStructure μ) (γ : EBMCarreDuChamp D), BHFunctionalCalculus γ) :
    EBMConjecture_1_6 :=
  fun X _ μ _ D γ => ebm_theorem_1_7_of_bhFunctionalCalculus γ (h X μ D γ)

end DprBridge.TextStatements
