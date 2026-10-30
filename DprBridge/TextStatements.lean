import DprBridge.Coordinate
import DprBridge.EID
import ErrorCalculus.Dirichlet.ProductRule
import ErrorCalculus.Dirichlet.ExtensionGammaBounds
import ErrorCalculus.Dirichlet.GammaCauchySchwarz

/-!
# EID formulations for probability-space Dirichlet structures

* Eriksson-Bique–Murugan, arXiv:2510.13659v1: def. 1.1 (pp. 1–2), (1.2)–(1.3) (p. 2), def. 1.4 (p.
2), conj. 1.6 and th. 1.7 (p. 3); rem. 2.23 (p. 16).
* Bouleau–Hirsch 1991: ch. V, p. 185 (Dirichlet structure, (P), (M), (OCC), (L), (EID)); cor.
II.5.2.3 (p. 109); Notes, ch. II, section 5 (p. 302); prop. I.4.1.3 (p. 17); prop. I.6.1.1, th.
I.6.1.2, cor. I.6.1.3 (pp. 36–37).

## Main results

EID is verified in Lean for every `ErrorStructure` on a probability space
(`DprBridge.eid_unconditional`; the direction from an error structure to def. 1.1 is proved
unconditionally). This module connects to EBM Theorem 1.7 and the BH det·m formulation under
(P)+(M), conditionally on the named hypothesis `BHFunctionalCalculus` (the conclusions of BH
I.6.1.1–I.6.1.3). That hypothesis follows from EBM axioms (i)–(vi) in (`DprBridge.ChainRuleBridge`).
The printed BH conjecture (sigma-finite m, without (M)) is proved in `DprBridge.BH1991PrintedProof`.
The printed f_* in th. 1.7 is read as φ_*.
-/

noncomputable section
set_option autoImplicit false
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

/-! ## D. Bouleau–Hirsch 1991: (OCC) and (EID) in BH's sense, the conjecture under (P) and (M) -/

section BH
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {D : EBMDirichletStructure μ} (γ : EBMCarreDuChamp D)

/--
BH 1991 prop. I.4.1.3 (p. 17), with Γ = 2γ: for f, g, h ∈ ℱ ∩ L^∞,
ℰ(fh, g) + ℰ(gh, f) − ℰ(h, fg) = ∫ h Γ(f, g) dμ.
-/
theorem bh_product_identity (f g h : D.F) (hf : AEBounded (μ := μ) ((f : Lp ℝ 2 μ) : X → ℝ))
    (hg : AEBounded (μ := μ) ((g : Lp ℝ 2 μ) : X → ℝ))
    (hh : AEBounded (μ := μ) ((h : Lp ℝ 2 μ) : X → ℝ)) (p q r : D.F)
    (hp : ⇑(p : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (h : Lp ℝ 2 μ) x)
    (hq : ⇑(q : Lp ℝ 2 μ) =ᵐ[μ] fun x => (g : Lp ℝ 2 μ) x * (h : Lp ℝ 2 μ) x)
    (hr : ⇑(r : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (g : Lp ℝ 2 μ) x) :
    D.E p g + D.E q f - D.E h r = ∫ x, (h : Lp ℝ 2 μ) x * (2 * γ.γ f g x) ∂μ := by
  have e := γ.product f g h hf hg hh p q r hp hq hr
  have hI : ∫ x, (h : Lp ℝ 2 μ) x * (2 * γ.γ f g x) ∂μ =
      2 * ∫ x, (h : Lp ℝ 2 μ) x * γ.γ f g x ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hI, ← e]
  ring

/--
BH 1991 (EID) on p. 185 and cor. II.5.2.3 (p. 109): the matrix Γ(u, u*) with Γ = 2γ,
evaluated at x.
-/
def bhGammaMatrix {n : ℕ} (u : Fin n → D.F) (x : X) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => 2 * γ.γ (u i) (u j) x

/--
BH 1991 (EID) (p. 185) and the conclusion of cor. II.5.2.3 (p. 109): for every n ∈ ℕ* and
every u ∈ 𝔻ⁿ, u_*((det Γ(u, u*)) · m) ≪ λₙ.
-/
def BH1991EIDProperty : Prop :=
  ∀ n : ℕ, 0 < n → ∀ u : Fin n → D.F,
    (μ.withDensity fun x => ENNReal.ofReal (bhGammaMatrix γ u x).det).map
      (fun x i => (u i : Lp ℝ 2 μ) x) ≪ volume

/--
For measurable d, the measures g_*((d ∨ 0) · μ) and g_*(𝟙_{d > 0} · μ) have the same null
sets; in particular, one is ≪ ν if and only if the other is.
-/
theorem map_withDensity_ofReal_ac_iff {Y : Type*} [MeasurableSpace Y] {d : X → ℝ}
    (hd : Measurable d) {g : X → Y} (hg : Measurable g) (ν : Measure Y) :
    (μ.withDensity fun x => ENNReal.ofReal (d x)).map g ≪ ν ↔
      (μ.withDensity ({x | 0 < d x}.indicator 1)).map g ≪ ν := by
  have hA : MeasurableSet {x | 0 < d x} := measurableSet_lt measurable_const hd
  have e1 : μ.withDensity (fun x => ENNReal.ofReal (d x)) =
      (μ.restrict {x | 0 < d x}).withDensity (fun x => ENNReal.ofReal (d x)) := by
    rw [← withDensity_indicator hA]
    congr 1
    funext x
    by_cases hx : 0 < d x
    · simp [Set.indicator, hx]
    · simp [Set.indicator, hx, ENNReal.ofReal_eq_zero.2 (not_lt.1 hx)]
  have ac1 : μ.withDensity (fun x => ENNReal.ofReal (d x)) ≪ μ.restrict {x | 0 < d x} := by
    rw [e1]
    exact withDensity_absolutelyContinuous _ _
  have ac2 : μ.restrict {x | 0 < d x} ≪ μ.withDensity (fun x => ENNReal.ofReal (d x)) := by
    rw [e1]
    refine withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hd).aemeasurable ?_
    filter_upwards [ae_restrict_mem hA] with x hx
    exact (ENNReal.ofReal_pos.2 hx).ne'
  rw [withDensity_indicator_one hA]
  exact ⟨fun h => (ac2.map hg).trans h, fun h => (ac1.map hg).trans h⟩

/--
The BH 1991 conjecture (Notes, p. 302: does cor. II.5.2.3 hold for general local Dirichlet
forms admitting a carre du champ?), restricted to structures satisfying (P), (M), (OCC), (L)
of ch. V (p. 185), under the named hypothesis `BHFunctionalCalculus`: for every n ∈ ℕ* and
every u ∈ 𝔻ⁿ, u_*((det Γ(u, u*)) · m) ≪ λₙ.
-/
theorem bh_eid_conjecture_PM_of_bhFunctionalCalculus (h : BHFunctionalCalculus γ) :
    BH1991EIDProperty γ := by
  intro n _ u
  have hg : Measurable (fun x i => (u i : Lp ℝ 2 μ) x) :=
    measurable_pi_lambda _ fun i => (Lp.stronglyMeasurable _).measurable
  have hd : Measurable fun x => (bhGammaMatrix γ u x).det :=
    measurable_det_of_measurable fun i j => measurable_const.mul (Lp.stronglyMeasurable _).measurable
  refine (map_withDensity_ofReal_ac_iff hd hg volume).2 ?_
  have hs : {x | 0 < (bhGammaMatrix γ u x).det} = {x | 0 < (ebmGammaMatrix γ u x).det} := by
    ext x
    have hm : bhGammaMatrix γ u x = (2 : ℝ) • ebmGammaMatrix γ u x := by
      ext i j
      simp [bhGammaMatrix, ebmGammaMatrix]
    simp only [Set.mem_setOf_eq, hm, Matrix.det_smul, Fintype.card_fin]
    exact mul_pos_iff_of_pos_left (by positivity)
  rw [hs]
  exact ebm_theorem_1_7_of_bhFunctionalCalculus γ h n u

end BH

/-! ## E. Reverse direction: every error structure is a structure of def. 1.1 -/

section Converse
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable (S : ErrorStructure X μ)

/-- An a.e. bounded factor times an L¹ class is integrable. -/
theorem integrable_mul_L1 {f : Lp ℝ 2 μ} (hf : AEBounded (μ := μ) (f : X → ℝ))
    (G : Lp ℝ 1 μ) : Integrable (fun x => f x * G x) μ := by
  obtain ⟨C, hC⟩ := hf
  exact (L1.integrable_coeFn G).bdd_mul (Lp.aestronglyMeasurable _) hC

/-- (iii) For an error structure: 0 ∨ (f ∧ 1) ∈ 𝔻 and ℰ(0 ∨ (f ∧ 1)) ≤ ℰ(f). -/
theorem markov_of_errorStructure (f : S.dom) : ∃ g : S.dom,
    (⇑(g : Lp ℝ 2 μ) =ᵐ[μ] fun x => max 0 (min ((f : Lp ℝ 2 μ) x) 1)) ∧
      S.energy.E g g ≤ S.energy.E f f := by
  have hL : LipschitzWith 1 (fun t : ℝ => max 0 (min t 1)) :=
    (LipschitzWith.id.min_const 1).const_max 0
  have hm : MemLp (fun x => max 0 (min ((f : Lp ℝ 2 μ) x) 1)) 2 μ :=
    hL.comp_memLp (by simp) (Lp.memLp _)
  obtain ⟨hd, he⟩ := S.normal_contraction hL f (hm.toLp _) hm.coeFn_toLp
  exact ⟨⟨hm.toLp _, hd⟩, hm.coeFn_toLp, he⟩

/-- (v) For an error structure, with γ(f, f) = ½ Γ(f, f). -/
theorem carreDuChamp_of_errorStructure (f : S.dom)
    (hf : AEBounded (μ := μ) ((f : Lp ℝ 2 μ) : X → ℝ)) : ∃ γff : Lp ℝ 1 μ,
    ∀ h : S.dom, AEBounded (μ := μ) ((h : Lp ℝ 2 μ) : X → ℝ) → ∀ p q : S.dom,
      (⇑(p : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (h : Lp ℝ 2 μ) x) →
      (⇑(q : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x ^ 2) →
      S.energy.E p f - (1 / 2 : ℝ) * S.energy.E h q = ∫ x, (h : Lp ℝ 2 μ) x * γff x ∂μ := by
  refine ⟨(1 / 2 : ℝ) • S.Γ f f, fun h hh p q hp hq => ?_⟩
  have hq' : ⇑(q : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (f : Lp ℝ 2 μ) x :=
    hq.mono fun x hx => hx.trans (sq _)
  rw [S.energy_mul f h p f hf hh hp, S.energy.symm h q, S.energy_mul f f q h hf hf hq',
    S.Γ_symm h f]
  have i1 := integrable_mul_L1 hf (S.Γ f h)
  have i2 := integrable_mul_L1 hh (S.Γ f f)
  rw [integral_add i1 i2, integral_add i1 i1]
  have hr : ∫ x, (h : Lp ℝ 2 μ) x * ((1 / 2 : ℝ) • S.Γ f f) x ∂μ =
      (1 / 2 : ℝ) * ∫ x, (h : Lp ℝ 2 μ) x * S.Γ f f x ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (S.Γ f f)] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hr]
  ring

/-- (vi) For an error structure: (f + a) g = 0 a.e. ⇒ ℰ(f, g) = 0. -/
theorem strongLocality_of_errorStructure (f g : S.dom) (a : ℝ)
    (h : ∀ᵐ x ∂μ, ((f : Lp ℝ 2 μ) x + a) * (g : Lp ℝ 2 μ) x = 0) : S.energy.E f g = 0 := by
  rw [ErrorData.energy_apply]
  have hz : ∀ᵐ x ∂μ, S.Γ f g x = 0 := by
    filter_upwards [h, S.gamma_eq_zero_on_const f (-a), S.gamma_eq_zero_on_const g 0,
      S.gamma_cauchy_schwarz f g] with x hx hf hg hcs
    rcases mul_eq_zero.1 hx with h1 | h1
    · rw [hf (by linarith), zero_mul] at hcs
      exact (pow_eq_zero_iff two_ne_zero).1 (le_antisymm hcs (sq_nonneg _))
    · rw [hg h1, mul_zero] at hcs
      exact (pow_eq_zero_iff two_ne_zero).1 (le_antisymm hcs (sq_nonneg _))
  rw [integral_eq_zero_of_ae hz, mul_zero]

/--
Every error structure is a Dirichlet structure in the sense of EBM def. 1.1: ℱ = 𝔻, ℰ = ½ ∫ Γ.
-/
def toEBM : EBMDirichletStructure μ where
  F := S.dom
  E := S.energy.E
  dense := S.dense
  nonneg := S.energy.nonneg
  symm := S.energy.symm
  complete := formComplete_of_isClosed S.energy S.energy_closed
  markov := markov_of_errorStructure S
  one_mem := S.one_mem
  energy_one := S.energy_const 1
  carreDuChamp := carreDuChamp_of_errorStructure S
  strongLocality := strongLocality_of_errorStructure S

/-- Evaluation of ½ Γ(u, v). -/
theorem coeFn_half (u v : S.dom) :
    ⇑(((1 / 2 : ℝ) • S.Γ) u v) =ᵐ[μ] fun x => (1 / 2 : ℝ) * S.Γ u v x := by
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (S.Γ u v)] with x hx
  change ((1 / 2 : ℝ) • S.Γ u v) x = _
  rw [hx, Pi.smul_apply, smul_eq_mul]

/-- (1.2) For an error structure, with γ = ½ Γ. -/
theorem product_of_errorStructure (f g h : S.dom)
    (hf : AEBounded (μ := μ) ((f : Lp ℝ 2 μ) : X → ℝ))
    (hg : AEBounded (μ := μ) ((g : Lp ℝ 2 μ) : X → ℝ))
    (hh : AEBounded (μ := μ) ((h : Lp ℝ 2 μ) : X → ℝ)) (p q r : S.dom)
    (hp : ⇑(p : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (h : Lp ℝ 2 μ) x)
    (hq : ⇑(q : Lp ℝ 2 μ) =ᵐ[μ] fun x => (g : Lp ℝ 2 μ) x * (h : Lp ℝ 2 μ) x)
    (hr : ⇑(r : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (g : Lp ℝ 2 μ) x) :
    (1 / 2 : ℝ) * S.energy.E p g + (1 / 2 : ℝ) * S.energy.E q f - (1 / 2 : ℝ) * S.energy.E h r =
      ∫ x, (h : Lp ℝ 2 μ) x * ((1 / 2 : ℝ) • S.Γ) f g x ∂μ := by
  rw [S.energy_mul f h p g hf hh hp, S.energy_mul g h q f hg hh hq, S.energy.symm h r,
    S.energy_mul f g r h hf hg hr, S.Γ_symm h g, S.Γ_symm h f, S.Γ_symm g f]
  have i1 := integrable_mul_L1 hf (S.Γ g h)
  have i2 := integrable_mul_L1 hh (S.Γ f g)
  have i3 := integrable_mul_L1 hg (S.Γ f h)
  rw [integral_add i1 i2, integral_add i3 i2, integral_add i1 i3]
  have hI : ∫ x, (h : Lp ℝ 2 μ) x * ((1 / 2 : ℝ) • S.Γ) f g x ∂μ =
      (1 / 2 : ℝ) * ∫ x, (h : Lp ℝ 2 μ) x * S.Γ f g x ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_half S f g] with x hx
    rw [hx]
    ring
  rw [hI]
  ring

/-- Continuity of ½ Γ for ℰ₁: ‖½ Γ(f, g)‖_{L¹} ≤ √ℰ₁(f) √ℰ₁(g). -/
theorem norm_half_gamma_le (f g : S.dom) :
    ‖((1 / 2 : ℝ) • S.Γ) f g‖ ≤ 1 * Real.sqrt (S.energy.E f f + ‖(f : Lp ℝ 2 μ)‖ ^ 2) *
      Real.sqrt (S.energy.E g g + ‖(g : Lp ℝ 2 μ)‖ ^ 2) := by
  have h0 := S.toErrorData.norm_gamma_le_energy f g
  have hf : S.energy.seminorm f ≤ Real.sqrt (S.energy.E f f + ‖(f : Lp ℝ 2 μ)‖ ^ 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  have hg : S.energy.seminorm g ≤ Real.sqrt (S.energy.E g g + ‖(g : Lp ℝ 2 μ)‖ ^ 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  have hsf : 0 ≤ S.energy.seminorm f := Real.sqrt_nonneg _
  have hsg : 0 ≤ S.energy.seminorm g := Real.sqrt_nonneg _
  change ‖(1 / 2 : ℝ) • S.Γ f g‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), one_mul]
  calc (1 / 2 : ℝ) * ‖S.Γ f g‖ ≤ S.energy.seminorm f * S.energy.seminorm g := by
        change (1 / 2 : ℝ) * ‖S.Γ f g‖ ≤
          S.toErrorData.energy.seminorm f * S.toErrorData.energy.seminorm g
        linarith
    _ ≤ _ := mul_le_mul hf hg hsg (Real.sqrt_nonneg _)

/-- The carre du champ operator of `toEBM S`: γ = ½ Γ. -/
def toEBMCarreDuChamp : EBMCarreDuChamp (toEBM S) where
  γ := (1 / 2 : ℝ) • S.Γ
  symm f g := by
    change (1 / 2 : ℝ) • S.Γ f g = (1 / 2 : ℝ) • S.Γ g f
    rw [S.Γ_symm]
  nonneg f := by
    filter_upwards [S.Γ_nonneg f, coeFn_half S f f] with x hx hs
    change (0 : ℝ) ≤ ((1 / 2 : ℝ) • S.Γ) f f x
    rw [hs]
    exact mul_nonneg (by norm_num) hx
  continuous := ⟨1, norm_half_gamma_le S⟩
  product := product_of_errorStructure S

/-- The conclusions of BH I.6.1.1–I.6.1.3 hold for `toEBM S` and γ = ½ Γ. -/
theorem bhFunctionalCalculus_of_errorStructure :
    BHFunctionalCalculus (toEBMCarreDuChamp S) := by
  refine ⟨fun f => ?_, fun m hm u G L hC hL w hw => ?_⟩
  · change S.energy.E f f = ∫ x, ((1 / 2 : ℝ) • S.Γ) f f x ∂μ
    rw [ErrorData.energy_apply, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_half S f f] with x hx
    rw [hx]
  · obtain ⟨hd, hch⟩ := S.calc m hm u G L hC hL w hw
    refine ⟨hd, fun v => ?_⟩
    change ⇑(((1 / 2 : ℝ) • S.Γ) (⟨w, hd⟩ : S.dom) v) =ᵐ[μ] fun x =>
      ∑ i, fderiv ℝ G (fun j => (u j : Lp ℝ 2 μ) x) (Pi.single i 1) *
        ((1 / 2 : ℝ) • S.Γ) (u i) v x
    filter_upwards [hch v, coeFn_half S ⟨w, hd⟩ v,
      ae_all_iff.2 fun i => coeFn_half S (u i) v] with x h1 h2 h3
    rw [h2, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h3 i]
    ring

/--
Round trip: the error structure reconstructed from `toEBM S` has the same domain
(definitionally) and the same Γ as S.
-/
theorem toErrorStructure_toEBM_Γ (u v : S.dom) :
    (toErrorStructure (toEBMCarreDuChamp S) (bhFunctionalCalculus_of_errorStructure S)).Γ u v =
      S.Γ u v := by
  change (2 : ℝ) • ((1 / 2 : ℝ) • S.Γ u v) = S.Γ u v
  rw [smul_smul]
  norm_num

/--
The EID property in EBM's sense (def. 1.4) for the Dirichlet structure of an arbitrary
error structure.
-/
theorem ebm_eid_of_errorStructure : EBMEIDProperty (toEBMCarreDuChamp S) :=
  ebm_theorem_1_7_of_bhFunctionalCalculus _ (bhFunctionalCalculus_of_errorStructure S)

/--
The BH 1991 (EID) property (p. 185) for the Dirichlet structure of an arbitrary error structure.
-/
theorem bh_eid_of_errorStructure : BH1991EIDProperty (toEBMCarreDuChamp S) :=
  bh_eid_conjecture_PM_of_bhFunctionalCalculus _ (bhFunctionalCalculus_of_errorStructure S)

end Converse

/-! ## F. Instances and finiteness -/

/--
Instance: the library's one-dimensional Ornstein–Uhlenbeck structure, viewed as a
Dirichlet structure in the sense of EBM def. 1.1.
-/
def ebmOU : EBMDirichletStructure (ProbabilityTheory.gaussianReal 0 1) := toEBM ouStructure

/-- The one-dimensional Ornstein–Uhlenbeck structure has EBM's EID property. -/
theorem ebm_eid_ou : EBMEIDProperty (toEBMCarreDuChamp ouStructure) :=
  ebm_eid_of_errorStructure ouStructure

/-- If the constant 1 is square integrable for μ, the measure μ is finite. -/
theorem isFiniteMeasure_of_one_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (h : MemLp (fun _ : X => (1 : ℝ)) 2 μ) : IsFiniteMeasure μ := by
  rw [memLp_const_iff (by norm_num) (by norm_num)] at h
  rcases h with h | h
  · exact absurd h one_ne_zero
  · exact ⟨h⟩

end DprBridge.TextStatements
