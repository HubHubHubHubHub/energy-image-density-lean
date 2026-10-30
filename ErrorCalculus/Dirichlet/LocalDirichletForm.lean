import ErrorCalculus.Dirichlet.QuadForm
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# framework, constants, staircase contractions

## Main results
Framework: a Dirichlet form in the sense of Eriksson-Bique–Murugan definition 1.1 (arXiv:2510.13659,
pp. 1–2), axioms (i)–(iv) and (vi): a closed form on L²(μ), with μ a probability measure, only the
unit contraction (iii), 1 ∈ 𝔻 and ℰ(1, 1) = 0 (iv), strong locality (vi) = (L₂) of BH 1991 I.5.1.3
(p. 29). The field ℰ(1, 1) = 0 is retained as stated by EBM (BH cor. I.5.1.4, p. 31, derives it from
(L₂) and 1 ∈ 𝔻; this redundancy is not formalized here). Two-level clamps a ∨ (f ∧ b) (BH ex. 3.1
and prop. I.3.3.1, pp. 14–15) and their staircase orthogonality by (L₂). Local route: locality
replaces BH's semigroup.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option maxHeartbeats 800000

namespace ErrorCalculus

/-! ## A. Framework, constants, staircase contractions -/

/--
Eriksson-Bique–Murugan, def. 1.1 (pp. 1–2), axioms (i)–(iv) and (vi), and BH 1991 ch. V (p. 185:
(P), (M), (L)): a closed form on L²(μ), with μ a probability measure.

The field `form`: a nonnegative symmetric bilinear form on a subspace 𝔻 of L²(μ) (EBM (i)–(ii));
`dense`: 𝔻 dense in L²(μ) (EBM (i)); `closed`: sequential closedness (EBM (ii)); `markov`: f ∈ 𝔻 ⇒ 0
∨ (f ∧ 1) ∈ 𝔻 and ℰ(0 ∨ (f ∧ 1)) ≤ ℰ(f) (EBM (iii), the unit contraction alone); `one_mem`,
`energy_one`: 1 ∈ 𝔻 and ℰ(1, 1) = 0 (EBM (iv)); `strongLocality`: (f + a) g = 0 a.e. ⇒ ℰ(f, g) = 0
(EBM (vi), (L₂) of BH I.5.1.3). No carre du champ is postulated (EBM (v) is not a field).
-/
structure LocalDirichletForm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] where
  /-- The form ℰ and its domain 𝔻 ⊂ L²(μ). -/
  form : QuadForm (Lp ℝ 2 μ)
  /-- EBM (i): 𝔻 is dense in L²(μ). -/
  dense : Dense (form.dom : Set (Lp ℝ 2 μ))
  /-- EBM (ii): the form is closed. -/
  closed : form.IsClosed
  /-- EBM (iii): the unit contraction. -/
  markov : ∀ f : form.dom, ∃ g : form.dom,
    (⇑(g : Lp ℝ 2 μ) =ᵐ[μ] fun x => max 0 (min ((f : Lp ℝ 2 μ) x) 1)) ∧
      form.E g g ≤ form.E f f
  /-- EBM (iv) : 1 ∈ 𝔻. -/
  one_mem : Lp.const 2 μ (1 : ℝ) ∈ form.dom
  /-- EBM (iv) : ℰ(1, 1) = 0. -/
  energy_one : form.E ⟨Lp.const 2 μ (1 : ℝ), one_mem⟩ ⟨Lp.const 2 μ (1 : ℝ), one_mem⟩ = 0
  /-- EBM (vi): strong locality. -/
  strongLocality : ∀ f g : form.dom, ∀ a : ℝ,
    (∀ᵐ x ∂μ, ((f : Lp ℝ 2 μ) x + a) * (g : Lp ℝ 2 μ) x = 0) → form.E f g = 0

/-- Two elements of a form domain in L² that are equal a.e. are equal. -/
theorem QuadForm.dom_ext_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Q : QuadForm (Lp ℝ 2 μ)} {g₁ g₂ : Q.dom}
    (h : ⇑(g₁ : Lp ℝ 2 μ) =ᵐ[μ] ⇑(g₂ : Lp ℝ 2 μ)) : g₁ = g₂ :=
  Subtype.ext (Lp.ext h)

/-- ℰ(c u, c u) = c² ℰ(u, u). -/
theorem QuadForm.energy_smul_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Q : QuadForm H) (c : ℝ) (u : Q.dom) : Q.E (c • u) (c • u) = c ^ 2 * Q.E u u := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Expansion of ℰ(u + v, u + v). -/
theorem QuadForm.energy_add_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Q : QuadForm H) (u v : Q.dom) :
    Q.E (u + v) (u + v) = Q.E u u + 2 * Q.E u v + Q.E v v := by
  simp only [map_add, LinearMap.add_apply]
  rw [Q.symm v u]
  ring

/-- The identity t ↦ a + c (0 ∨ (s ∧ 1)) = a ∨ ((a + c s) ∧ (a + c)), c ≥ 0. -/
theorem clamp_affine_aux {a c : ℝ} (hc : 0 ≤ c) (s : ℝ) :
    a + c * max 0 (min s 1) = max a (min (a + c * s) (a + c)) := by
  rw [mul_max_of_nonneg _ _ hc, mul_min_of_nonneg _ _ hc, mul_zero, mul_one,
    ← max_add_add_left, ← min_add_add_left, add_zero]

namespace LocalDirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (D : LocalDirichletForm μ)

/-- The constant 1 as an element of 𝔻. -/
def one : D.form.dom := ⟨Lp.const 2 μ (1 : ℝ), D.one_mem⟩

/--
The distinguished domain constant is represented by the constant function one almost everywhere.
-/
theorem coeFn_one : ⇑((D.one : D.form.dom) : Lp ℝ 2 μ) =ᵐ[μ] fun _ => (1 : ℝ) :=
  Lp.coeFn_const 2 μ (1 : ℝ)

/-- ℰ(1, v) = 0 for every v ∈ 𝔻 (Cauchy–Schwarz and ℰ(1, 1) = 0). -/
theorem energy_one_left (v : D.form.dom) : D.form.E D.one v = 0 := by
  have h := D.form.cauchy_schwarz D.one v
  have h0 : D.form.seminorm D.one = 0 := by
    rw [QuadForm.seminorm]
    change Real.sqrt (D.form.E ⟨Lp.const 2 μ (1 : ℝ), D.one_mem⟩
      ⟨Lp.const 2 μ (1 : ℝ), D.one_mem⟩) = 0
    rw [D.energy_one, Real.sqrt_zero]
  rw [h0, zero_mul] at h
  exact abs_nonpos_iff.mp h

/-- Pairing any domain element with the constant one gives zero energy. -/
theorem energy_one_right (v : D.form.dom) : D.form.E v D.one = 0 := by
  rw [D.form.symm]
  exact D.energy_one_left v

/-- Energy is invariant under addition of constants. -/
theorem energy_add_smul_one (f g : D.form.dom) (a b : ℝ) :
    D.form.E (f + a • D.one) (g + b • D.one) = D.form.E f g := by
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    D.energy_one_left, D.energy_one_right, mul_zero, add_zero]

/-- Adding a real constant to the second argument does not change the energy pairing. -/
theorem energy_add_smul_one_right (f g : D.form.dom) (b : ℝ) :
    D.form.E f (g + b • D.one) = D.form.E f g := by
  simp only [map_add, map_smul, smul_eq_mul, D.energy_one_right, mul_zero, add_zero]

/-- Representative of g + b · 1. -/
theorem coeFn_add_smul_one (g : D.form.dom) (b : ℝ) :
    ⇑((g + b • D.one : D.form.dom) : Lp ℝ 2 μ) =ᵐ[μ] fun x => (g : Lp ℝ 2 μ) x + b := by
  rw [Submodule.coe_add, Submodule.coe_smul]
  filter_upwards [Lp.coeFn_add (g : Lp ℝ 2 μ) (b • ((D.one : D.form.dom) : Lp ℝ 2 μ)),
    Lp.coeFn_smul b ((D.one : D.form.dom) : Lp ℝ 2 μ), D.coeFn_one] with x h1 h2 h3
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, smul_eq_mul, mul_one]

/-- Representative of c · g. -/
theorem coeFn_smul_dom (g : D.form.dom) (c : ℝ) :
    ⇑((c • g : D.form.dom) : Lp ℝ 2 μ) =ᵐ[μ] fun x => c * (g : Lp ℝ 2 μ) x := by
  rw [Submodule.coe_smul]
  filter_upwards [Lp.coeFn_smul c (g : Lp ℝ 2 μ)] with x h1
  rw [h1, Pi.smul_apply, smul_eq_mul]

/--
BH 1991, ex. 3.1 (pp. 14–15) and prop. 3.3.1 (p. 14) for a two-level clamp, under EBM (iii)–(iv).

For real a, b and f ∈ 𝔻, the clamp a ∨ (f ∧ b) is represented in 𝔻 and its energy is at most ℰ(f).
-/
theorem exists_clamp (a b : ℝ) (f : D.form.dom) : ∃ g : D.form.dom,
    (⇑(g : Lp ℝ 2 μ) =ᵐ[μ] fun x => max a (min ((f : Lp ℝ 2 μ) x) b)) ∧
      D.form.E g g ≤ D.form.E f f := by
  rcases le_or_gt b a with hba | hab
  · refine ⟨a • D.one, ?_, ?_⟩
    · filter_upwards [D.coeFn_smul_dom D.one a, D.coeFn_one] with x h1 h2
      rw [h1, h2, mul_one]
      exact (max_eq_left ((min_le_right _ _).trans hba)).symm
    · rw [QuadForm.energy_smul_smul, D.energy_one_left, mul_zero]
      exact D.form.nonneg f
  · set c : ℝ := b - a with hc
    have hc0 : 0 < c := by rw [hc]; linarith
    obtain ⟨U, hU, hUE⟩ := D.markov (c⁻¹ • (f + (-a) • D.one))
    refine ⟨c • U + a • D.one, ?_, ?_⟩
    · filter_upwards [D.coeFn_add_smul_one (c • U) a, D.coeFn_smul_dom U c, hU,
        D.coeFn_smul_dom (f + (-a) • D.one) c⁻¹, D.coeFn_add_smul_one f (-a)] with x h1 h2 h3 h4 h5
      rw [h1, h2, h3, h4, h5, add_comm, clamp_affine_aux hc0.le]
      have e1 : a + c * (c⁻¹ * ((f : Lp ℝ 2 μ) x + -a)) = (f : Lp ℝ 2 μ) x := by
        rw [mul_inv_cancel_left₀ hc0.ne']
        ring
      have e2 : a + c = b := by rw [hc]; ring
      rw [e1, e2]
    · rw [D.energy_add_smul_one, QuadForm.energy_smul_smul]
      rw [QuadForm.energy_smul_smul, D.energy_add_smul_one] at hUE
      have hc2 : c ^ 2 * (c⁻¹ ^ 2 * D.form.E f f) = D.form.E f f := by
        field_simp
      calc c ^ 2 * D.form.E U U ≤ c ^ 2 * (c⁻¹ ^ 2 * D.form.E f f) :=
            mul_le_mul_of_nonneg_left hUE (sq_nonneg c)
        _ = D.form.E f f := hc2

/-- The clamp a ∨ (f ∧ b) in 𝔻. -/
def clamp (a b : ℝ) (f : D.form.dom) : D.form.dom := (D.exists_clamp a b f).choose

/-- The domain clamp is represented almost everywhere by max(a, min(f, b)). -/
theorem coeFn_clamp (a b : ℝ) (f : D.form.dom) :
    ⇑((D.clamp a b f : D.form.dom) : Lp ℝ 2 μ) =ᵐ[μ]
      fun x => max a (min ((f : Lp ℝ 2 μ) x) b) :=
  (D.exists_clamp a b f).choose_spec.1

/-- Clamping a domain element between any two real bounds does not increase its energy. -/
theorem energy_clamp_le (a b : ℝ) (f : D.form.dom) :
    D.form.E (D.clamp a b f) (D.clamp a b f) ≤ D.form.E f f :=
  (D.exists_clamp a b f).choose_spec.2

/--
a consequence of (L₂) (BH 1991, prop. I.5.1.3, p. 29) for two staircase clamps.

If a ≤ b ≤ c ≤ d, the clamps a ∨ (f ∧ b) and c ∨ (f ∧ d) are ℰ-orthogonal.
-/
theorem energy_clamp_clamp_eq_zero {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (f : D.form.dom) : D.form.E (D.clamp a b f) (D.clamp c d f) = 0 := by
  have h := D.strongLocality (D.clamp a b f) (D.clamp c d f + (-c) • D.one) (-b) ?_
  · rwa [D.energy_add_smul_one_right] at h
  · filter_upwards [D.coeFn_clamp a b f, D.coeFn_clamp c d f,
      D.coeFn_add_smul_one (D.clamp c d f) (-c)] with x h1 h2 h3
    rw [h3, h1, h2]
    rcases le_or_gt b ((f : Lp ℝ 2 μ) x) with hx | hx
    · rw [min_eq_right hx, max_eq_right hab]
      ring
    · have hm : min ((f : Lp ℝ 2 μ) x) d = (f : Lp ℝ 2 μ) x := min_eq_left (by linarith)
      rw [hm, max_eq_left (show (f : Lp ℝ 2 μ) x ≤ c by linarith)]
      ring

end LocalDirichletForm
end ErrorCalculus
