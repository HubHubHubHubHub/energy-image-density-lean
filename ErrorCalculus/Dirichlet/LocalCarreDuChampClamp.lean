import ErrorCalculus.Dirichlet.LocalCarreDuChampLevels

/-!
# `ClampRule` proved for the generic carre du champ

## Main results
For a local Dirichlet form `D : LocalDirichletForm μ` equipped with a datum `G : D.CarreDuChamp`
(Eriksson-Bique–Murugan normalization, ℰ(f, f) = ∫ γ(f, f) dμ):

* Weak pointwise Cauchy–Schwarz: γ(f, f) = 0 ⇒ γ(f, g) = 0 a.e.
(`ae_gamma_eq_zero_of_gamma_self_eq_zero`).
* Cancellation of γ(u, v) on every level set {u = c} (`ae_gamma_eq_zero_of_eq`, a consequence of BH
1991, th. I.5.2.3, p. 32).
* **`clampRule : G.ClampRule`** and **`clampRuleStatement : ClampRuleStatement`**: the contract
`ClampRule` (γ(a ∨ (u ∧ b), v) = 1_{]a, b[}(u) γ(u, v) a.e.; on the route to BH 1991, th. I.6.1.2,
p. 36) is proved.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option maxHeartbeats 800000

namespace ErrorCalculus

/-! ## A. Real-variable tools -/

/--
If A = 0 and 0 ≤ A + 2tB + t²C for t = ±1/(n + 1), n ∈ ℕ, then B = 0 (weak Cauchy–Schwarz, scalar
version).
-/
theorem eq_zero_of_forall_quadratic_nonneg {A B C : ℝ} (hA : A = 0)
    (h : ∀ n : ℕ, 0 ≤ A + 2 * (1 / ((n : ℝ) + 1)) * B + (1 / ((n : ℝ) + 1)) ^ 2 * C ∧
      0 ≤ A + 2 * (-(1 / ((n : ℝ) + 1))) * B + (-(1 / ((n : ℝ) + 1))) ^ 2 * C) : B = 0 := by
  have hb : ∀ n : ℕ, |B| ≤ C / 2 * (1 / ((n : ℝ) + 1)) := by
    intro n
    obtain ⟨h1, h2⟩ := h n
    set t : ℝ := 1 / ((n : ℝ) + 1) with ht
    have htp : 0 < t := Nat.one_div_pos_of_nat
    rw [hA] at h1 h2
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  have hlim : Tendsto (fun n : ℕ => C / 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (C / 2)
    rwa [mul_zero] at h0
  exact abs_nonpos_iff.mp (ge_of_tendsto' hlim hb)

/-- The map t ↦ min (t − a) (b − t) is 1-Lipschitz. -/
theorem lipschitzWith_min_sub_sub (a b : ℝ) :
    LipschitzWith 1 (fun t : ℝ => min (t - a) (b - t)) := by
  have h₁ : LipschitzWith 1 (fun t : ℝ => t - a) :=
    (IsometryEquiv.subRight a).isometry.lipschitz
  have h₂ : LipschitzWith 1 (fun t : ℝ => b - t) :=
    (IsometryEquiv.subLeft b).isometry.lipschitz
  simpa only [max_self] using h₁.min h₂

/-- The map t ↦ t − b is 1-Lipschitz. -/
theorem lipschitzWith_sub_const_one (b : ℝ) : LipschitzWith 1 (fun t : ℝ => t - b) := by
  exact (IsometryEquiv.subRight b).isometry.lipschitz

/-- The map t ↦ a − t is 1-Lipschitz. -/
theorem lipschitzWith_const_sub_one (a : ℝ) : LipschitzWith 1 (fun t : ℝ => a - t) := by
  exact (IsometryEquiv.subLeft a).isometry.lipschitz

namespace LocalDirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (D : LocalDirichletForm μ)

/-! ## C. Bounded cutoffs -/

/--
For 1-Lipschitz φ and u ∈ 𝔻, the cutoff x ↦ min (max (φ(u(x))) 0) 1 is represented in 𝔻 and is
essentially bounded.
-/
theorem exists_aeBounded_cutoff {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) (u : D.form.dom) :
    ∃ h : D.form.dom,
      (⇑(h : Lp ℝ 2 μ) =ᵐ[μ] fun x => min (max (φ ((u : Lp ℝ 2 μ) x)) 0) 1) ∧
        AEBounded (μ := μ) ((h : Lp ℝ 2 μ) : Ω → ℝ) := by
  have hL : LipschitzWith 1 (fun t => min (max (φ t) 0) 1) := (hφ.max_const 0).min_const 1
  obtain ⟨w, hw⟩ := exists_lp_comp (μ := μ) hL (u : Lp ℝ 2 μ)
  obtain ⟨hm, -⟩ := D.exists_mem_of_lipschitzWith hL u w hw
  refine ⟨⟨w, hm⟩, hw, 1, ?_⟩
  filter_upwards [hw] with x hx
  rw [hx, Real.norm_eq_abs, abs_le]
  constructor
  · have := le_min (le_max_right (φ ((u : Lp ℝ 2 μ) x)) 0) zero_le_one
    linarith
  · exact min_le_right _ _

namespace CarreDuChamp
variable {D} (G : D.CarreDuChamp)

/-! ## D. Weak Cauchy–Schwarz, constants, level sets -/

/-- γ(f + t g, f + t g) = γ(f, f) + 2t γ(f, g) + t² γ(g, g) in L¹. -/
theorem gamma_add_smul_self (f g : D.form.dom) (t : ℝ) :
    G.gamma (f + t • g) (f + t • g) =
      G.gamma f f + (2 * t) • G.gamma f g + (t ^ 2) • G.gamma g g := by
  exact (ErrorData.gamma_polynomial ⟨D.form.dom, G.gamma, G.symm, G.nonneg⟩ f g t)

/--
weak pointwise Cauchy–Schwarz (the form used for levels in BH 1991, th. I.5.2.3, p. 32): for f, g ∈
𝔻, for almost every x, γ(f, f)(x) = 0 ⇒ γ(f, g)(x) = 0, by transporting
`ErrorData.gamma_cauchy_schwarz` to the data ⟨D.form.dom, G.gamma, G.symm, G.nonneg⟩.
-/
theorem ae_gamma_eq_zero_of_gamma_self_eq_zero (f g : D.form.dom) :
    ∀ᵐ x ∂μ, G.gamma f f x = 0 → G.gamma f g x = 0 := by
  filter_upwards [ErrorData.gamma_cauchy_schwarz
    ⟨D.form.dom, G.gamma, G.symm, G.nonneg⟩ f g] with x h h0
  change G.gamma f g x ^ 2 ≤ G.gamma f f x * G.gamma g g x at h
  rw [h0, zero_mul] at h
  nlinarith [sq_nonneg (G.gamma f g x)]

/-- γ(v, 1) = 0. -/
theorem gamma_one_right (v : D.form.dom) : G.gamma v D.one = 0 := by
  rw [G.symm]
  exact G.gamma_one_left v

/-- γ(f + c·1, v) = γ(f, v). -/
theorem gamma_add_smul_one (f v : D.form.dom) (c : ℝ) :
    G.gamma (f + c • D.one) v = G.gamma f v := by
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, G.gamma_one_left, smul_zero,
    add_zero]

/--
level sets (a consequence of BH 1991, th. I.5.2.3, p. 32, and weak Cauchy–Schwarz): for u, v ∈ 𝔻 and
fixed c ∈ ℝ, for almost every x, u(x) = c ⇒ γ(u, v)(x) = 0 (the null set depends on c).
-/
theorem ae_gamma_eq_zero_of_eq (u v : D.form.dom) (c : ℝ) :
    ∀ᵐ x ∂μ, (u : Lp ℝ 2 μ) x = c → G.gamma u v x = 0 := by
  filter_upwards [G.ae_gamma_self_eq_zero_of_eq u c,
    G.ae_gamma_eq_zero_of_gamma_self_eq_zero u v] with x h1 h2 hx
  exact h2 (h1 hx)

/-! ## The clamp rule -/

/--
For domain elements u, v, w and any real a, b, if w = a ∨ (u ∧ b) almost everywhere, then γ(w, v) =
1_{]a,b[}(u) γ(u, v) almost everywhere, including a ≥ b. This proves `ClampRule`, used in the chain
rule of BH 1991, th. I.6.1.2, p. 36.
-/
theorem clampRule : G.ClampRule := by
  intro u v w a b hw
  rcases le_or_gt b a with hba | hab
  · have hw1 : w = a • D.one := by
      apply QuadForm.dom_ext_ae
      filter_upwards [hw, D.coeFn_smul_dom D.one a, D.coeFn_one] with x h1 h2 h3
      rw [h1, h2, h3, mul_one]
      exact max_eq_left ((min_le_right _ _).trans hba)
    rw [hw1, map_smul, LinearMap.smul_apply, G.gamma_one_left, smul_zero]
    filter_upwards [Lp.coeFn_zero ℝ 1 μ] with x hx
    rw [hx, Set.Ioo_eq_empty (not_lt.2 hba), Set.indicator_empty]
    simp
  · set c : D.form.dom := D.clamp a b u with hc
    have hwc : w = c := QuadForm.dom_ext_ae (hw.trans (D.coeFn_clamp a b u).symm)
    have hcx : ⇑(c : Lp ℝ 2 μ) =ᵐ[μ] fun x => max a (min ((u : Lp ℝ 2 μ) x) b) :=
      D.coeFn_clamp a b u
    -- Inside ]a, b[: cutoff h₁ = min ((u − a)⁺ ∧ (b − u)⁺) 1, annihilating u − c.
    have hI : ∀ᵐ x ∂μ, a < (u : Lp ℝ 2 μ) x → (u : Lp ℝ 2 μ) x < b →
        G.gamma c v x = G.gamma u v x := by
      obtain ⟨h₁, hh₁, hb₁⟩ := D.exists_aeBounded_cutoff (lipschitzWith_min_sub_sub a b) u
      have hz : ∀ᵐ x ∂μ, (h₁ : Lp ℝ 2 μ) x * ((u - c : D.form.dom) : Lp ℝ 2 μ) x = 0 := by
        filter_upwards [hh₁, hcx, Lp.coeFn_sub (u : Lp ℝ 2 μ) (c : Lp ℝ 2 μ)] with x e1 e2 e3
        rw [Submodule.coe_sub, e3, Pi.sub_apply, e1, e2]
        by_cases h1 : a < (u : Lp ℝ 2 μ) x ∧ (u : Lp ℝ 2 μ) x < b
        · rw [min_eq_left h1.2.le, max_eq_right h1.1.le, sub_self, mul_zero]
        · have hneg : min ((u : Lp ℝ 2 μ) x - a) (b - (u : Lp ℝ 2 μ) x) ≤ 0 := by
            rcases not_and_or.1 h1 with h | h
            · exact (min_le_left _ _).trans (by linarith [not_lt.1 h])
            · exact (min_le_right _ _).trans (by linarith [not_lt.1 h])
          rw [max_eq_right hneg, min_eq_left zero_le_one, zero_mul]
      have hm := G.mul_gamma_eq_zero v (u - c) h₁ hb₁ hz
      have hsplit : G.gamma u v = G.gamma c v + G.gamma (u - c) v := by
        rw [← LinearMap.add_apply, ← map_add, add_sub_cancel]
      filter_upwards [hm, hh₁, Lp.coeFn_add (G.gamma c v) (G.gamma (u - c) v)]
        with x e1 e2 e3 ha hb'
      have hpos : 0 < (h₁ : Lp ℝ 2 μ) x := by
        rw [e2]
        exact lt_min (lt_max_of_lt_left (lt_min (by linarith) (by linarith))) one_pos
      have hz' : G.gamma v (u - c) x = 0 := (mul_eq_zero.1 e1).resolve_left hpos.ne'
      rw [hsplit, e3, Pi.add_apply, G.symm (u - c) v, hz', add_zero]
    -- Above b: cutoff h₂ = min ((u − b)⁺) 1, annihilating c − b.
    have hR : ∀ᵐ x ∂μ, b < (u : Lp ℝ 2 μ) x → G.gamma c v x = 0 := by
      obtain ⟨h₂, hh₂, hb₂⟩ := D.exists_aeBounded_cutoff (lipschitzWith_sub_const_one b) u
      have hz : ∀ᵐ x ∂μ,
          (h₂ : Lp ℝ 2 μ) x * ((c + (-b) • D.one : D.form.dom) : Lp ℝ 2 μ) x = 0 := by
        filter_upwards [hh₂, D.coeFn_add_smul_one c (-b), hcx] with x e1 e2 e3
        rw [e1, e2, e3]
        rcases le_or_gt ((u : Lp ℝ 2 μ) x) b with h | h
        · rw [max_eq_right (by linarith : (u : Lp ℝ 2 μ) x - b ≤ 0), min_eq_left zero_le_one,
            zero_mul]
        · rw [min_eq_right h.le, max_eq_right hab.le]
          ring
      have hm := G.mul_gamma_eq_zero v _ h₂ hb₂ hz
      filter_upwards [hm, hh₂] with x e1 e2 hx
      have hpos : 0 < (h₂ : Lp ℝ 2 μ) x := by
        rw [e2]
        exact lt_min (lt_max_of_lt_left (by linarith)) one_pos
      have hz' := (mul_eq_zero.1 e1).resolve_left hpos.ne'
      rw [← G.gamma_add_smul_one c v (-b), G.symm]
      exact hz'
    -- Below a: cutoff h₃ = min ((a − u)⁺) 1, annihilating c − a.
    have hL : ∀ᵐ x ∂μ, (u : Lp ℝ 2 μ) x < a → G.gamma c v x = 0 := by
      obtain ⟨h₃, hh₃, hb₃⟩ := D.exists_aeBounded_cutoff (lipschitzWith_const_sub_one a) u
      have hz : ∀ᵐ x ∂μ,
          (h₃ : Lp ℝ 2 μ) x * ((c + (-a) • D.one : D.form.dom) : Lp ℝ 2 μ) x = 0 := by
        filter_upwards [hh₃, D.coeFn_add_smul_one c (-a), hcx] with x e1 e2 e3
        rw [e1, e2, e3]
        rcases le_or_gt a ((u : Lp ℝ 2 μ) x) with h | h
        · rw [max_eq_right (by linarith : a - (u : Lp ℝ 2 μ) x ≤ 0), min_eq_left zero_le_one,
            zero_mul]
        · rw [min_eq_left (show (u : Lp ℝ 2 μ) x ≤ b by linarith), max_eq_left h.le]
          ring
      have hm := G.mul_gamma_eq_zero v _ h₃ hb₃ hz
      filter_upwards [hm, hh₃] with x e1 e2 hx
      have hpos : 0 < (h₃ : Lp ℝ 2 μ) x := by
        rw [e2]
        exact lt_min (lt_max_of_lt_left (by linarith)) one_pos
      have hz' := (mul_eq_zero.1 e1).resolve_left hpos.ne'
      rw [← G.gamma_add_smul_one c v (-a), G.symm]
      exact hz'
    rw [hwc]
    filter_upwards [hI, hR, hL, G.ae_gamma_eq_zero_of_eq c v a, G.ae_gamma_eq_zero_of_eq c v b, hcx]
      with x e1 e2 e3 e4 e5 e6
    rcases lt_trichotomy ((u : Lp ℝ 2 μ) x) a with h | h | h
    · rw [Set.indicator_of_notMem (fun hm => absurd hm.1 (not_lt.2 h.le)), zero_mul]
      exact e3 h
    · rw [Set.indicator_of_notMem (fun hm => absurd hm.1 (by rw [h]; exact lt_irrefl a)),
        zero_mul]
      exact e4 (by rw [e6, h, min_eq_left hab.le, max_self])
    · rcases lt_trichotomy ((u : Lp ℝ 2 μ) x) b with h' | h' | h'
      · rw [Set.indicator_of_mem (show (u : Lp ℝ 2 μ) x ∈ Set.Ioo a b from ⟨h, h'⟩),
          Pi.one_apply, one_mul]
        exact e1 h h'
      · rw [Set.indicator_of_notMem (fun hm => absurd hm.2 (by rw [h']; exact lt_irrefl b)),
          zero_mul]
        exact e5 (by rw [e6, h', min_self, max_eq_right hab.le])
      · rw [Set.indicator_of_notMem (fun hm => absurd hm.2 (not_lt.2 h'.le)), zero_mul]
        exact e2 h'

end CarreDuChamp

/-! ## I. Quantified version (contract `ClampRuleStatement`) -/

/--
The quantified contract `ClampRuleStatement` is proved: `CarreDuChamp.ClampRule` holds for every
probability space `(Ω : Type)`, every local Dirichlet form and every carre du champ datum.
-/
theorem clampRuleStatement : ClampRuleStatement := by
  intro Ω _ μ _ D G
  exact G.clampRule

end LocalDirichletForm
end ErrorCalculus
