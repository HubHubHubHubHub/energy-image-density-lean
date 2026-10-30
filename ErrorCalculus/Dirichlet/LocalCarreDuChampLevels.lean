import ErrorCalculus.Dirichlet.LocalCarreDuChamp

/-!
# level sets of the generic carre du champ; contracts of clause (b)

## Main results
For a local Dirichlet form `D` equipped with data `G : D.CarreDuChamp` (Eriksson-Bique–Murugan
normalization, ℰ(f, f) = ∫ γ(f, f) dμ):

* Cancellation of γ(u, u) on level sets {u = c} (`ae_gamma_self_eq_zero_of_eq`, the consequence
σ^u({c}) = 0 of BH 1991, th. I.5.2.3, used in I.6.1.1), by locality of γ, the energy identity and
semicontinuity of the closed form.
* Exact statements of clause (b) (C¹ ∩ Lip chain rule, BH 1991, th. I.6.1.2) and two steps of its
route (`ClampRule`, `LeibnizRule`), with quantified versions. These contracts are proved by
`clampRule`, `leibnizRule` and `chainRule` for every generic local Dirichlet form.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option maxHeartbeats 800000

namespace ErrorCalculus

/-! ## A. A real-variable tool -/

/-- For ε ∈ ℝ, the function t ↦ (ε − |t|)⁺ is 1-Lipschitz on ℝ. -/
theorem lipschitzWith_bump (ε : ℝ) : LipschitzWith 1 (fun t : ℝ => max (ε - |t|) 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
  have h := abs_max_sub_max_le_abs (ε - |s|) (ε - |t|) 0
  rw [show ε - |s| - (ε - |t|) = -(|s| - |t|) by ring, abs_neg] at h
  exact h.trans (abs_abs_sub_abs_le_abs_sub s t)

namespace LocalDirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

variable (D : LocalDirichletForm μ)

namespace CarreDuChamp
variable {D} (G : D.CarreDuChamp)

/-! ## E. Level sets (BH th. I.5.2.3, σ^u({c}) = 0, in terms of γ) -/

/-- γ(1, v) = 0 for every v ∈ 𝔻 (locality of γ, `gamma_eq_zero_of_mul` with a = −1). -/
theorem gamma_one_left (v : D.form.dom) : G.gamma D.one v = 0 := by
  refine G.gamma_eq_zero_of_mul _ v (-1) ?_
  filter_upwards [D.coeFn_one] with x hx
  rw [hx]
  ring

end CarreDuChamp

/--
For a domain element u, the energy of its symmetric clamp to [−1/(k + 1), 1/(k + 1)] tends to zero.
The proof uses the orthogonal energy decomposition and lower semicontinuity of the closed form.
-/
theorem tendsto_energy_clamp_one_div_add_one (u : D.form.dom) :
    Tendsto (fun k : ℕ => D.form.E (D.clamp (-(1 / ((k : ℝ) + 1))) (1 / ((k : ℝ) + 1)) u)
      (D.clamp (-(1 / ((k : ℝ) + 1))) (1 / ((k : ℝ) + 1)) u)) atTop (𝓝 0) := by
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεd
  have hε : ∀ k, 0 < ε k := fun k => Nat.one_div_pos_of_nat
  set c : ℕ → D.form.dom := fun k => D.clamp (-(ε k)) (ε k) u with hc
  have hdec : ∀ k, D.form.E u u = D.form.E (c k) (c k) + D.form.E (u - c k) (u - c k) :=
    fun k => D.energy_eq_clamp_add (hε k).le u
  have hc0 : Tendsto (fun k => ((c k : D.form.dom) : Lp ℝ 2 μ)) atTop (𝓝 0) := by
    apply lp_two_tendsto_zero_of_dominated _ (Lp.const 2 μ (1 : ℝ))
    · intro k
      filter_upwards [D.coeFn_clamp (-(ε k)) (ε k) u, Lp.coeFn_const 2 μ (1 : ℝ)] with x h1 h2
      rw [h1, h2, Function.const_apply, abs_one]
      have hk1 : ε k ≤ 1 := by
        simp only [hεd]
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      exact (abs_le.2 ⟨le_max_left _ _, max_le (by linarith [hε k]) (min_le_right _ _)⟩).trans hk1
    · have hall : ∀ᵐ x ∂μ, ∀ k : ℕ, ((c k : D.form.dom) : Lp ℝ 2 μ) x =
          max (-(ε k)) (min ((u : Lp ℝ 2 μ) x) (ε k)) := by
        rw [ae_all_iff]
        intro k
        exact D.coeFn_clamp _ _ u
      filter_upwards [hall] with x hx
      simp only [hx]
      have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      apply squeeze_zero_norm (fun k => ?_) hlim
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨le_max_left _ _, max_le (by linarith [hε k]) (min_le_right _ _)⟩
  have hL : Tendsto (fun k => ((u - c k : D.form.dom) : Lp ℝ 2 μ)) atTop
      (𝓝 (u : Lp ℝ 2 μ)) := by
    have h := (tendsto_const_nhds (x := (u : Lp ℝ 2 μ))).sub hc0
    rw [sub_zero] at h
    exact h.congr fun k => by rw [Submodule.coe_sub]
  have hle : ∀ k, D.form.E (u - c k) (u - c k) ≤ D.form.E u u := fun k => by
    have := hdec k
    linarith [D.form.nonneg (c k)]
  have hlim := D.closed.energy_le_liminf (x := fun k => u - c k) hL
    ⟨D.form.E u u, (Eventually.of_forall hle).frequently⟩ u.2
  simp only [Subtype.coe_eta] at hlim
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun k => D.form.E (u - c k) (u - c k)) :=
    isBoundedUnder_of ⟨0, fun k => D.form.nonneg _⟩
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun k => lt_of_lt_of_le ha (D.form.nonneg _),
    fun a ha => ?_⟩
  have hev := eventually_lt_of_lt_liminf (show D.form.E u u - a < liminf
    (fun k => D.form.E (u - c k) (u - c k)) atTop by linarith) hbdd
  filter_upwards [hev] with k hk
  have := hdec k
  change D.form.E (c k) (c k) < a
  linarith

namespace CarreDuChamp
variable {D} (G : D.CarreDuChamp)

/--
For u ∈ 𝔻 and ε > 0, the integral of γ(u, u) on {u = 0} is bounded above by the energy of the clamp
(−ε) ∨ (u ∧ ε) (local cancellation `mul_gamma_eq_zero` with bounded multiplier h = (ε − |u|)⁺, then
the energy identity).
-/
theorem integral_indicator_gamma_le (u : D.form.dom) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, ((u : Lp ℝ 2 μ) ⁻¹' {0}).indicator (fun x => G.gamma u u x) x ∂μ ≤
      D.form.E (D.clamp (-ε) ε u) (D.clamp (-ε) ε u) := by
  set S : Set Ω := (u : Lp ℝ 2 μ) ⁻¹' {0} with hS
  have hSm : MeasurableSet S :=
    (Lp.stronglyMeasurable (u : Lp ℝ 2 μ)).measurable (measurableSet_singleton 0)
  set c : D.form.dom := D.clamp (-ε) ε u with hc
  have hcx : ⇑((c : D.form.dom) : Lp ℝ 2 μ) =ᵐ[μ]
      fun x => max (-ε) (min ((u : Lp ℝ 2 μ) x) ε) :=
    D.coeFn_clamp _ _ u
  set w : D.form.dom := u - c with hw
  obtain ⟨bw, hbw⟩ := exists_lp_comp (μ := μ) (lipschitzWith_bump ε) (u : Lp ℝ 2 μ)
  obtain ⟨bm, -⟩ := D.exists_mem_of_lipschitzWith (lipschitzWith_bump ε) u bw hbw
  set b : D.form.dom := ⟨bw, bm⟩ with hb
  have hbb : AEBounded (μ := μ) ((b : Lp ℝ 2 μ) : Ω → ℝ) := by
    refine ⟨ε, ?_⟩
    filter_upwards [hbw] with x hx
    change ‖bw x‖ ≤ ε
    rw [hx, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [abs_nonneg ((u : Lp ℝ 2 μ) x)]) hε.le
  have hbw0 : ∀ᵐ x ∂μ, (b : Lp ℝ 2 μ) x * (w : Lp ℝ 2 μ) x = 0 := by
    filter_upwards [hbw, hcx, Lp.coeFn_sub (u : Lp ℝ 2 μ) (c : Lp ℝ 2 μ)] with x h1 h2 h3
    change bw x * ((u - c : D.form.dom) : Lp ℝ 2 μ) x = 0
    rw [Submodule.coe_sub, h3, Pi.sub_apply, h1, h2]
    rcases le_or_gt |(u : Lp ℝ 2 μ) x| ε with h | h
    · rw [min_eq_left (abs_le.1 h).2, max_eq_right (abs_le.1 h).1, sub_self, mul_zero]
    · rw [max_eq_right (by linarith), zero_mul]
  have hA := G.mul_gamma_eq_zero c w b hbb hbw0
  have hB := G.mul_gamma_eq_zero w w b hbb hbw0
  have hsplit : G.gamma u u = G.gamma c c + G.gamma c w + G.gamma w c + G.gamma w w := by
    have hu : u = c + w := by rw [hw, add_sub_cancel]
    rw [hu]
    simp only [map_add, LinearMap.add_apply]
    abel
  have hsym : G.gamma w c = G.gamma c w := G.symm w c
  have hind : S.indicator (fun x => G.gamma u u x) =ᵐ[μ] S.indicator (fun x => G.gamma c c x) := by
    rw [hsplit, hsym]
    filter_upwards [hA, hB, hbw, Lp.coeFn_add (G.gamma c c + G.gamma c w + G.gamma c w)
      (G.gamma w w), Lp.coeFn_add (G.gamma c c + G.gamma c w) (G.gamma c w),
      Lp.coeFn_add (G.gamma c c) (G.gamma c w)] with x a1 a2 a3 a4 a5 a6
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, a4, Pi.add_apply, a5, Pi.add_apply,
        a6, Pi.add_apply]
      have hux : (u : Lp ℝ 2 μ) x = 0 := hx
      have hbx : (b : Lp ℝ 2 μ) x = ε := by
        change bw x = ε
        rw [a3, hux, abs_zero, sub_zero, max_eq_left hε.le]
      rw [hbx] at a1 a2
      have z1 : G.gamma c w x = 0 := (mul_eq_zero.1 a1).resolve_left hε.ne'
      have z2 : G.gamma w w x = 0 := (mul_eq_zero.1 a2).resolve_left hε.ne'
      rw [z1, z2]
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  rw [integral_congr_ae hind, G.energy_eq_integral c]
  apply integral_mono_ae ((L1.integrable_coeFn _).indicator hSm) (L1.integrable_coeFn _)
  filter_upwards [G.nonneg c] with x hx
  by_cases h : x ∈ S
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]
    exact hx

/-- For u ∈ 𝔻: for almost every x, u(x) = 0 ⇒ γ(u, u)(x) = 0. -/
theorem ae_gamma_self_eq_zero_of_eq_zero (u : D.form.dom) :
    ∀ᵐ x ∂μ, (u : Lp ℝ 2 μ) x = 0 → G.gamma u u x = 0 := by
  set S : Set Ω := (u : Lp ℝ 2 μ) ⁻¹' {0} with hS
  have hSm : MeasurableSet S :=
    (Lp.stronglyMeasurable (u : Lp ℝ 2 μ)).measurable (measurableSet_singleton 0)
  have hint : Integrable (S.indicator fun x => G.gamma u u x) μ :=
    (L1.integrable_coeFn _).indicator hSm
  have hnn : 0 ≤ᵐ[μ] S.indicator fun x => G.gamma u u x := by
    filter_upwards [G.nonneg u] with x hx
    by_cases h : x ∈ S
    · rw [Set.indicator_of_mem h]
      exact hx
    · rw [Set.indicator_of_notMem h]
      exact le_rfl
  have hle : ∫ x, S.indicator (fun x => G.gamma u u x) x ∂μ ≤ 0 :=
    ge_of_tendsto' (D.tendsto_energy_clamp_one_div_add_one u) fun k : ℕ =>
      G.integral_indicator_gamma_le u (ε := 1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  have h0 : ∫ x, S.indicator (fun x => G.gamma u u x) x ∂μ = 0 :=
    le_antisymm hle (integral_nonneg_of_ae hnn)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0
  filter_upwards [hz] with x hx hxS
  have hm : x ∈ S := hxS
  rw [Set.indicator_of_mem hm] at hx
  exact hx

/--
BH 1991, th. I.5.2.3 (p. 32), the consequence σ^u({c}) = 0 used in the proof of prop. I.6.1.1 (p.
36), written in terms of γ: for u ∈ 𝔻 and fixed c ∈ ℝ, for almost every x, u(x) = c ⇒ γ(u, u)(x) = 0
(the null set depends on c; no set common to all c is asserted). Proof by locality and clamps alone,
without Beurling–Deny representation.
-/
theorem ae_gamma_self_eq_zero_of_eq (u : D.form.dom) (c : ℝ) :
    ∀ᵐ x ∂μ, (u : Lp ℝ 2 μ) x = c → G.gamma u u x = 0 := by
  have h1 : G.gamma D.one u = 0 := G.gamma_one_left u
  have h2 : G.gamma u D.one = 0 := by rw [G.symm]; exact h1
  have h3 : G.gamma D.one D.one = 0 := G.gamma_one_left D.one
  have hg : G.gamma (u - c • D.one) (u - c • D.one) = G.gamma u u := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, h1, h2, h3,
      smul_zero, sub_zero]
  have hux : ⇑((u - c • D.one : D.form.dom) : Lp ℝ 2 μ) =ᵐ[μ] fun x => (u : Lp ℝ 2 μ) x - c := by
    filter_upwards [Lp.coeFn_sub (u : Lp ℝ 2 μ) (c • ((D.one : D.form.dom) : Lp ℝ 2 μ)),
      Lp.coeFn_smul c ((D.one : D.form.dom) : Lp ℝ 2 μ), D.coeFn_one] with x a1 a2 a3
    rw [Submodule.coe_sub, Submodule.coe_smul, a1, Pi.sub_apply, a2, Pi.smul_apply, a3,
      smul_eq_mul, mul_one]
  filter_upwards [G.ae_gamma_self_eq_zero_of_eq_zero (u - c • D.one), hux] with x a b hx
  rw [← hg]
  exact a (by rw [b, hx, sub_self])

/-! ## F. Contracts of clause (b) (exact statements) -/

/--
**Contract proved** by `clampRule` for every generic local Dirichlet form. to clause (b) (BH 1991,
th. I.6.1.2), the generic version of `GammaClampStatement`: for all u, v, w ∈ 𝔻 and a, b ∈ ℝ
(including a ≥ b), if w = a ∨ (u ∧ b) a.e., then γ(w, v) = 1_{a < u < b} γ(u, v) a.e.
-/
def ClampRule : Prop :=
  ∀ (u v w : D.form.dom) (a b : ℝ),
    (⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun x => max a (min ((u : Lp ℝ 2 μ) x) b)) →
      ⇑(G.gamma w v) =ᵐ[μ] fun x => (Set.Ioo a b).indicator 1 ((u : Lp ℝ 2 μ) x) * G.gamma u v x

/--
**Contract proved** by `leibnizRule` for every generic local Dirichlet form. the generic version of
`GammaLeibnizStatement`: for essentially bounded f, g ∈ 𝔻, p ∈ 𝔻 equal a.e. to f g and v ∈ 𝔻, γ(p,
v) = f γ(g, v) + g γ(f, v) a.e.
-/
def LeibnizRule : Prop :=
  ∀ f g p v : D.form.dom, AEBounded (μ := μ) ((f : Lp ℝ 2 μ) : Ω → ℝ) →
    AEBounded (μ := μ) ((g : Lp ℝ 2 μ) : Ω → ℝ) →
    (⇑(p : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (g : Lp ℝ 2 μ) x) →
    ⇑(G.gamma p v) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * G.gamma g v x + (g : Lp ℝ 2 μ) x * G.gamma f v x

/--
**Contract proved** by `chainRule` for every generic local Dirichlet form. Clause (b) of
`BHFunctionalCalculus` (BH 1991, th. I.6.1.2 and cor. I.6.1.3, pp. 36–37), generic version: for m >
0, u ∈ 𝔻ᵐ, F : ℝᵐ → ℝ of class C¹ and L-Lipschitz, every class w ∈ L²(μ) equal a.e. to F ∘ u lies in
𝔻 and, for every v ∈ 𝔻, γ(w, v) = Σᵢ ∂ᵢF(u) γ(uᵢ, v) a.e.
-/
def ChainRule : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (u : Fin m → D.form.dom) (F : (Fin m → ℝ) → ℝ) (L : ℝ≥0),
    ContDiff ℝ 1 F → LipschitzWith L F →
    ∀ w : Lp ℝ 2 μ, (⇑w =ᵐ[μ] fun x => F (fun i => (u i : Lp ℝ 2 μ) x)) →
      ∃ hw : w ∈ D.form.dom, ∀ v : D.form.dom, ⇑(G.gamma ⟨w, hw⟩ v) =ᵐ[μ] fun x =>
        ∑ i, fderiv ℝ F (fun j => (u j : Lp ℝ 2 μ) x) (Pi.single i 1) * G.gamma (u i) v x

end CarreDuChamp

/--
**Contract proved** by `clampRuleStatement`, the quantified version of `clampRule`:
`CarreDuChamp.ClampRule` for every probability space `(Ω : Type)`, every generic local Dirichlet
form and every carre du champ datum.
-/
def ClampRuleStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : LocalDirichletForm μ) (G : D.CarreDuChamp), G.ClampRule

/--
**Contract proved** by `leibnizRuleStatement`, the quantified version of `leibnizRule`:
`CarreDuChamp.LeibnizRule` for every probability space `(Ω : Type)`, every generic local Dirichlet
form and every carre du champ datum.
-/
def LeibnizRuleStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : LocalDirichletForm μ) (G : D.CarreDuChamp), G.LeibnizRule

/--
**Contract proved** by `chainRuleStatement`, the quantified version of `chainRule`:
`CarreDuChamp.ChainRule` for every probability space `(Ω : Type)`, every generic local Dirichlet
form and every carre du champ datum.
-/
def ChainRuleStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : LocalDirichletForm μ) (G : D.CarreDuChamp), G.ChainRule

end LocalDirichletForm
end ErrorCalculus
