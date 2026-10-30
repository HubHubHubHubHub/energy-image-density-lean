import DprBridge.BH1991GammaLocality
import DprBridge.BH1991NormalContractions
import DprBridge.BH1991Printed

/-!
# Level cancellation and centered truncations

## Main results
Shifted annihilation, Gamma cancellation on levels and the centered clamp rule hold under BH
locality and a carré du champ. The original arbitrary measure and domain are retained, with Γ = 2γ
and no required constant domain element. Scalar chain and Leibniz rules are developed in
`BH1991ChainRules`, and multivariate chains in `BH1991ChainCurrents`.

References: Bouleau–Hirsch (1991), ch. I, I.5.1.3, I.5.2.3 and I.6.1.1–3; ch. V, p. 185; Notes, p.
302; Eriksson-Bique–Murugan, Section 4.2. The local heartbeat budget supports the form-space
transports in shifted annihilation.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ErrorCalculus
open scoped NNReal ENNReal
universe u

namespace DprBridge.BH1991.DirichletForm
variable {X : Type u} [MeasurableSpace X] {m : Measure X} (D : DirichletForm m)

/--
Conditional on BH locality, a bounded domain multiplier h annihilates Gamma(v,w) almost
everywhere for bounded domain arguments v,w whenever h(w+a) vanishes almost everywhere. The proof
uses the
characteristic identity and BH 1991, ch. I, I.5.1.3; EID context: ch. V, p. 185, Notes p. 302, and
EBM section 4.2.
-/
theorem mul_gamma_eq_zero_of_shift_bounded (hL : D.Local) (G : D.CarreDuChamp)
    (v w h : D.toCapacity.Space) (a : ℝ)
    (hv : v ∈ D.toCapacity.bddSpace) (hw : w ∈ D.toCapacity.bddSpace)
    (hh : h ∈ D.toCapacity.bddSpace)
    (hhw : ∀ᵐ x ∂m, D.toCapacity.toLp h x * (D.toCapacity.toLp w x + a) = 0) :
    ∀ᵐ x ∂m, D.toCapacity.toLp h x * G.Γ v w x = 0 := by
  have hm := D.bounded_memLp_top h hh
  let b := boundedMul (D.toCapacity.toLp h) hm (G.Γ v w)
  have hb : b = 0 := by
    apply D.gamma_eq_zero_of_tests
    intro k hk
    let z := D.toCapacity.mulS k h
    have hz : z ∈ D.toCapacity.bddSpace := D.toCapacity.mulS_mem hk hh
    have hzrep := D.toCapacity.coeFn_toLp_mulS hk hh
    have hp := D.toCapacity.coeFn_toLp_mulS hv hz
    have hq := D.toCapacity.coeFn_toLp_mulS hw hz
    have hr := D.toCapacity.coeFn_toLp_mulS hv hw
    have h1 := D.carreDuChamp_toCapacity G v hv w hw z hz
    have e1 : D.toCapacity.ener (D.toCapacity.mulS v z) w = 0 := by
      rw [D.toCapacity.ener_symm]
      apply D.local_toCapacity hL _ _ a
      filter_upwards [hp, hzrep, hhw] with x p q r
      change D.toCapacity.toLp z x = _ at q
      rw [p, q]
      linear_combination D.toCapacity.toLp v x * D.toCapacity.toLp k x * r
    have eqz : D.toCapacity.mulS w z = (-a) • z := by
      apply D.toCapacity.eq_of_ae
      rw [map_smul]
      filter_upwards [hq, hzrep, hhw, Lp.coeFn_smul (-a) (D.toCapacity.toLp z)]
        with x p q r s
      change D.toCapacity.toLp z x = _ at q
      rw [p, s, Pi.smul_apply, smul_eq_mul, q]
      linear_combination D.toCapacity.toLp k x * r
    have e3 : D.toCapacity.ener z (D.toCapacity.mulS v w + a • v) = 0 := by
      apply D.local_toCapacity hL _ _ 0
      simp only [map_add, map_smul]
      filter_upwards [hr, hzrep, hhw,
        Lp.coeFn_add (D.toCapacity.toLp (D.toCapacity.mulS v w)) (a • D.toCapacity.toLp v),
        Lp.coeFn_smul a (D.toCapacity.toLp v)] with x p q r s t
      change D.toCapacity.toLp z x = _ at q
      rw [add_zero, s, Pi.add_apply, t, Pi.smul_apply, smul_eq_mul, p, q]
      linear_combination D.toCapacity.toLp v x * D.toCapacity.toLp k x * r
    rw [e1, eqz] at h1
    simp only [map_add, map_smul, smul_apply, smul_eq_mul] at h1 e3
    have he : (∫ x, D.toCapacity.toLp k x * b x ∂m) =
        ∫ x, D.toCapacity.toLp z x * G.Γ v w x ∂m := by
      apply integral_congr_ae
      filter_upwards [coeFn_boundedMul (D.toCapacity.toLp h) hm (G.Γ v w), hzrep]
        with x p q
      change b x = _ at p
      change D.toCapacity.toLp z x = _ at q
      rw [p, q]
      ring
    rw [he]
    linarith
  filter_upwards [coeFn_boundedMul (D.toCapacity.toLp h) hm (G.Γ v w),
    Lp.coeFn_zero ℝ 1 m] with x p q
  change b x = _ at p
  change (0 : Lp ℝ 1 m) x = 0 at q
  rw [← p, hb, q]

/--
Symmetric truncation preserves a shifted zero product almost everywhere when the truncation level
is at least the absolute shift.
-/
theorem mul_truncS_add_eq_zero (h w : D.toCapacity.Space) (a : ℝ) (n : ℕ)
    (hn : |a| ≤ n)
    (hhw : ∀ᵐ x ∂m, D.toCapacity.toLp h x * (D.toCapacity.toLp w x + a) = 0) :
    ∀ᵐ x ∂m, D.toCapacity.toLp h x *
      (D.toCapacity.toLp (D.toCapacity.truncS n w) x + a) = 0 := by
  have hw := D.toCapacity.coe_contractLp
    (Capacity.DirichletForm.lipschitzWith_trunc n)
    (Capacity.DirichletForm.trunc_zero n) w
  simp only [Capacity.DirichletForm.truncS, Capacity.DirichletForm.toLp_contract]
  filter_upwards [hhw, hw] with x hx hwx
  rw [hwx]
  rcases mul_eq_zero.mp hx with hh0 | hw0
  · rw [hh0, zero_mul]
  · have he : D.toCapacity.toLp w x = -a := by linarith
    obtain ⟨ha1, ha2⟩ := abs_le.mp hn
    rw [he, min_eq_left (by linarith), max_eq_left (by linarith)]
    ring

set_option maxHeartbeats 1000000 in
/--
Conditional on BH locality, a bounded domain multiplier h annihilates Gamma(v,w) almost
everywhere for arbitrary domain arguments v,w whenever h(w+a) vanishes almost everywhere.
Consequence of BH 1991, ch. I, I.5.1.3 and I.6.1.1--3; EID context: ch. V, p. 185, Notes p. 302, and
EBM section 4.2.
-/
theorem mul_gamma_eq_zero_of_shift (hL : D.Local) (G : D.CarreDuChamp)
    (v w h : D.toCapacity.Space) (a : ℝ) (hh : h ∈ D.toCapacity.bddSpace)
    (hhw : ∀ᵐ x ∂m, D.toCapacity.toLp h x * (D.toCapacity.toLp w x + a) = 0) :
    ∀ᵐ x ∂m, D.toCapacity.toLp h x * G.Γ v w x = 0 := by
  have hm := D.bounded_memLp_top h hh
  obtain ⟨C, hC⟩ := hh
  let b : ℕ → Lp ℝ 1 m := fun n =>
    G.Γ (D.toCapacity.truncS n v) (D.toCapacity.truncS n w)
  have hb : ∀ᶠ n in atTop, boundedMul (D.toCapacity.toLp h) hm (b n) = 0 := by
    filter_upwards [eventually_ge_atTop ⌈|a|⌉₊] with n hn
    have hn' : |a| ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have h0 := D.mul_gamma_eq_zero_of_shift_bounded hL G _ _ h a
      (D.toCapacity.truncS_mem n v) (D.toCapacity.truncS_mem n w) ⟨C, hC⟩
      (D.mul_truncS_add_eq_zero h w a n hn' hhw)
    apply Lp.ext
    filter_upwards [h0, coeFn_boundedMul (D.toCapacity.toLp h) hm (b n),
      Lp.coeFn_zero ℝ 1 m] with x hx hbx hz
    change (0 : Lp ℝ 1 m) x = 0 at hz
    rw [hbx, hz]
    exact hx
  have ht : Tendsto b atTop (𝓝 (G.Γ v w)) :=
    (G.Γ.continuous₂.tendsto (v, w)).comp
      ((D.toCapacity.tendsto_contract_trunc v).prodMk_nhds
        (D.toCapacity.tendsto_contract_trunc w))
  have hlim := tendsto_boundedMul hm hC ht
  have hz : boundedMul (D.toCapacity.toLp h) hm (G.Γ v w) = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hb.mono fun _ hn => hn.symm))
  filter_upwards [coeFn_boundedMul (D.toCapacity.toLp h) hm (G.Γ v w),
    Lp.coeFn_zero ℝ 1 m] with x hx h0
  change (0 : Lp ℝ 1 m) x = 0 at h0
  rw [← hx, hz, h0]

/-- Subtracting the value at zero preserves a scalar function's Lipschitz constant. -/
theorem lipschitzWith_centered {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) :
    LipschitzWith L (fun t => F t - F 0) := by
  have hs : LipschitzWith 1 (fun t : ℝ => t - F 0) :=
    (IsometryEquiv.subRight (F 0)).isometry.lipschitz
  simpa only [one_mul, Function.comp_def] using hs.comp hF

/-- A scalar 1-Lipschitz composition centered at zero in the original form space. -/
def centeredComp (F : ℝ → ℝ) (hF : LipschitzWith 1 F)
    (v : D.toCapacity.Space) : D.toCapacity.Space :=
  D.toCapacity.contract (lipschitzWith_centered hF) (sub_self _) v

/-- The centered composition has representative F(v)-F(0) almost everywhere. -/
theorem coe_centeredComp (F : ℝ → ℝ) (hF : LipschitzWith 1 F)
    (v : D.toCapacity.Space) :
    ⇑(D.toCapacity.toLp (D.centeredComp F hF v)) =ᵐ[m]
      fun x => F (D.toCapacity.toLp v x) - F 0 :=
  D.toCapacity.coe_contractLp (lipschitzWith_centered hF) (sub_self _) v

/-- A bounded 1-Lipschitz scalar profile yields a bounded centered domain composition. -/
theorem centeredComp_bounded (F : ℝ → ℝ) (hF : LipschitzWith 1 F)
    (M : ℝ) (hM : ∀ t, |F t| ≤ M) (v : D.toCapacity.Space) :
    D.centeredComp F hF v ∈ D.toCapacity.bddSpace := by
  refine ⟨M + M, ?_⟩
  filter_upwards [D.coe_centeredComp F hF v] with x hx
  rw [hx]
  exact (abs_sub _ _).trans (add_le_add (hM _) (hM _))

/--
Multiplication of a bounded 1-Lipschitz scalar profile composed with a domain argument by a bounded
domain test has a bounded domain representative almost everywhere. Its centered composition and a
scalar multiple of the test supply that representative.
-/
theorem exists_bounded_mul_comp (F : ℝ → ℝ) (hF : LipschitzWith 1 F)
    (M : ℝ) (hM : ∀ t, |F t| ≤ M) (u z : D.toCapacity.Space)
    (hz : z ∈ D.toCapacity.bddSpace) :
    ∃ h : D.toCapacity.Space, h ∈ D.toCapacity.bddSpace ∧
      ⇑(D.toCapacity.toLp h) =ᵐ[m] fun x =>
        D.toCapacity.toLp z x * F (D.toCapacity.toLp u x) := by
  let q := D.centeredComp F hF u
  have hq : q ∈ D.toCapacity.bddSpace := D.centeredComp_bounded F hF M hM u
  refine ⟨D.toCapacity.mulS z q + F 0 • z,
    D.toCapacity.bddSpace.add_mem (D.toCapacity.mulS_mem hz hq)
      (D.toCapacity.bddSpace.smul_mem (F 0) hz), ?_⟩
  simp only [map_add, map_smul]
  filter_upwards [D.toCapacity.coeFn_toLp_mulS hz hq, D.coe_centeredComp F hF u,
    Lp.coeFn_add (D.toCapacity.toLp (D.toCapacity.mulS z q)) (F 0 • D.toCapacity.toLp z),
    Lp.coeFn_smul (F 0) (D.toCapacity.toLp z)] with x p qx r s
  change D.toCapacity.toLp q x = _ at qx
  rw [r, Pi.add_apply, s, Pi.smul_apply, smul_eq_mul, p, qx]
  ring

/-- The translated residual profile is 1-Lipschitz for a nonnegative threshold. -/
theorem lipschitzWith_shifted_residual (c : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    LipschitzWith 1 (fun t => softThreshold ε (t - c)) := by
  have hs : LipschitzWith 1 (fun t : ℝ => t - c) :=
    (IsometryEquiv.subRight c).isometry.lipschitz
  simpa only [one_mul, Function.comp_def] using (lipschitzWith_softThreshold hε).comp hs

/--
The residual around a fixed real level is centered before composition, with threshold equal to the
reciprocal of n+1.
-/
def levelResidual (c : ℝ) (n : ℕ) (u : D.toCapacity.Space) : D.toCapacity.Space :=
  D.centeredComp (fun t => softThreshold ((n : ℝ) + 1)⁻¹ (t - c))
    (lipschitzWith_shifted_residual c (by positivity)) u

/-- Almost everywhere representative of the centered residual at a fixed real level. -/
theorem coe_levelResidual (c : ℝ) (n : ℕ) (u : D.toCapacity.Space) :
    ⇑(D.toCapacity.toLp (D.levelResidual c n u)) =ᵐ[m] fun x =>
      softThreshold ((n : ℝ) + 1)⁻¹ (D.toCapacity.toLp u x - c) -
        softThreshold ((n : ℝ) + 1)⁻¹ (-c) := by
  simpa only [levelResidual, zero_sub] using D.coe_centeredComp
    (fun t => softThreshold ((n : ℝ) + 1)⁻¹ (t - c))
    (lipschitzWith_shifted_residual c (by positivity)) u

/--
Every centered 1-Lipschitz scalar composition decreases energy. Consequence of BH 1991, ch. I,
normal contractions; EBM section 4.2.
-/
theorem energy_centeredComp_le (F : ℝ → ℝ) (hF : LipschitzWith 1 F)
    (u : D.toCapacity.Space) :
    D.toCapacity.ener (D.centeredComp F hF u) (D.centeredComp F hF u) ≤
      D.toCapacity.ener u u := by
  obtain ⟨hw, he⟩ := D.normal_contraction (lipschitzWith_centered hF) (sub_self _)
    (D.form.formToDomain u) _ (D.coe_centeredComp F hF u)
  simp only [D.toCapacity.ener_apply]
  exact he

/--
Residuals centered around a fixed real level converge to the original argument in the form norm. The
proof uses the energy bound and dominated L2 convergence on the original measure; BH 1991, ch. I,
and EBM section 4.2.
-/
theorem tendsto_levelResidual (c : ℝ) (u : D.toCapacity.Space) :
    Tendsto (fun n => D.levelResidual c n u) atTop (𝓝 u) := by
  have ht : Tendsto (fun n => D.toCapacity.toLp (D.levelResidual c n u)) atTop
      (𝓝 (D.toCapacity.toLp u)) := by
    have h := Foundations.tendsto_toLp_dominated m
      (fun n => Lp.memLp (D.toCapacity.toLp (D.levelResidual c n u)))
      (Lp.memLp (D.toCapacity.toLp u)) (Lp.memLp (D.toCapacity.toLp u)).norm
      (fun n => ?_) ?_
    · have he : ∀ z : Lp ℝ 2 m, (Lp.memLp z).toLp _ = z :=
        fun z => Lp.ext (Lp.memLp z).coeFn_toLp
      simpa only [he] using h
    · filter_upwards [D.coe_levelResidual c n u] with x hx
      have hb := (lipschitzWith_shifted_residual c (by positivity :
        (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹)).dist_le_mul (D.toCapacity.toLp u x) 0
      simpa only [hx, Real.norm_eq_abs, Real.dist_eq, sub_zero, zero_sub,
        NNReal.coe_one, one_mul] using hb
    · filter_upwards [ae_all_iff.mpr (fun n => D.coe_levelResidual c n u)] with x hx
      have h := (tendsto_softThreshold (D.toCapacity.toLp u x - c)).sub
        (tendsto_softThreshold (-c))
      simpa only [hx, sub_neg_eq_add, sub_add_cancel] using h
  have hs := D.closed.tendsto_formSpace_of_energy_le
    (u := fun n => D.form.formToDomain (D.levelResidual c n u))
    (v := D.form.formToDomain u) ht (fun n => by
      simpa only [D.toCapacity.ener_apply, levelResidual] using
        D.energy_centeredComp_le (fun t => softThreshold ((n : ℝ) + 1)⁻¹ (t - c))
          (lipschitzWith_shifted_residual c (by positivity)) u)
  simpa only [LinearEquiv.symm_apply_apply] using hs

/--
The translated triangular bump with nonnegative height is 1-Lipschitz and bounded in absolute
value by its height.
-/
theorem level_bump_properties (c : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    LipschitzWith 1 (fun t => max (ε - |t - c|) 0) ∧
      ∀ t, |max (ε - |t - c|) 0| ≤ ε := by
  constructor
  · have hs : LipschitzWith 1 (fun t : ℝ => t - c) :=
      (IsometryEquiv.subRight c).isometry.lipschitz
    simpa only [one_mul, Function.comp_def] using (ErrorCalculus.lipschitzWith_bump ε).comp hs
  · intro t
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [abs_nonneg (t - c)]) hε

/--
The triangular bump times the uncentered residual is zero for every scalar argument, center, and
threshold.
-/
theorem level_bump_mul_softThreshold (c : ℝ) (ε : ℝ) (t : ℝ) :
    max (ε - |t - c|) 0 * softThreshold ε (t - c) = 0 := by
  by_cases ht : |t - c| ≤ ε
  · obtain ⟨h1, h2⟩ := abs_le.mp ht
    simp only [softThreshold, min_eq_left h2, max_eq_left h1, sub_self, mul_zero]
  · rw [max_eq_right (by linarith [lt_of_not_ge ht]), zero_mul]

/--
Conditional on BH locality, every bounded domain test annihilates Gamma(v,R_n(u)) almost everywhere
on the fixed level set of u.
-/
theorem mul_gamma_levelResidual_on_level (hL : D.Local) (G : D.CarreDuChamp)
    (u v z : D.toCapacity.Space) (hz : z ∈ D.toCapacity.bddSpace) (c : ℝ) (n : ℕ) :
    ∀ᵐ x ∂m, D.toCapacity.toLp u x = c →
      D.toCapacity.toLp z x * G.Γ v (D.levelResidual c n u) x = 0 := by
  let ε : ℝ := ((n : ℝ) + 1)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  let F : ℝ → ℝ := fun t => max (ε - |t - c|) 0
  obtain ⟨h, hh, hrep⟩ := D.exists_bounded_mul_comp F
    (level_bump_properties c hε.le).1 ε (level_bump_properties c hε.le).2 u z hz
  have hprod : ∀ᵐ x ∂m, D.toCapacity.toLp h x *
      (D.toCapacity.toLp (D.levelResidual c n u) x + softThreshold ε (-c)) = 0 := by
    filter_upwards [hrep, D.coe_levelResidual c n u] with x p q
    rw [p, q]
    change D.toCapacity.toLp z x * F (D.toCapacity.toLp u x) *
      (softThreshold ε (D.toCapacity.toLp u x - c) - softThreshold ε (-c) +
        softThreshold ε (-c)) = 0
    rw [sub_add_cancel, mul_assoc, level_bump_mul_softThreshold, mul_zero]
  have hzero := D.mul_gamma_eq_zero_of_shift hL G v (D.levelResidual c n u) h
    (softThreshold ε (-c)) hh hprod
  filter_upwards [hrep, hzero] with x p q hx
  have hFx : F (D.toCapacity.toLp u x) = ε := by
    simp only [F, hx, sub_self, abs_zero, sub_zero, max_eq_left hε.le]
  rw [p, hFx] at q
  have he : ε * (D.toCapacity.toLp z x * G.Γ v (D.levelResidual c n u) x) = 0 := by
    nlinarith [q]
  exact (mul_eq_zero.mp he).resolve_left hε.ne'

/--
A fixed essentially bounded measurable multiplier preserves almost everywhere annihilation under L1
convergence.
-/
theorem mul_eq_zero_of_tendsto_L1 {q : X → ℝ} (hq : MemLp q ∞ m) {C : ℝ}
    (hC : ∀ᵐ x ∂m, |q x| ≤ C) {a : ℕ → Lp ℝ 1 m} {b : Lp ℝ 1 m}
    (ht : Tendsto a atTop (𝓝 b))
    (hz : ∀ n, ∀ᵐ x ∂m, q x * a n x = 0) :
    ∀ᵐ x ∂m, q x * b x = 0 := by
  have he : ∀ n, boundedMul q hq (a n) = 0 := by
    intro n
    apply Lp.ext
    filter_upwards [coeFn_boundedMul q hq (a n), hz n, Lp.coeFn_zero ℝ 1 m]
      with x p qx r
    change (0 : Lp ℝ 1 m) x = 0 at r
    rw [p, qx, r]
  have hlim := tendsto_boundedMul hq hC ht
  have h0 : boundedMul q hq b = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun n => (he n).symm)
  filter_upwards [coeFn_boundedMul q hq b, Lp.coeFn_zero ℝ 1 m] with x p r
  change (0 : Lp ℝ 1 m) x = 0 at r
  rw [← p, h0, r]

/--
Conditional on BH locality, every bounded domain test annihilates Gamma(v,u) almost everywhere on a
fixed real level of u. The L1 limit uses the fixed multiplier given by the test times the level
indicator.
-/
theorem mul_gamma_on_level (hL : D.Local) (G : D.CarreDuChamp)
    (u v z : D.toCapacity.Space) (hz : z ∈ D.toCapacity.bddSpace) (c : ℝ) :
    ∀ᵐ x ∂m, D.toCapacity.toLp u x = c → D.toCapacity.toLp z x * G.Γ v u x = 0 := by
  let S : Set X := {x | D.toCapacity.toLp u x = c}
  have hS : MeasurableSet S :=
    (Lp.stronglyMeasurable (D.toCapacity.toLp u)).measurable (measurableSet_singleton c)
  let q : X → ℝ := S.indicator (D.toCapacity.toLp z)
  have hq : MemLp q ∞ m := (D.bounded_memLp_top z hz).indicator hS
  obtain ⟨C, hC⟩ := hz
  have hC' : ∀ᵐ x ∂m, |q x| ≤ max C 0 := by
    filter_upwards [hC] with x hx
    by_cases hs : x ∈ S
    · simpa only [q, Set.indicator_of_mem hs] using hx.trans (le_max_left C 0)
    · simp only [q, Set.indicator_of_notMem hs, abs_zero, le_max_iff, le_refl, or_true]
  have ht : Tendsto (fun n => G.Γ v (D.levelResidual c n u)) atTop (𝓝 (G.Γ v u)) :=
    (G.Γ v).continuous.continuousAt.tendsto.comp (D.tendsto_levelResidual c u)
  have h0 := mul_eq_zero_of_tendsto_L1 hq hC' ht (fun n => ?_)
  · filter_upwards [h0] with x hx hs
    have hs' : x ∈ S := hs
    simpa only [q, Set.indicator_of_mem hs'] using hx
  · filter_upwards [D.mul_gamma_levelResidual_on_level hL G u v z ⟨C, hC⟩ c n]
      with x hx
    by_cases hs : x ∈ S
    · simpa only [q, Set.indicator_of_mem hs] using hx hs
    · simp only [q, Set.indicator_of_notMem hs, zero_mul]

/--
Conditional on BH locality, Gamma(u,v) vanishes almost everywhere on a fixed real level of u in the
form-space adapter. Bounded domain tests are used individually for separation.
-/
theorem gamma_eq_zero_on_level_space (hL : D.Local) (G : D.CarreDuChamp)
    (u v : D.toCapacity.Space) (c : ℝ) :
    ∀ᵐ x ∂m, D.toCapacity.toLp u x = c → G.Γ u v x = 0 := by
  let S : Set X := {x | D.toCapacity.toLp u x = c}
  have hS : MeasurableSet S :=
    (Lp.stronglyMeasurable (D.toCapacity.toLp u)).measurable (measurableSet_singleton c)
  have hi : Integrable (S.indicator (G.Γ v u)) m := (L1.integrable_coeFn _).indicator hS
  have hzero : S.indicator (G.Γ v u) =ᵐ[m] (fun _ => 0) := by
    apply D.toCapacity.ae_eq_of_integral_mul_eq D.denseRange_toCapacity hi (integrable_zero _ _ _)
    intro z hz
    simp only [Pi.zero_apply, mul_zero, integral_zero]
    apply integral_eq_zero_of_ae
    filter_upwards [D.mul_gamma_on_level hL G u v z hz c] with x hx
    by_cases hs : x ∈ S
    · rw [Set.indicator_of_mem hs]
      exact hx hs
    · rw [Set.indicator_of_notMem hs, mul_zero, Pi.zero_apply]
  filter_upwards [hzero] with x hx hs
  have hs' : x ∈ S := hs
  rw [Set.indicator_of_mem hs'] at hx
  rwa [G.symm] at hx

/--
Conditional on BH locality, Gamma(f,g) vanishes almost everywhere where the original domain
representative f equals a fixed real level. Consequence of BH 1991, ch. I, I.5.2.3 and I.6.1.1
--3; EID context: ch. V, p. 185, Notes p. 302, and EBM section 4.2.
-/
theorem gamma_eq_zero_on_level (hL : D.Local) (G : D.CarreDuChamp)
    (f g : D.form.dom) (a : ℝ) :
    ∀ᵐ x ∂m, (f : Lp ℝ 2 m) x = a →
      G.Γ (D.form.formToDomain.symm f) (D.form.formToDomain.symm g) x = 0 :=
  D.gamma_eq_zero_on_level_space hL G
    (D.form.formToDomain.symm f) (D.form.formToDomain.symm g) a

/--
Conditional on BH locality, the Gamma values of two domain arguments against a third agree almost
everywhere wherever their representatives differ by a fixed scalar.
-/
theorem gamma_eq_on_shifted_eq (hL : D.Local) (G : D.CarreDuChamp)
    (u w v : D.toCapacity.Space) (c : ℝ) :
    ∀ᵐ x ∂m, D.toCapacity.toLp u x - D.toCapacity.toLp w x = c →
      G.Γ u v x = G.Γ w v x := by
  have hg : G.Γ (u - w) v = G.Γ u v - G.Γ w v := by
    simp only [map_sub, sub_apply]
  have h0 := D.gamma_eq_zero_on_level_space hL G (u - w) v c
  rw [hg] at h0
  simp only [map_sub] at h0
  filter_upwards [h0, Lp.coeFn_sub (D.toCapacity.toLp u) (D.toCapacity.toLp w),
    Lp.coeFn_sub (G.Γ u v) (G.Γ w v)] with x p q r hx
  have hp := p (by simpa only [q, Pi.sub_apply] using hx)
  simpa only [r, Pi.sub_apply, sub_eq_zero] using hp

/--
Conditional on BH locality, Gamma(u,v) vanishes almost everywhere on the inverse image under u of a
fixed countable set of real levels, with one common null exception.
-/
theorem gamma_eq_zero_on_countable_levels (hL : D.Local) (G : D.CarreDuChamp)
    (u v : D.toCapacity.Space) {S : Set ℝ} (hS : S.Countable) :
    ∀ᵐ x ∂m, D.toCapacity.toLp u x ∈ S → G.Γ u v x = 0 := by
  have h := (ae_ball_iff hS).mpr
    (fun c (_ : c ∈ S) => D.gamma_eq_zero_on_level_space hL G u v c)
  filter_upwards [h] with x hx hs
  exact hx _ hs rfl

/--
The difference between an argument and its centered level residual converges to zero in the form
norm.
-/
theorem tendsto_small_centered_cutoff (c : ℝ) (u : D.toCapacity.Space) :
    Tendsto (fun n => u - D.levelResidual c n u) atTop (𝓝 0) := by
  simpa only [sub_self] using
    (tendsto_const_nhds (x := u)).sub (D.tendsto_levelResidual c u)

/--
Conditional on BH locality, the centered clamp has a representative in the original domain
whose Gamma against every domain argument equals the original Gamma on the open clipping
interval and vanishes elsewhere almost everywhere, including both endpoints. Consequence of BH
1991, ch. I, I.5.2.3 and I.6.1.1--3; EID context: ch. V, p. 185, Notes p. 302, and EBM section 4.2.
-/
theorem centered_clampRule (hL : D.Local) (G : D.CarreDuChamp)
    (f : D.form.dom) (a b : ℝ) (hab : a ≤ b) :
    ∃ w : D.form.dom,
      (⇑(w : Lp ℝ 2 m) =ᵐ[m] fun x =>
        max a (min ((f : Lp ℝ 2 m) x) b) - max a (min 0 b)) ∧
      ∀ g : D.form.dom,
        ⇑(G.Γ (D.form.formToDomain.symm w) (D.form.formToDomain.symm g)) =ᵐ[m]
          fun x => Set.indicator {x | a < (f : Lp ℝ 2 m) x ∧ (f : Lp ℝ 2 m) x < b}
            (fun x => G.Γ (D.form.formToDomain.symm f) (D.form.formToDomain.symm g) x) x := by
  let F : ℝ → ℝ := fun t => max a (min t b)
  have hF : LipschitzWith 1 F :=
    (LipschitzWith.id.min_const b).const_max a
  let u := D.form.formToDomain.symm f
  let w := D.centeredComp F hF u
  have hw := D.coe_centeredComp F hF u
  refine ⟨D.form.formToDomain w, hw, ?_⟩
  intro g
  let v := D.form.formToDomain.symm g
  have hI := D.gamma_eq_on_shifted_eq hL G u w v (F 0)
  have hA := D.gamma_eq_zero_on_level_space hL G w v (a - F 0)
  have hB := D.gamma_eq_zero_on_level_space hL G w v (b - F 0)
  simp only [LinearEquiv.symm_apply_apply]
  filter_upwards [hw, hI, hA, hB] with x p q r s
  change D.toCapacity.toLp w x = F (D.toCapacity.toLp u x) - F 0 at p
  change G.Γ w v x = Set.indicator {x | a < D.toCapacity.toLp u x ∧
    D.toCapacity.toLp u x < b} (fun x => G.Γ u v x) x
  by_cases hi : a < D.toCapacity.toLp u x ∧ D.toCapacity.toLp u x < b
  · rw [Set.indicator_of_mem (show x ∈ {x | a < D.toCapacity.toLp u x ∧
      D.toCapacity.toLp u x < b} from hi)]
    symm
    apply q
    rw [p]
    dsimp [F]
    rw [min_eq_left hi.2.le, max_eq_right hi.1.le]
    ring
  · rw [Set.indicator_of_notMem (show x ∉ {x | a < D.toCapacity.toLp u x ∧
      D.toCapacity.toLp u x < b} from hi)]
    rcases not_and_or.mp hi with ha | hb
    · apply r
      rw [p]
      have he : F (D.toCapacity.toLp u x) = a :=
        max_eq_left ((min_le_left _ _).trans (le_of_not_gt ha))
      rw [he]
    · apply s
      rw [p]
      have he : F (D.toCapacity.toLp u x) = b := by
        dsimp [F]
        rw [min_eq_right (le_of_not_gt hb), max_eq_right hab]
      rw [he]

end DprBridge.BH1991.DirichletForm

#print axioms DprBridge.BH1991.DirichletForm.mul_gamma_eq_zero_of_shift_bounded
#print axioms DprBridge.BH1991.DirichletForm.mul_truncS_add_eq_zero
#print axioms DprBridge.BH1991.DirichletForm.mul_gamma_eq_zero_of_shift
#print axioms DprBridge.BH1991.DirichletForm.lipschitzWith_centered
#print axioms DprBridge.BH1991.DirichletForm.centeredComp
#print axioms DprBridge.BH1991.DirichletForm.coe_centeredComp
#print axioms DprBridge.BH1991.DirichletForm.centeredComp_bounded
#print axioms DprBridge.BH1991.DirichletForm.exists_bounded_mul_comp
#print axioms DprBridge.BH1991.DirichletForm.lipschitzWith_shifted_residual
#print axioms DprBridge.BH1991.DirichletForm.levelResidual
#print axioms DprBridge.BH1991.DirichletForm.coe_levelResidual
#print axioms DprBridge.BH1991.DirichletForm.energy_centeredComp_le
#print axioms DprBridge.BH1991.DirichletForm.tendsto_levelResidual
#print axioms DprBridge.BH1991.DirichletForm.level_bump_properties
#print axioms DprBridge.BH1991.DirichletForm.level_bump_mul_softThreshold
#print axioms DprBridge.BH1991.DirichletForm.mul_gamma_levelResidual_on_level
#print axioms DprBridge.BH1991.DirichletForm.mul_eq_zero_of_tendsto_L1
#print axioms DprBridge.BH1991.DirichletForm.mul_gamma_on_level
#print axioms DprBridge.BH1991.DirichletForm.gamma_eq_zero_on_level_space
#print axioms DprBridge.BH1991.DirichletForm.gamma_eq_zero_on_level
#print axioms DprBridge.BH1991.DirichletForm.gamma_eq_on_shifted_eq
#print axioms DprBridge.BH1991.DirichletForm.gamma_eq_zero_on_countable_levels
#print axioms DprBridge.BH1991.DirichletForm.tendsto_small_centered_cutoff
#print axioms DprBridge.BH1991.DirichletForm.centered_clampRule

#check @DprBridge.BH1991.DirichletForm.mul_gamma_eq_zero_of_shift
#check @DprBridge.BH1991.DirichletForm.gamma_eq_zero_on_level
#check @DprBridge.BH1991.DirichletForm.centered_clampRule
