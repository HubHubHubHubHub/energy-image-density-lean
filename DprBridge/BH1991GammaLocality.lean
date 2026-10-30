import DprBridge.BH1991NormalContractions
import DprBridge.BH1991Printed
import ErrorCalculus.Dirichlet.FormConvergence

/-!
# Positivity, locality and the BH energy identity

## Main results
Under BH locality and a supplied carré du champ, Gamma is local and satisfies the energy identity on
the original arbitrary measure, with Γ = 2γ. No constant in the form domain or sigma-finiteness is
required. The normal-current reduction for the sigma-finite EID conclusion is proved in
`DprBridge.BH1991PrintedProof`.

References: Bouleau–Hirsch (1991), ch. I, I.4.1.3, I.5.1.3 and I.6.1.1; ch. V, p. 185; Notes, p.
302. Eriksson-Bique–Murugan, arXiv:2510.13659v1, §4.2, supplies the normal-current method.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ErrorCalculus
open scoped NNReal ENNReal
universe u

namespace DprBridge.BH1991.DirichletForm
variable {X : Type u} [MeasurableSpace X] {m : Measure X} (D : DirichletForm m)

/-- Finite linear combinations commute with the continuous BH bilinear operator. -/
theorem gamma_sum_smul (G : D.CarreDuChamp) {n : ℕ}
    (v : Fin n → D.form.FormSpace) (a b : Fin n → ℝ) :
    G.Γ (∑ i, a i • v i) (∑ j, b j • v j) =
      ∑ i, ∑ j, (a i * b j) • G.Γ (v i) (v j) := by
  simp only [map_sum, map_smul, sum_apply,
    smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- The finite bilinear expansion holds almost everywhere for the selected L1 representatives. -/
theorem coe_gamma_sum_smul (G : D.CarreDuChamp) {n : ℕ}
    (v : Fin n → D.form.FormSpace) (a b : Fin n → ℝ) :
    ⇑(G.Γ (∑ i, a i • v i) (∑ j, b j • v j)) =ᵐ[m]
      fun x => ∑ i, ∑ j, a i * b j * G.Γ (v i) (v j) x := by
  classical
  rw [D.gamma_sum_smul]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => ∑ j, (a i * b j) • G.Γ (v i) (v j)),
    ae_all_iff.mpr (fun i => Lp.coeFn_fun_finsetSum Finset.univ
      (fun j => (a i * b j) • G.Γ (v i) (v j))),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
      Lp.coeFn_smul (a i * b j) (G.Γ (v i) (v j))))] with x h1 h2 h3
  simp only [h1, h2, h3, Pi.smul_apply, smul_eq_mul]

/--
The finite Gamma matrix is positive semidefinite on a single full-measure set. Consequence
of BH 1991, ch. I, I.4.1.3; EID context: ch. V, p. 185, Notes p. 302, and EBM §4.2.
-/
theorem gammaMatrix_posSemidef (G : D.CarreDuChamp)
    {n : ℕ} (f : Fin n → D.form.dom) :
    ∀ᵐ x ∂m, (D.gammaMatrix G f x).PosSemidef := by
  classical
  let v : Fin n → D.form.FormSpace := fun i => D.form.formToDomain.symm (f i)
  have hq : ∀ q : Fin n → ℚ, ∀ᵐ x ∂m,
      0 ≤ ∑ i, ∑ j, (q i : ℝ) * (q j : ℝ) * G.Γ (v i) (v j) x := by
    intro q
    filter_upwards [G.nonneg (∑ i, (q i : ℝ) • v i),
      D.coe_gamma_sum_smul G v (fun i => (q i : ℝ)) (fun i => (q i : ℝ))]
      with x hp he
    simpa only [he, Pi.zero_apply] using hp
  filter_upwards [ae_all_iff.mpr hq] with x hx
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact congrArg (fun z : Lp ℝ 1 m => z x) (G.symm (v j) (v i))
  · intro a
    have hd : DenseRange (fun q : Fin n → ℚ => fun i => (q i : ℝ)) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    have hr : 0 ≤ ∑ i, ∑ j, a i * a j * G.Γ (v i) (v j) x :=
      hd.induction_on a (isClosed_le continuous_const (by fun_prop)) hx
    simpa [gammaMatrix, v, dotProduct, Matrix.mulVec, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm] using hr

/--
The determinant of the finite Gamma matrix is nonnegative almost everywhere. Consequence of
BH 1991, ch. I, I.4.1.3; EID context: ch. V, p. 185, Notes p. 302.
-/
theorem gammaMatrix_det_nonneg (G : D.CarreDuChamp)
    {n : ℕ} (f : Fin n → D.form.dom) :
    ∀ᵐ x ∂m, 0 ≤ (D.gammaMatrix G f x).det :=
  (D.gammaMatrix_posSemidef G f).mono fun _ hx => hx.det_nonneg

/-- Each coordinate of the finite Gamma matrix is integrable. Consequence of the L1-valued
operator in BH 1991, ch. I, I.4.1.3; EBM §4.2. -/
theorem gammaMatrix_integrable (G : D.CarreDuChamp)
    {n : ℕ} (f : Fin n → D.form.dom) (i j : Fin n) :
    Integrable (fun x => D.gammaMatrix G f x i j) m :=
  L1.integrable_coeFn _

/--
Conditional on BH locality, the shifted zero-product energy identity holds on the form- preserving
capacity adapter. Using BH 1991, ch. I, I.5.1.3.
-/
theorem local_toCapacity (hL : D.Local) (f g : D.toCapacity.Space) (a : ℝ)
    (h : ∀ᵐ x ∂m, (D.toCapacity.toLp f x + a) * D.toCapacity.toLp g x = 0) :
    D.toCapacity.ener f g = 0 := by
  rw [D.toCapacity.ener_apply]
  exact hL (D.form.formToDomain f) (D.form.formToDomain g) a h

/--
An L1 class is zero if its integral pairing with every bounded domain test vanishes on the original
measure.
-/
theorem gamma_eq_zero_of_tests (b : Lp ℝ 1 m)
    (h : ∀ z ∈ D.toCapacity.bddSpace,
      ∫ x, D.toCapacity.toLp z x * b x ∂m = 0) : b = 0 := by
  apply D.toCapacity.eq_of_pair_eq D.denseRange_toCapacity
  intro z hz
  change (∫ x, D.toCapacity.toLp z x * b x ∂m) =
    ∫ x, D.toCapacity.toLp z x * (0 : Lp ℝ 1 m) x ∂m
  rw [h z hz]
  symm
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_zero ℝ 1 m] with x hx
  change (0 : Lp ℝ 1 m) x = 0 at hx
  change D.toCapacity.toLp z x * (0 : Lp ℝ 1 m) x = 0
  rw [hx, mul_zero]

/--
Conditional on BH locality, Gamma of two bounded domain arguments vanishes when their shifted
product is zero almost everywhere.
-/
theorem gamma_eq_zero_of_mul_bounded (hL : D.Local) (G : D.CarreDuChamp)
    (f g : D.toCapacity.Space) (a : ℝ)
    (hf : f ∈ D.toCapacity.bddSpace) (hg : g ∈ D.toCapacity.bddSpace)
    (h : ∀ᵐ x ∂m, (D.toCapacity.toLp f x + a) * D.toCapacity.toLp g x = 0) :
    G.Γ f g = 0 := by
  apply D.gamma_eq_zero_of_tests
  intro k hk
  let p := D.toCapacity.mulS f k
  let q := D.toCapacity.mulS g k
  let r := D.toCapacity.mulS f g
  have hp := D.toCapacity.coeFn_toLp_mulS hf hk
  have hq := D.toCapacity.coeFn_toLp_mulS hg hk
  have hr := D.toCapacity.coeFn_toLp_mulS hf hg
  have h1 := D.carreDuChamp_toCapacity G f hf g hg k hk
  have hpg : D.toCapacity.ener (p + a • k) g = 0 := by
    apply D.local_toCapacity hL _ _ 0
    simp only [map_add, map_smul]
    filter_upwards [h, hp, Lp.coeFn_add (D.toCapacity.toLp p) (a • D.toCapacity.toLp k),
      Lp.coeFn_smul a (D.toCapacity.toLp k)] with x hx hpx h3 h4
    rw [h3, Pi.add_apply, h4, Pi.smul_apply, smul_eq_mul, add_zero]
    change (D.toCapacity.toLp p x + a * D.toCapacity.toLp k x) * _ = 0
    change D.toCapacity.toLp p x = _ at hpx
    rw [hpx]
    linear_combination D.toCapacity.toLp k x * hx
  have hqf : D.toCapacity.ener q f = 0 := by
    rw [D.toCapacity.ener_symm]
    apply D.local_toCapacity hL _ _ a
    filter_upwards [h, hq] with x hx hqx
    change D.toCapacity.toLp q x = _ at hqx
    rw [hqx]
    linear_combination D.toCapacity.toLp k x * hx
  have hr' : r = (-a) • g := by
    apply D.toCapacity.eq_of_ae
    rw [map_smul]
    filter_upwards [h, hr, Lp.coeFn_smul (-a) (D.toCapacity.toLp g)] with x hx hrx hs
    change D.toCapacity.toLp r x = _ at hrx
    rw [hrx, hs, Pi.smul_apply, smul_eq_mul]
    linear_combination hx
  change D.toCapacity.ener p g + D.toCapacity.ener q f -
    D.toCapacity.ener k r = _ at h1
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul] at hpg
  rw [hqf, hr', map_smul, smul_eq_mul] at h1
  linarith

/--
Conditional on BH locality, Gamma of any two domain arguments vanishes when their shifted product is
zero almost everywhere.
-/
theorem gamma_eq_zero_of_mul (hL : D.Local) (G : D.CarreDuChamp)
    (f g : D.toCapacity.Space) (a : ℝ)
    (h : ∀ᵐ x ∂m, (D.toCapacity.toLp f x + a) * D.toCapacity.toLp g x = 0) :
    G.Γ f g = 0 := by
  have hz : ∀ n : ℕ, |a| ≤ n →
      G.Γ (D.toCapacity.truncS n f) (D.toCapacity.truncS n g) = 0 := by
    intro n hn
    apply D.gamma_eq_zero_of_mul_bounded hL G _ _ a
      (D.toCapacity.truncS_mem n f) (D.toCapacity.truncS_mem n g)
    have hf := D.toCapacity.coe_contractLp
      (Capacity.DirichletForm.lipschitzWith_trunc n)
      (Capacity.DirichletForm.trunc_zero n) f
    have hg := D.toCapacity.coe_contractLp
      (Capacity.DirichletForm.lipschitzWith_trunc n)
      (Capacity.DirichletForm.trunc_zero n) g
    simp only [Capacity.DirichletForm.truncS, Capacity.DirichletForm.toLp_contract]
    filter_upwards [h, hf, hg] with x hx hfx hgx
    rw [hfx, hgx]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rcases mul_eq_zero.mp hx with ha | hg0
    · have hfa : D.toCapacity.toLp f x = -a := by linarith
      have hab := abs_le.mp hn
      rw [hfa, min_eq_left (by linarith), max_eq_left (by linarith)]
      ring
    · rw [hg0, min_eq_left hn0, max_eq_left (neg_nonpos.mpr hn0), mul_zero]
  have ht := G.Γ.continuous₂.tendsto (f, g) |>.comp
    ((D.toCapacity.tendsto_contract_trunc f).prodMk_nhds
      (D.toCapacity.tendsto_contract_trunc g))
  have he : (fun n => G.Γ (D.toCapacity.truncS n f) (D.toCapacity.truncS n g))
      =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_ge_atTop ⌈|a|⌉₊] with n hn
    exact hz n ((Nat.le_ceil _).trans (by exact_mod_cast hn))
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)

/-- A bounded domain element has an L-infinity representative on an arbitrary measure. -/
theorem bounded_memLp_top (h : D.toCapacity.Space) (hh : h ∈ D.toCapacity.bddSpace) :
    MemLp (D.toCapacity.toLp h) ∞ m := by
  obtain ⟨C, hC⟩ := hh
  exact memLp_top_of_bound (Lp.aestronglyMeasurable _) C
    (hC.mono fun _ hx => by simpa only [Real.norm_eq_abs] using hx)

/--
Conditional on BH locality, bounded domain arguments satisfy h Gamma(v,w) = 0 almost everywhere
whenever h w = 0 almost everywhere.
-/
theorem mul_gamma_eq_zero_bounded (hL : D.Local) (G : D.CarreDuChamp)
    (v w h : D.toCapacity.Space) (hv : v ∈ D.toCapacity.bddSpace)
    (hw : w ∈ D.toCapacity.bddSpace) (hh : h ∈ D.toCapacity.bddSpace)
    (hhw : ∀ᵐ x ∂m, D.toCapacity.toLp h x * D.toCapacity.toLp w x = 0) :
    ∀ᵐ x ∂m, D.toCapacity.toLp h x * G.Γ v w x = 0 := by
  have hm : MemLp (D.toCapacity.toLp h) ∞ m := D.bounded_memLp_top h hh
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
      apply D.local_toCapacity hL _ _ 0
      filter_upwards [hp, hzrep, hhw] with x a b c
      change D.toCapacity.toLp z x = _ at b
      rw [a, b, add_zero]
      linear_combination D.toCapacity.toLp v x * D.toCapacity.toLp k x * c
    have e2 : D.toCapacity.ener (D.toCapacity.mulS w z) v = 0 := by
      apply D.local_toCapacity hL _ _ 0
      filter_upwards [hq, hzrep, hhw] with x a b c
      change D.toCapacity.toLp z x = _ at b
      rw [a, b, add_zero]
      linear_combination D.toCapacity.toLp v x * D.toCapacity.toLp k x * c
    have e3 : D.toCapacity.ener z (D.toCapacity.mulS v w) = 0 := by
      apply D.local_toCapacity hL _ _ 0
      filter_upwards [hr, hzrep, hhw] with x a b c
      change D.toCapacity.toLp z x = _ at b
      rw [a, b, add_zero]
      linear_combination D.toCapacity.toLp v x * D.toCapacity.toLp k x * c
    rw [e1, e2, e3] at h1
    have he : (∫ x, D.toCapacity.toLp k x * b x ∂m) =
        ∫ x, D.toCapacity.toLp z x * G.Γ v w x ∂m := by
      apply integral_congr_ae
      filter_upwards [coeFn_boundedMul (D.toCapacity.toLp h) hm (G.Γ v w), hzrep]
        with x a c
      change b x = _ at a
      change D.toCapacity.toLp z x = _ at c
      rw [a, c]
      ring
    rw [he]
    linarith
  filter_upwards [coeFn_boundedMul (D.toCapacity.toLp h) hm (G.Γ v w),
    Lp.coeFn_zero ℝ 1 m] with x hx hz
  change b x = _ at hx
  change (0 : Lp ℝ 1 m) x = 0 at hz
  rw [← hx, hb, hz]

/--
A zero product remains zero almost everywhere after symmetric truncation of its second factor.
-/
theorem mul_truncS_eq_zero (h w : D.toCapacity.Space) (n : ℕ)
    (hhw : ∀ᵐ x ∂m, D.toCapacity.toLp h x * D.toCapacity.toLp w x = 0) :
    ∀ᵐ x ∂m, D.toCapacity.toLp h x * D.toCapacity.toLp (D.toCapacity.truncS n w) x = 0 := by
  have hw := D.toCapacity.coe_contractLp
    (Capacity.DirichletForm.lipschitzWith_trunc n)
    (Capacity.DirichletForm.trunc_zero n) w
  simp only [Capacity.DirichletForm.truncS, Capacity.DirichletForm.toLp_contract]
  filter_upwards [hhw, hw] with x hx hwx
  rw [hwx]
  rcases mul_eq_zero.mp hx with hh0 | hw0
  · rw [hh0, zero_mul]
  · rw [hw0, min_eq_left (Nat.cast_nonneg n),
      max_eq_left (neg_nonpos.mpr (Nat.cast_nonneg n)), mul_zero]

/-- A fixed essentially bounded multiplier preserves L1 convergence on an arbitrary measure. -/
theorem tendsto_boundedMul {c : X → ℝ} (hc : MemLp c ∞ m) {C : ℝ}
    (hC : ∀ᵐ x ∂m, |c x| ≤ C) {a : ℕ → Lp ℝ 1 m} {b : Lp ℝ 1 m}
    (ht : Tendsto a atTop (𝓝 b)) :
    Tendsto (fun n => boundedMul c hc (a n)) atTop (𝓝 (boundedMul c hc b)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim := (tendsto_iff_norm_sub_tendsto_zero.mp ht).const_mul C
  rw [mul_zero] at hlim
  apply squeeze_zero (fun n => norm_nonneg _) _ hlim
  intro n
  rw [← boundedMul_sub c hc (a n) b]
  exact norm_boundedMul_le c hc (a n - b) hC

set_option maxHeartbeats 1000000 in
/--
Under BH locality, h Γ(v, w) = 0 almost everywhere for arbitrary domain elements v, w and a bounded
domain multiplier h satisfying hw = 0 almost everywhere. Elaboration of the form-space and L²
transports requires the local heartbeat budget.
-/
theorem mul_gamma_eq_zero (hL : D.Local) (G : D.CarreDuChamp)
    (v w h : D.toCapacity.Space) (hh : h ∈ D.toCapacity.bddSpace)
    (hhw : ∀ᵐ x ∂m, D.toCapacity.toLp h x * D.toCapacity.toLp w x = 0) :
    ∀ᵐ x ∂m, D.toCapacity.toLp h x * G.Γ v w x = 0 := by
  have hm : MemLp (D.toCapacity.toLp h) ∞ m := D.bounded_memLp_top h hh
  obtain ⟨C, hC⟩ := hh
  let a : ℕ → Lp ℝ 1 m := fun n =>
    G.Γ (D.toCapacity.truncS n v) (D.toCapacity.truncS n w)
  have ha : ∀ n, boundedMul (D.toCapacity.toLp h) hm (a n) = 0 := by
    intro n
    have h0 := D.mul_gamma_eq_zero_bounded hL G _ _ h
      (D.toCapacity.truncS_mem n v) (D.toCapacity.truncS_mem n w) ⟨C, hC⟩
      (D.mul_truncS_eq_zero h w n hhw)
    apply Lp.ext
    filter_upwards [h0, coeFn_boundedMul (D.toCapacity.toLp h) hm (a n),
      Lp.coeFn_zero ℝ 1 m] with x hx hb hz
    change (0 : Lp ℝ 1 m) x = 0 at hz
    rw [hb, hz]
    exact hx
  have ht : Tendsto a atTop (𝓝 (G.Γ v w)) :=
    (G.Γ.continuous₂.tendsto (v, w)).comp
      ((D.toCapacity.tendsto_contract_trunc v).prodMk_nhds
        (D.toCapacity.tendsto_contract_trunc w))
  have hlim := tendsto_boundedMul hm hC ht
  have hz : boundedMul (D.toCapacity.toLp h) hm (G.Γ v w) = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun n => (ha n).symm)
  filter_upwards [coeFn_boundedMul (D.toCapacity.toLp h) hm (G.Γ v w),
    Lp.coeFn_zero ℝ 1 m] with x hx h0
  change (0 : Lp ℝ 1 m) x = 0 at h0
  rw [← hx, hz, h0]

/-- The diagonal Gamma has total integral at most twice the energy. Consequence of BH 1991, ch.
I, I.4.1.3. -/
theorem integral_gamma_self_le (G : D.CarreDuChamp) (f : D.toCapacity.Space) :
    ∫ x, G.Γ f f x ∂m ≤ 2 * D.toCapacity.ener f f := by
  have he : ‖G.Γ f f‖ = ∫ x, G.Γ f f x ∂m := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [G.nonneg f] with x hx
    exact Real.norm_of_nonneg hx
  rw [← he]
  exact D.toCapacity.isCarreDuChamp_norm_le D.denseRange_toCapacity
    (D.carreDuChamp_toCapacity G) f

/--
Conditional on BH locality, a bounded domain function v satisfies the diagonal energy identity if a
bounded domain plateau h obeys h <= 1 and h v = v almost everywhere.
-/
theorem integral_gamma_self_of_plateau (hL : D.Local) (G : D.CarreDuChamp)
    (v h : D.toCapacity.Space) (hv : v ∈ D.toCapacity.bddSpace)
    (hh : h ∈ D.toCapacity.bddSpace)
    (hupper : ∀ᵐ x ∂m, D.toCapacity.toLp h x ≤ 1)
    (hplateau : ∀ᵐ x ∂m, D.toCapacity.toLp h x * D.toCapacity.toLp v x =
      D.toCapacity.toLp v x) :
    ∫ x, G.Γ v v x ∂m = 2 * D.toCapacity.ener v v := by
  have hvh : D.toCapacity.mulS v h = v := by
    apply D.toCapacity.eq_of_ae
    filter_upwards [D.toCapacity.coeFn_toLp_mulS hv hh, hplateau] with x he hp
    rw [he, mul_comm]
    exact hp
  have hEr : D.toCapacity.ener h (D.toCapacity.mulS v v) = 0 := by
    apply D.local_toCapacity hL _ _ (-1)
    filter_upwards [D.toCapacity.coeFn_toLp_mulS hv hv, hplateau] with x he hp
    rw [he]
    linear_combination D.toCapacity.toLp v x * hp
  have hi := D.carreDuChamp_toCapacity G v hv v hv h hh
  rw [hvh, hEr] at hi
  have hle : (∫ x, D.toCapacity.toLp h x * G.Γ v v x ∂m) ≤ ∫ x, G.Γ v v x ∂m := by
    apply integral_mono_ae (D.toCapacity.integrable_pair hh _) (L1.integrable_coeFn _)
    filter_upwards [hupper, G.nonneg v] with x hx hp
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hx hp
  have hb := D.integral_gamma_self_le G v
  linarith

/-- The scalar residual is t minus its symmetric min/max truncation at level c. -/
def softThreshold (c t : ℝ) : ℝ := t - max (min t c) (-c)

/-- The scalar residual fixes zero for every nonnegative level. -/
theorem softThreshold_zero {c : ℝ} (hc : 0 ≤ c) : softThreshold c 0 = 0 := by
  simp [softThreshold, min_eq_left hc, max_eq_left (neg_nonpos.mpr hc)]

/-- The scalar residual is 1-Lipschitz at every nonnegative level. -/
theorem lipschitzWith_softThreshold {c : ℝ} (_hc : 0 ≤ c) :
    LipschitzWith 1 (softThreshold c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  have hab1 := le_abs_self (x - y)
  have hab2 := neg_le_abs (x - y)
  apply abs_le.mpr
  simp only [softThreshold, min_def, max_def]
  split_ifs <;> constructor <;> linarith

/-- At a nonnegative level, the scalar residual is dominated in absolute value by its input. -/
theorem abs_softThreshold_le {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    |softThreshold c t| ≤ |t| := by
  have h := (lipschitzWith_softThreshold hc).dist_le_mul t 0
  simpa only [softThreshold_zero hc, Real.dist_eq, sub_zero, NNReal.coe_one,
    one_mul] using h

/-- The scalar residual at level 1/(n+1) tends pointwise to its input. -/
theorem tendsto_softThreshold (t : ℝ) :
    Tendsto (fun n : ℕ => softThreshold ((n : ℝ) + 1)⁻¹ t) atTop (𝓝 t) := by
  have hc : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
  have ht : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
  simpa [softThreshold] using ht.sub ((ht.min hc).max hc.neg)

/-- The residual cutoff at level 1/(n+1) is obtained by contraction in the original form space. -/
def residual (n : ℕ) (f : D.toCapacity.Space) : D.toCapacity.Space :=
  D.toCapacity.contract (lipschitzWith_softThreshold (by positivity :
    (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹)) (softThreshold_zero (by positivity)) f

/-- The residual cutoff is represented almost everywhere by the scalar residual at level 1/(n+1). -/
theorem coe_residual (n : ℕ) (f : D.toCapacity.Space) :
    ⇑(D.toCapacity.toLp (D.residual n f)) =ᵐ[m]
      fun x => softThreshold ((n : ℝ) + 1)⁻¹ (D.toCapacity.toLp f x) :=
  D.toCapacity.coe_contractLp (lipschitzWith_softThreshold (by positivity :
    (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹)) (softThreshold_zero (by positivity)) f

/-- Residual cutoffs retain essential boundedness. -/
theorem residual_bounded (n : ℕ) (f : D.toCapacity.Space)
    (hf : f ∈ D.toCapacity.bddSpace) : D.residual n f ∈ D.toCapacity.bddSpace := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  filter_upwards [hC, D.coe_residual n f] with x hx he
  rw [he]
  exact (abs_softThreshold_le (by positivity) _).trans hx

/-- Residual cutoffs have no greater energy than their input. -/
theorem energy_residual_le (n : ℕ) (f : D.toCapacity.Space) :
    D.toCapacity.ener (D.residual n f) (D.residual n f) ≤ D.toCapacity.ener f f := by
  have h := D.normal_contraction (lipschitzWith_softThreshold (by positivity :
      (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹)) (softThreshold_zero (by positivity))
    (D.form.formToDomain f) (D.toCapacity.toLp (D.residual n f)) (D.coe_residual n f)
  obtain ⟨hw, he⟩ := h
  simp only [D.toCapacity.ener_apply]
  exact he

/--
Residual cutoffs converge to their input in the form norm, by dominated L2 convergence and the
closed-form energy bound.
-/
theorem tendsto_residual (f : D.toCapacity.Space) :
    Tendsto (fun n => D.residual n f) atTop (𝓝 f) := by
  have ht : Tendsto (fun n => D.toCapacity.toLp (D.residual n f)) atTop
      (𝓝 (D.toCapacity.toLp f)) := by
    have h := Foundations.tendsto_toLp_dominated m
      (fun n => Lp.memLp (D.toCapacity.toLp (D.residual n f)))
      (Lp.memLp (D.toCapacity.toLp f)) (Lp.memLp (D.toCapacity.toLp f)).norm
      (fun n => ?_) ?_
    · have he : ∀ z : Lp ℝ 2 m, (Lp.memLp z).toLp _ = z :=
        fun z => Lp.ext (Lp.memLp z).coeFn_toLp
      simpa only [he] using h
    · filter_upwards [D.coe_residual n f] with x hx
      simpa only [hx, Real.norm_eq_abs] using abs_softThreshold_le
        (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹) (D.toCapacity.toLp f x)
    · filter_upwards [ae_all_iff.mpr (fun n => D.coe_residual n f)] with x hx
      simpa only [hx] using tendsto_softThreshold (D.toCapacity.toLp f x)
  have hs := D.closed.tendsto_formSpace_of_energy_le
    (u := fun n => D.form.formToDomain (D.residual n f))
    (v := D.form.formToDomain f) ht (fun n => by
      simpa only [D.toCapacity.ener_apply] using D.energy_residual_le n f)
  simpa only [LinearEquiv.symm_apply_apply] using hs

/-- The domain plateau is the unit truncation of (n+1) times the domain absolute value. -/
def residualPlateau (n : ℕ) (f : D.toCapacity.Space) : D.toCapacity.Space :=
  D.toCapacity.contract Capacity.DirichletForm.lipschitzWith_unitF
    Capacity.DirichletForm.unitF_zero (((n : ℝ) + 1) • D.toCapacity.absS f)

/--
The plateau is represented almost everywhere by the unit truncation of (n+1) times the absolute
value of the input representative.
-/
theorem coe_residualPlateau (n : ℕ) (f : D.toCapacity.Space) :
    ⇑(D.toCapacity.toLp (D.residualPlateau n f)) =ᵐ[m] fun x =>
      Capacity.DirichletForm.unitF (((n : ℝ) + 1) * |D.toCapacity.toLp f x|) := by
  have hc := D.toCapacity.coe_contractLp Capacity.DirichletForm.lipschitzWith_unitF
    Capacity.DirichletForm.unitF_zero (((n : ℝ) + 1) • D.toCapacity.absS f)
  have he : D.toCapacity.toLp (((n : ℝ) + 1) • D.toCapacity.absS f) =
      ((n : ℝ) + 1) • |D.toCapacity.toLp f| := by
    rw [map_smul, D.toCapacity.toLp_absS]
  change ⇑(D.toCapacity.toLp (D.residualPlateau n f)) =ᵐ[m] _ at hc
  rw [he] at hc
  filter_upwards [hc, Lp.coeFn_smul ((n : ℝ) + 1) |D.toCapacity.toLp f|,
    Lp.coeFn_abs (D.toCapacity.toLp f)] with x h1 h2 h3
  simpa only [h2, h3, Pi.smul_apply, smul_eq_mul] using h1

/-- The domain plateau takes values in the unit interval almost everywhere. -/
theorem residualPlateau_unit (n : ℕ) (f : D.toCapacity.Space) :
    ∀ᵐ x ∂m, 0 ≤ D.toCapacity.toLp (D.residualPlateau n f) x ∧
      D.toCapacity.toLp (D.residualPlateau n f) x ≤ 1 := by
  filter_upwards [D.coe_residualPlateau n f] with x hx
  rw [hx]
  exact Capacity.DirichletForm.unitF_mem _

/-- The domain plateau belongs to the bounded form algebra. -/
theorem residualPlateau_bounded (n : ℕ) (f : D.toCapacity.Space) :
    D.residualPlateau n f ∈ D.toCapacity.bddSpace := by
  refine ⟨1, ?_⟩
  filter_upwards [D.residualPlateau_unit n f] with x hx
  simpa only [abs_of_nonneg hx.1] using hx.2

/--
For positive b, the unit truncation of b times the input modulus fixes the scalar residual at level
1/b by multiplication.
-/
theorem unitF_mul_softThreshold {b : ℝ} (hb : 0 < b) (t : ℝ) :
    Capacity.DirichletForm.unitF (b * |t|) * softThreshold b⁻¹ t =
      softThreshold b⁻¹ t := by
  by_cases ht : |t| ≤ b⁻¹
  · have ht' := abs_le.mp ht
    have hz : softThreshold b⁻¹ t = 0 := by
      simp only [softThreshold, min_eq_left ht'.2, max_eq_left ht'.1, sub_self]
    simp only [hz, mul_zero]
  · have hbt : 1 ≤ b * |t| := by
      have h := mul_le_mul_of_nonneg_left (le_of_not_ge ht) hb.le
      rwa [mul_inv_cancel₀ hb.ne'] at h
    rw [Capacity.DirichletForm.unitF_eq_one hbt, one_mul]

/-- Multiplication by the domain plateau fixes the residual cutoff almost everywhere. -/
theorem residualPlateau_mul_residual (n : ℕ) (f : D.toCapacity.Space) :
    ∀ᵐ x ∂m, D.toCapacity.toLp (D.residualPlateau n f) x *
      D.toCapacity.toLp (D.residual n f) x = D.toCapacity.toLp (D.residual n f) x := by
  filter_upwards [D.coe_residualPlateau n f, D.coe_residual n f] with x hh hv
  rw [hh, hv]
  exact unitF_mul_softThreshold (by positivity) _

/--
Conditional on BH locality, every residual cutoff of a bounded domain element satisfies the diagonal
energy identity.
-/
theorem integral_gamma_residual (hL : D.Local) (G : D.CarreDuChamp)
    (f : D.toCapacity.Space) (hf : f ∈ D.toCapacity.bddSpace) (n : ℕ) :
    ∫ x, G.Γ (D.residual n f) (D.residual n f) x ∂m =
      2 * D.toCapacity.ener (D.residual n f) (D.residual n f) :=
  D.integral_gamma_self_of_plateau hL G _ _ (D.residual_bounded n f hf)
    (D.residualPlateau_bounded n f) ((D.residualPlateau_unit n f).mono fun _ hx => hx.2)
    (D.residualPlateau_mul_residual n f)

/--
Conditional on BH locality, every bounded domain element satisfies the diagonal energy identity.
Proving BH 1991, ch. I, I.6.1.1 in this case.
-/
theorem integral_gamma_self_bounded (hL : D.Local) (G : D.CarreDuChamp)
    (f : D.toCapacity.Space) (hf : f ∈ D.toCapacity.bddSpace) :
    ∫ x, G.Γ f f x ∂m = 2 * D.toCapacity.ener f f := by
  have ht := (D.tendsto_residual f).prodMk_nhds (D.tendsto_residual f)
  have hg := continuous_integral.tendsto (G.Γ f f) |>.comp
    ((G.Γ.continuous₂.tendsto (f, f)).comp ht)
  have he := ((D.toCapacity.ener.continuous₂.tendsto (f, f)).comp ht).const_mul 2
  exact tendsto_nhds_unique hg (he.congr fun n => (D.integral_gamma_residual hL G f hf n).symm)

/-- Conditional on BH locality, the integral of diagonal Gamma equals twice the energy on an
arbitrary measure. BH 1991, ch. I, I.6.1.1. -/
theorem integral_gamma_self (hL : D.Local) (G : D.CarreDuChamp)
    (f : D.toCapacity.Space) :
    ∫ x, G.Γ f f x ∂m = 2 * D.toCapacity.ener f f := by
  have hc : IsClosed {v : D.toCapacity.Space |
      ∫ x, G.Γ v v x ∂m = 2 * D.toCapacity.ener v v} :=
    isClosed_eq (continuous_integral.comp (G.Γ.continuous.clm_apply continuous_id))
      (continuous_const.mul (D.toCapacity.ener.continuous.clm_apply continuous_id))
  exact hc.closure_subset_iff.mpr (D.integral_gamma_self_bounded hL G)
    (D.toCapacity.dense_bddSpace f)

/-- Conditional on BH locality, the integral of Gamma(f,g) equals twice the bilinear energy on
the capacity adapter. BH 1991, ch. I, I.6.1.1, polarized. -/
theorem integral_gamma (hL : D.Local) (G : D.CarreDuChamp)
    (f g : D.toCapacity.Space) :
    ∫ x, G.Γ f g x ∂m = 2 * D.toCapacity.ener f g := by
  have h := D.integral_gamma_self hL G (f + g)
  have hff := D.integral_gamma_self hL G f
  have hgg := D.integral_gamma_self hL G g
  have he : G.Γ (f + g) (f + g) = (G.Γ f f + G.Γ f g) + (G.Γ f g + G.Γ g g) := by
    simp only [map_add, add_apply, G.symm g f]
  have hi : (∫ x, G.Γ (f + g) (f + g) x ∂m) =
      (∫ x, G.Γ f f x ∂m) + (∫ x, G.Γ f g x ∂m) +
        ((∫ x, G.Γ f g x ∂m) + (∫ x, G.Γ g g x ∂m)) := by
    rw [he]
    have hadd (a b : Lp ℝ 1 m) :
        (∫ x, (a + b) x ∂m) = (∫ x, a x ∂m) + ∫ x, b x ∂m := by
      calc
        _ = ∫ x, a x + b x ∂m := integral_congr_ae (Lp.coeFn_add a b)
        _ = _ := integral_add (L1.integrable_coeFn a) (L1.integrable_coeFn b)
    rw [hadd, hadd, hadd]
  have hsym : D.toCapacity.ener g f = D.toCapacity.ener f g := D.toCapacity.ener_symm _ _
  rw [hi] at h
  simp only [map_add, add_apply, hsym] at h
  linarith

/--
Conditional on BH locality, the original bilinear energy equals one half of the integral of
Gamma on the original BH domain. BH 1991, ch. I, I.6.1.1; EID context: ch. V, p. 185, Notes p. 302;
EBM §4.2 uses gamma = Gamma/2.
-/
theorem energy_eq_integral (hL : D.Local) (G : D.CarreDuChamp)
    (f g : D.form.dom) :
    D.form.E f g = (1 / 2 : ℝ) *
      ∫ x, G.Γ (D.form.formToDomain.symm f)
        (D.form.formToDomain.symm g) x ∂m := by
  have h := D.integral_gamma hL G (D.form.formToDomain.symm f) (D.form.formToDomain.symm g)
  rw [D.toCapacity.ener_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply] at h
  linarith

end DprBridge.BH1991.DirichletForm

/-!
Subsequent results: the centered chain rule and actual normal currents with their Dirac boundary are
proved in `DprBridge.BH1991ChainCurrents`; the L1 generator core in `DprBridge.BH1991ResolventCore`;
finite reference, RN transport, kernel positivity, countable certificates and the unconditional
printed BH EID conjecture in `DprBridge.BH1991PrintedProof`.
-/

#print axioms DprBridge.BH1991.DirichletForm.gamma_sum_smul
#print axioms DprBridge.BH1991.DirichletForm.coe_gamma_sum_smul
#print axioms DprBridge.BH1991.DirichletForm.gammaMatrix_posSemidef
#print axioms DprBridge.BH1991.DirichletForm.gammaMatrix_det_nonneg
#print axioms DprBridge.BH1991.DirichletForm.gammaMatrix_integrable
#print axioms DprBridge.BH1991.DirichletForm.local_toCapacity
#print axioms DprBridge.BH1991.DirichletForm.gamma_eq_zero_of_tests
#print axioms DprBridge.BH1991.DirichletForm.gamma_eq_zero_of_mul_bounded
#print axioms DprBridge.BH1991.DirichletForm.gamma_eq_zero_of_mul
#print axioms DprBridge.BH1991.DirichletForm.bounded_memLp_top
#print axioms DprBridge.BH1991.DirichletForm.mul_gamma_eq_zero_bounded
#print axioms DprBridge.BH1991.DirichletForm.mul_truncS_eq_zero
#print axioms DprBridge.BH1991.DirichletForm.tendsto_boundedMul
#print axioms DprBridge.BH1991.DirichletForm.mul_gamma_eq_zero
#print axioms DprBridge.BH1991.DirichletForm.integral_gamma_self_le
#print axioms DprBridge.BH1991.DirichletForm.integral_gamma_self_of_plateau
#print axioms DprBridge.BH1991.DirichletForm.softThreshold
#print axioms DprBridge.BH1991.DirichletForm.softThreshold_zero
#print axioms DprBridge.BH1991.DirichletForm.lipschitzWith_softThreshold
#print axioms DprBridge.BH1991.DirichletForm.abs_softThreshold_le
#print axioms DprBridge.BH1991.DirichletForm.tendsto_softThreshold
#print axioms DprBridge.BH1991.DirichletForm.residual
#print axioms DprBridge.BH1991.DirichletForm.coe_residual
#print axioms DprBridge.BH1991.DirichletForm.residual_bounded
#print axioms DprBridge.BH1991.DirichletForm.energy_residual_le
#print axioms DprBridge.BH1991.DirichletForm.tendsto_residual
#print axioms DprBridge.BH1991.DirichletForm.residualPlateau
#print axioms DprBridge.BH1991.DirichletForm.coe_residualPlateau
#print axioms DprBridge.BH1991.DirichletForm.residualPlateau_unit
#print axioms DprBridge.BH1991.DirichletForm.residualPlateau_bounded
#print axioms DprBridge.BH1991.DirichletForm.unitF_mul_softThreshold
#print axioms DprBridge.BH1991.DirichletForm.residualPlateau_mul_residual
#print axioms DprBridge.BH1991.DirichletForm.integral_gamma_residual
#print axioms DprBridge.BH1991.DirichletForm.integral_gamma_self_bounded
#print axioms DprBridge.BH1991.DirichletForm.integral_gamma_self
#print axioms DprBridge.BH1991.DirichletForm.integral_gamma
#print axioms DprBridge.BH1991.DirichletForm.energy_eq_integral

#check @DprBridge.BH1991.DirichletForm.gammaMatrix_posSemidef
#check @DprBridge.BH1991.DirichletForm.gamma_eq_zero_of_mul
#check @DprBridge.BH1991.DirichletForm.mul_gamma_eq_zero
#check @DprBridge.BH1991.DirichletForm.energy_eq_integral
