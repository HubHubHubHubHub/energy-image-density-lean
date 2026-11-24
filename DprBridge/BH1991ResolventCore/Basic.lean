import DprBridge.BH1991LevelCancellation
import DprBridge.BH1991ChainRules.Basic
import DprBridge.BH1991GammaLocality.Basic
import DprBridge.BH1991NormalContractions.Basic
import DprBridge.BH1991Printed.Basic

/-!
# Chain coefficient closure and the integrable-generator core

This file contains the results of the development of `DprBridge.BH1991ResolventCore` that the main
statements of the library (the head theorems listed in the README of the repository) use.
`DprBridge.BH1991ResolventCore` imports it and continues the development.

## Main statements

* `BH1991.DirichletForm.l1GeneratorCore`: Every domain element on the original arbitrary measure is
  approximated in the form norm by generator pairs whose generator values belong to L¹.
* `BH1991.DirichletForm.chain_coefficients_closed`: Closure under bounded, almost everywhere
  convergent chain coefficients.
* `BH1991.DirichletForm.centered_translated_product`: Finite centered translated products and their
  full Leibniz identity.

## References

References: Bouleau–Hirsch (1991), ch. I, resolvent and generator; EID in ch. V, p. 185; Notes, p.
302; Eriksson-Bique–Murugan, Section 4.2, Remarks 4.12 and 4.22. Multivariate chains and the
original-measure EID proof are developed in `BH1991ChainCurrents` and `BH1991PrintedProof`.
-/
noncomputable section
open MeasureTheory Filter Topology ErrorCalculus
open scoped NNReal ENNReal ContDiff
universe u

namespace DprBridge.BH1991.DirichletForm
variable {X : Type u} [MeasurableSpace X] {m : Measure X} (D : DirichletForm m)

/-- Two applications of a chain identity give its diagonal quadratic identity. -/
theorem chain_diagonal (G : D.CarreDuChamp) {n : ℕ}
    (f : Fin n → D.toCapacity.Space) (p : D.toCapacity.Space) (a : Fin n → X → ℝ)
    (hγ : ∀ v, ⇑(G.Γ p v) =ᵐ[m] fun x => ∑ i, a i x * G.Γ (f i) v x) :
    ⇑(G.Γ p p) =ᵐ[m] fun x => ∑ i, ∑ j, a i x * a j x * G.Γ (f j) (f i) x := by
  filter_upwards [hγ p, ae_all_iff.2 fun i => hγ (f i)] with x h1 h2
  rw [h1]
  apply Finset.sum_congr rfl
  intro i _
  rw [G.symm (f i) p, h2 i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The diagonal is dominated by an integrable sum of the fixed Gamma entries. -/
theorem chain_diagonal_bound (G : D.CarreDuChamp) {n : ℕ}
    (f : Fin n → D.toCapacity.Space) (p : D.toCapacity.Space) (a : Fin n → X → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hγ : ∀ v, ⇑(G.Γ p v) =ᵐ[m] fun x => ∑ i, a i x * G.Γ (f i) v x)
    (ha : ∀ i, ∀ᵐ x ∂m, |a i x| ≤ B) :
    ∀ᵐ x ∂m, |G.Γ p p x| ≤ B ^ 2 * ∑ i, ∑ j, |G.Γ (f j) (f i) x| := by
  filter_upwards [D.chain_diagonal G f p a hγ, ae_all_iff.2 ha] with x hx hax
  rw [hx, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [pow_two] using mul_le_mul (hax i) (hax j) (abs_nonneg _) hB)
    (abs_nonneg _)

/--
Weak identification of Gamma from dominated pointwise limits, on an arbitrary measure. The energy
bound gives domain membership, not strong form convergence.
-/
theorem exists_gamma_limit (G : D.CarreDuChamp)
    {p : ℕ → D.toCapacity.Space} {w : Lp ℝ 2 m} {C : ℝ}
    (hT : Tendsto (fun k => D.toCapacity.toLp (p k)) atTop (𝓝 w))
    (hE : ∀ k, D.toCapacity.ener (p k) (p k) ≤ C)
    (g h : D.toCapacity.Space → X → ℝ) (hh : ∀ v, Integrable (h v) m)
    (hb : ∀ v k, ∀ᵐ x ∂m, |G.Γ (p k) v x| ≤ h v x)
    (ht : ∀ v, ∀ᵐ x ∂m, Tendsto (fun k => G.Γ (p k) v x) atTop (𝓝 (g v x))) :
    ∃ q : D.toCapacity.Space, D.toCapacity.toLp q = w ∧
      ∀ v, ⇑(G.Γ q v) =ᵐ[m] g v := by
  have hE' : ∀ k, D.form.E (D.form.formToDomain (p k)) (D.form.formToDomain (p k)) ≤ C := by
    simpa only [D.toCapacity.ener_apply] using hE
  obtain ⟨hw, _⟩ := D.closed.mem_dom_of_tendsto_of_energy_le hT hE'
  let q : D.toCapacity.Space := D.form.formToDomain.symm ⟨w, hw⟩
  refine ⟨q, rfl, fun v => ?_⟩
  have hm := aestronglyMeasurable_of_tendsto_ae atTop
    (fun k => Lp.aestronglyMeasurable (G.Γ (p k) v)) (ht v)
  have hgb : ∀ᵐ x ∂m, ‖g v x‖ ≤ h v x := by
    filter_upwards [ae_all_iff.2 (hb v), ht v] with x h1 h2
    exact le_of_tendsto' h2.norm fun k => by simpa only [Real.norm_eq_abs] using h1 k
  have hi : Integrable (g v) m := Integrable.mono' (hh v) hm hgb
  apply D.toCapacity.ae_eq_of_integral_mul_eq D.denseRange_toCapacity (L1.integrable_coeFn _) hi
  intro z hz
  have h1 := D.tendsto_integral_mul_gamma_of_energy_bound G hE
    (q := q) hT hz v
  obtain ⟨Cz, hCz⟩ := hz
  have h2 : Tendsto (fun k => ∫ x, D.toCapacity.toLp z x * G.Γ (p k) v x ∂m) atTop
      (𝓝 (∫ x, D.toCapacity.toLp z x * g v x ∂m)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => Cz * h v x)
      (fun k => (Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _))
      ((hh v).const_mul _) (fun k => ?_) ?_
    · filter_upwards [hCz, hb v k] with x h1 h2
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    · filter_upwards [ht v] with x hx
      exact hx.const_mul _
  exact tendsto_nhds_unique h1 h2

/--
Closure under bounded, almost everywhere convergent chain coefficients. Coordinate bounds are
equivalent to a finite-dimensional uniform vector bound. No measurability assumption on the
coefficients is needed: Gamma itself is measurable. The conclusion includes strong convergence in
the form norm.
-/
theorem chain_coefficients_closed (hL : D.Local) (G : D.CarreDuChamp) {n : ℕ}
    (f : Fin n → D.toCapacity.Space) (p : ℕ → D.toCapacity.Space) (w : Lp ℝ 2 m)
    (a : ℕ → Fin n → X → ℝ) (d : Fin n → X → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hT : Tendsto (fun k => D.toCapacity.toLp (p k)) atTop (𝓝 w))
    (ha : ∀ k i, ∀ᵐ x ∂m, |a k i x| ≤ B)
    (hd : ∀ i, ∀ᵐ x ∂m, Tendsto (fun k => a k i x) atTop (𝓝 (d i x)))
    (hγ : ∀ k v, ⇑(G.Γ (p k) v) =ᵐ[m] fun x => ∑ i, a k i x * G.Γ (f i) v x) :
    ∃ q : D.toCapacity.Space, D.toCapacity.toLp q = w ∧ Tendsto p atTop (𝓝 q) ∧
      ∀ v, ⇑(G.Γ q v) =ᵐ[m] fun x => ∑ i, d i x * G.Γ (f i) v x := by
  let H : X → ℝ := fun x => ∑ i, ∑ j, |G.Γ (f j) (f i) x|
  have hHi : Integrable H m := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => (L1.integrable_coeFn _).abs
  have hbd := fun k => D.chain_diagonal_bound G f (p k) (a k) hB (hγ k) (ha k)
  have hE : ∀ k, D.toCapacity.ener (p k) (p k) ≤ (1 / 2 : ℝ) * ∫ x, B ^ 2 * H x ∂m := by
    intro k
    have hi := integral_mono_ae (L1.integrable_coeFn (G.Γ (p k) (p k)))
      (hHi.const_mul (B ^ 2)) ((hbd k).mono fun x hx => (le_abs_self _).trans hx)
    rw [D.integral_gamma_self hL G] at hi
    linarith
  obtain ⟨q, hq, hqγ⟩ := D.exists_gamma_limit G hT hE
    (fun v x => ∑ i, d i x * G.Γ (f i) v x)
    (fun v x => ∑ i, B * |G.Γ (f i) v x|)
    (fun v => integrable_finsetSum _ fun i _ => (L1.integrable_coeFn _).abs.const_mul B)
    (fun v k => by
      filter_upwards [hγ k v, ae_all_iff.2 (ha k)] with x h1 h2
      rw [h1]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (h2 i) (abs_nonneg _))
    (fun v => by
      filter_upwards [ae_all_iff.2 fun k => hγ k v, ae_all_iff.2 hd] with x h1 h2
      simp only [h1]
      exact tendsto_finsetSum _ fun i _ => (h2 i).mul_const _)
  have hdb : ∀ i, ∀ᵐ x ∂m, |d i x| ≤ B := by
    intro i
    filter_upwards [ae_all_iff.2 fun k => ha k i, hd i] with x h1 h2
    exact le_of_tendsto' h2.abs h1
  have hsub : ∀ k v, ⇑(G.Γ (p k - q) v) =ᵐ[m]
      fun x => ∑ i, (a k i x - d i x) * G.Γ (f i) v x := by
    intro k v
    simp only [map_sub, sub_apply]
    filter_upwards [Lp.coeFn_sub (G.Γ (p k) v) (G.Γ q v), hγ k v, hqγ v] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (sub_mul _ _ _).symm
  have hsubbd : ∀ k i, ∀ᵐ x ∂m, |a k i x - d i x| ≤ 2 * B := by
    intro k i
    filter_upwards [ha k i, hdb i] with x h1 h2
    exact (abs_sub _ _).trans (by linarith)
  have he0 : Tendsto (fun k => ∫ x, G.Γ (p k - q) (p k - q) x ∂m) atTop (𝓝 0) := by
    have hz : (∫ _ : X, (0 : ℝ) ∂m) = 0 := integral_zero _ _
    rw [← hz]
    apply tendsto_integral_of_dominated_convergence (fun x => (2 * B) ^ 2 * H x)
      (fun k => Lp.aestronglyMeasurable _) (hHi.const_mul _)
    · intro k
      simpa only [Real.norm_eq_abs] using
        D.chain_diagonal_bound G f (p k - q) (fun i x => a k i x - d i x)
          (by positivity) (hsub k) (hsubbd k)
    · filter_upwards [ae_all_iff.2 fun k => D.chain_diagonal G f (p k - q)
        (fun i x => a k i x - d i x) (hsub k), ae_all_iff.2 hd] with x h1 h2
      simp only [h1]
      have ht := tendsto_finsetSum Finset.univ fun i _ =>
        tendsto_finsetSum Finset.univ fun j _ =>
          (((h2 i).sub_const (d i x)).mul ((h2 j).sub_const (d j x))).mul_const
            (G.Γ (f j) (f i) x)
      simpa only [sub_self, zero_mul, Finset.sum_const_zero] using ht
  have he : Tendsto (fun k => D.toCapacity.ener (p k - q) (p k - q)) atTop (𝓝 0) := by
    have hh := he0.const_mul (1 / 2 : ℝ)
    simp only [D.integral_gamma_self hL G, mul_zero] at hh
    convert hh using 1
    ext k
    ring
  have hl : Tendsto (fun k => D.toCapacity.toLp (p k - q)) atTop (𝓝 0) := by
    simpa only [map_sub, hq, sub_self] using hT.sub_const w
  have hn : Tendsto (fun k => ‖p k - q‖ ^ 2) atTop (𝓝 0) := by
    have hh := (hl.norm.pow 2).add he
    norm_num only [norm_zero, zero_pow, zero_add] at hh
    convert hh using 1
    ext k
    rw [D.toCapacity.ener_apply]
    exact D.form.formSpace_norm_sq (p k - q)
  have hs : Tendsto p atTop (𝓝 q) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hn
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh
  exact ⟨q, hq, hs, hqγ⟩

/--
The centered product of two translated bounded factors has a bounded domain representative and the
stated Leibniz identity.
-/
theorem centered_translated_mul (hL : D.Local) (G : D.CarreDuChamp)
    (u v : D.toCapacity.Space) (hu : u ∈ D.toCapacity.bddSpace)
    (hv : v ∈ D.toCapacity.bddSpace) (a b : ℝ) :
    ∃ w : D.toCapacity.Space, w ∈ D.toCapacity.bddSpace ∧
      (⇑(D.toCapacity.toLp w) =ᵐ[m] fun x =>
        (D.toCapacity.toLp u x + a) * (D.toCapacity.toLp v x + b) - a * b) ∧
      ∀ g, ⇑(G.Γ w g) =ᵐ[m] fun x =>
        (D.toCapacity.toLp u x + a) * G.Γ v g x +
        (D.toCapacity.toLp v x + b) * G.Γ u g x := by
  let p := D.toCapacity.mulS u v
  have hp := D.toCapacity.coeFn_toLp_mulS hu hv
  refine ⟨p + b • u + a • v,
    D.toCapacity.bddSpace.add_mem
      (D.toCapacity.bddSpace.add_mem (D.toCapacity.mulS_mem hu hv)
        (D.toCapacity.bddSpace.smul_mem b hu))
      (D.toCapacity.bddSpace.smul_mem a hv), ?_, fun g => ?_⟩
  · simp only [map_add, map_smul]
    filter_upwards [hp,
      Lp.coeFn_add (D.toCapacity.toLp p + b • D.toCapacity.toLp u) (a • D.toCapacity.toLp v),
      Lp.coeFn_add (D.toCapacity.toLp p) (b • D.toCapacity.toLp u),
      Lp.coeFn_smul b (D.toCapacity.toLp u), Lp.coeFn_smul a (D.toCapacity.toLp v)]
      with x hp h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, hp]
    ring
  · have hγ := D.gamma_bounded_product hL G u v p g hu hv hp
    simp only [map_add, map_smul, add_apply, smul_apply]
    filter_upwards [hγ,
      Lp.coeFn_add (G.Γ p g + b • G.Γ u g) (a • G.Γ v g),
      Lp.coeFn_add (G.Γ p g) (b • G.Γ u g),
      Lp.coeFn_smul b (G.Γ u g), Lp.coeFn_smul a (G.Γ v g)] with x hg h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, hg]
    ring

/--
Finite centered translated products and their full Leibniz identity. The empty product is
represented by zero; no constant domain element is used.
-/
theorem centered_translated_product (hL : D.Local) (G : D.CarreDuChamp)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → D.toCapacity.Space)
    (hu : ∀ i ∈ s, u i ∈ D.toCapacity.bddSpace) (a : ι → ℝ) :
    ∃ w : D.toCapacity.Space, w ∈ D.toCapacity.bddSpace ∧
      (⇑(D.toCapacity.toLp w) =ᵐ[m] fun x =>
        (∏ i ∈ s, (D.toCapacity.toLp (u i) x + a i)) - ∏ i ∈ s, a i) ∧
      ∀ g, ⇑(G.Γ w g) =ᵐ[m] fun x =>
        ∑ i ∈ s, (∏ j ∈ s.erase i, (D.toCapacity.toLp (u j) x + a j)) * G.Γ (u i) g x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, D.toCapacity.bddSpace.zero_mem, ?_, fun g => ?_⟩
    · simp only [map_zero, Finset.prod_empty, sub_self]
      filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx
      exact hx
    · simp only [map_zero, zero_apply, Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero ℝ 1 m] with x hx
      exact hx
  | @insert i s hi ih =>
    obtain ⟨v, hv, hvrep, hvγ⟩ := ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))
    obtain ⟨w, hw, hwrep, hwγ⟩ := D.centered_translated_mul hL G (u i) v
      (hu i (Finset.mem_insert_self _ _)) hv (a i) (∏ j ∈ s, a j)
    refine ⟨w, hw, ?_, fun g => ?_⟩
    · filter_upwards [hwrep, hvrep] with x h1 h2
      rw [h1, h2, sub_add_cancel, Finset.prod_insert hi, Finset.prod_insert hi]
    · filter_upwards [hwγ g, hvrep, hvγ g] with x h1 h2 h3
      rw [h1, h2, sub_add_cancel, h3, Finset.sum_insert hi, Finset.erase_insert hi,
        Finset.mul_sum]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := ne_of_mem_of_not_mem hj hi
      rw [Finset.erase_insert_of_ne hji.symm,
        Finset.prod_insert ((fun h => hi (Finset.mem_of_mem_erase h)))]
      ring

/--
The absolute value of the scaled resolvent is almost everywhere bounded by the scaled resolvent of
the absolute value.
-/
theorem scaled_resolvent_abs_domination (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 m) :
    ∀ᵐ x ∂m, |(β • D.form.resolvent D.closed β hβ f) x| ≤
      (β • D.form.resolvent D.closed β hβ |f|) x := by
  have h₁ := D.scaled_resolvent_mono β hβ f |f| (by
    filter_upwards [Lp.coeFn_abs f] with x hx
    rw [hx]; exact le_abs_self _)
  have h₂ := D.scaled_resolvent_mono β hβ (-f) |f| (by
    filter_upwards [Lp.coeFn_abs f, Lp.coeFn_neg f] with x hx hy
    rw [hx, hy, Pi.neg_apply]; exact neg_le_abs _)
  simp only [map_neg, smul_neg] at h₂
  filter_upwards [h₁, h₂, Lp.coeFn_neg (β • D.form.resolvent D.closed β hβ f)]
    with x h1 h2 h3
  rw [h3, Pi.neg_apply] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/--
L1 contractivity of the scaled resolvent on an arbitrary measure. The positive case uses finite
level sets of its own L2 output, not sigma-finiteness.
-/
theorem scaled_resolvent_integrable (β : ℝ) (hβ : 0 < β)
    (f : Lp ℝ 2 m) (hf : Integrable f m) :
    Integrable (β • D.form.resolvent D.closed β hβ f) m ∧
      (∫ x, |(β • D.form.resolvent D.closed β hβ f) x| ∂m) ≤ ∫ x, |f x| ∂m := by
  have hfi : Integrable (⇑|f|) m := hf.abs.congr (Lp.coeFn_abs f).symm
  have hf0 : ∀ᵐ x ∂m, 0 ≤ |f| x := by
    filter_upwards [Lp.coeFn_abs f] with x hx
    rw [hx]; exact abs_nonneg _
  obtain ⟨hi, hb⟩ := D.toCapacity.integrable_sres β hβ hf0 hfi
  change Integrable (β • D.form.resolvent D.closed β hβ |f|) m at hi
  change (∫ x, (β • D.form.resolvent D.closed β hβ |f|) x ∂m) ≤ ∫ x, |f| x ∂m at hb
  have hd := D.scaled_resolvent_abs_domination β hβ f
  have hri : Integrable (β • D.form.resolvent D.closed β hβ f) m :=
    hi.mono' (Lp.aestronglyMeasurable _) (by simpa only [Real.norm_eq_abs] using hd)
  refine ⟨hri, (integral_mono_ae hri.abs hi hd).trans ?_⟩
  simpa only [integral_congr_ae (Lp.coeFn_abs f)] using hb

/--
For beta at least one, the squared form norm of the scaled resolvent is at most beta times the
squared L2 norm of its input.
-/
theorem scaled_resolvent_form_bound (β : ℝ) (hβ : 0 < β)
    (hβ1 : 1 ≤ β) (f : Lp ℝ 2 m) :
    ‖D.form.formToDomain.symm (D.form.betaResolventDom D.closed β hβ f)‖ ^ 2 ≤
      β * ‖f‖ ^ 2 := by
  let v := D.form.betaResolventDom D.closed β hβ f
  have he := D.form.beta_resolvent_spec D.closed β hβ f v
  have hn := D.form.norm_beta_resolvent_le D.closed β hβ f
  change ‖(v : Lp ℝ 2 m)‖ ≤ ‖f‖ at hn
  change D.form.E v v + β * inner ℝ (v : Lp ℝ 2 m) (v : Lp ℝ 2 m) =
    β * inner ℝ f (v : Lp ℝ 2 m) at he
  rw [real_inner_self_eq_norm_sq] at he
  rw [D.form.formSpace_norm_sq, LinearEquiv.apply_symm_apply]
  have hi := real_inner_le_norm f (v : Lp ℝ 2 m)
  have hb := mul_le_mul_of_nonneg_left hn (norm_nonneg f)
  have hnn := sq_nonneg ‖(v : Lp ℝ 2 m)‖
  nlinarith

/-- Resolvent approximation in the form norm, for every domain element. -/
theorem tendsto_scaled_resolvent_form (f : D.form.dom) :
    Tendsto (fun k : ℕ => D.form.formToDomain.symm
      (D.form.betaResolventDom D.closed ((k : ℝ) + 1) (by positivity) f)) atTop
      (𝓝 (D.form.formToDomain.symm f)) := by
  apply D.closed.tendsto_formSpace_of_energy_le
  · exact D.form.tendsto_beta_resolvent_dom D.closed _ (fun k => by positivity)
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop) f
  · intro k
    have h := D.form.resolvent_minimizes D.closed ((k : ℝ) + 1) (by positivity) f f
    simp only [QuadForm.resolventFunctional, sub_self, norm_zero] at h
    have hn : 0 ≤ ((k : ℝ) + 1) *
        ‖(D.form.betaResolventDom D.closed ((k : ℝ) + 1) (by positivity) f : Lp ℝ 2 m) - f‖ ^ 2 :=
          by positivity
    linarith

/--
Each L2 function has L1 and L2 approximants obtained by removing its small values. The domination
is by (k+1) times its square; no exhaustion of the measure space is used.
-/
theorem exists_integrable_L2_approx (f : Lp ℝ 2 m) :
    ∃ v : ℕ → Lp ℝ 2 m, (∀ k, Integrable (v k) m) ∧ Tendsto v atTop (𝓝 f) := by
  let A : ℕ → Set X := fun k => {x | 1 / ((k : ℝ) + 1) ≤ |f x|}
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    measurableSet_le measurable_const (Lp.stronglyMeasurable f).measurable.abs
  let F : ℕ → X → ℝ := fun k => (A k).indicator f
  have hF : ∀ k, MemLp (F k) 2 m := fun k => (Lp.memLp f).indicator (hAm k)
  have hi : ∀ k, Integrable (F k) m := by
    intro k
    apply ((Lp.memLp f).integrable_sq.const_mul ((k : ℝ) + 1)).mono' (hF k).aestronglyMeasurable
    apply ae_of_all
    intro x
    by_cases hx : x ∈ A k
    · dsimp only [F]
      rw [Set.indicator_of_mem hx, Real.norm_eq_abs]
      have hp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hx' : 1 ≤ |f x| * ((k : ℝ) + 1) := (div_le_iff₀ hp).mp hx
      have hm := mul_le_mul_of_nonneg_left hx' (abs_nonneg (f x))
      nlinarith [sq_abs (f x)]
    · dsimp only [F]
      rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  let v : ℕ → Lp ℝ 2 m := fun k => (hF k).toLp (F k)
  refine ⟨v, fun k => (hi k).congr (hF k).coeFn_toLp.symm, ?_⟩
  have ht := Foundations.tendsto_toLp_dominated m hF (Lp.memLp f) (Lp.memLp f).norm
    (fun k => ae_of_all _ fun x => norm_indicator_le_norm_self _ _)
    (ae_of_all _ fun x => ?_)
  · have hid : (Lp.memLp f).toLp f = f := Lp.ext (Lp.memLp f).coeFn_toLp
    simpa only [hid] using ht
  · by_cases hx : f x = 0
    · have he : ∀ k, F k x = 0 := fun k => by simp [F, Set.indicator, hx]
      simp only [he, hx]
      exact tendsto_const_nhds
    · have hp : 0 < |f x| := abs_pos.mpr hx
      have he := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hp)
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with k hk
      exact (Set.indicator_of_mem (show x ∈ A k from hk.le) f).symm

/-- L1 intersect L2 is dense in L2 even when the measure is not sigma-finite. -/
theorem exists_integrable_L2_near (f : Lp ℝ 2 m) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Lp ℝ 2 m, Integrable v m ∧ ‖v - f‖ < ε := by
  obtain ⟨v, hi, ht⟩ := exists_integrable_L2_approx f
  obtain ⟨k, hk⟩ := ((tendsto_iff_norm_sub_tendsto_zero.mp ht).eventually
    (gt_mem_nhds hε)).exists
  exact ⟨v k, hi k, hk⟩

/--
For beta at least one, the form norm of the scaled resolvent is at most beta times the L2 norm of
its input. This nonsharp bound supports the diagonal argument.
-/
theorem scaled_resolvent_form_norm_le (β : ℝ) (hβ : 0 < β) (hβ1 : 1 ≤ β)
    (f : Lp ℝ 2 m) :
    ‖D.form.formToDomain.symm (D.form.betaResolventDom D.closed β hβ f)‖ ≤ β * ‖f‖ := by
  have h := D.scaled_resolvent_form_bound β hβ hβ1 f
  have hb : β * ‖f‖ ^ 2 ≤ (β * ‖f‖) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right (show β ≤ β ^ 2 by nlinarith) (sq_nonneg ‖f‖)
    nlinarith
  nlinarith [norm_nonneg (D.form.formToDomain.symm (D.form.betaResolventDom D.closed β hβ f)),
    mul_nonneg hβ.le (norm_nonneg f)]

/--
Every domain element on the original arbitrary measure is approximated in the form norm by generator
pairs whose generator values belong to L¹. Sigma-finiteness is not required.

References: Bouleau–Hirsch (1991), ch. I, resolvent and generator; ch. V, p. 185; Notes, p. 302;
Eriksson-Bique–Murugan, Section 4.2, Remarks 4.12 and 4.22. The arbitrary-measure version is
established by the proof here.
-/
theorem l1GeneratorCore : D.L1GeneratorCore := by
  intro f
  let β : ℕ → ℝ := fun k => (k : ℝ) + 1
  have hβ : ∀ k, 0 < β k := fun k => by dsimp [β]; positivity
  have hβ1 : ∀ k, 1 ≤ β k := fun k => by
    dsimp [β]
    exact le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hv : ∀ k, ∃ v : Lp ℝ 2 m, Integrable v m ∧ ‖v - (f : Lp ℝ 2 m)‖ < (β k)⁻¹ ^ 2 :=
    fun k => exists_integrable_L2_near (f : Lp ℝ 2 m) (by positivity)
  choose v hvi hvd using hv
  let g : ℕ → D.form.dom := fun k => D.form.betaResolventDom D.closed (β k) (hβ k) (v k)
  let a : ℕ → Lp ℝ 2 m := fun k => β k • ((g k : Lp ℝ 2 m) - v k)
  have hgi : ∀ k, Integrable (g k : Lp ℝ 2 m) m :=
    fun k => (D.scaled_resolvent_integrable (β k) (hβ k) (v k) (hvi k)).1
  refine ⟨g, a, fun k => ⟨D.isGeneratorPair_scaled_resolvent (β k) (hβ k) (v k), ?_⟩, ?_⟩
  · exact (((hgi k).sub (hvi k)).smul (β k)).congr
      ((Lp.coeFn_smul (β k) ((g k : Lp ℝ 2 m) - v k)).trans
        ((Lp.coeFn_sub (g k : Lp ℝ 2 m) (v k)).mono fun x hx => by
          simp only [Pi.smul_apply, Pi.sub_apply, hx])).symm
  · let q : ℕ → D.form.FormSpace := fun k => D.form.formToDomain.symm
      (D.form.betaResolventDom D.closed (β k) (hβ k) f)
    have hdist : ∀ k, ‖D.form.formToDomain.symm (g k) - q k‖ ≤ (β k)⁻¹ := by
      intro k
      have he : D.form.formToDomain.symm (g k) - q k =
          D.form.formToDomain.symm (D.form.betaResolventDom D.closed (β k) (hβ k)
            (v k - (f : Lp ℝ 2 m))) := by
        apply D.form.formToDomain.injective
        apply Subtype.ext
        simp only [g, q, map_sub, LinearEquiv.apply_symm_apply, QuadForm.coe_betaResolventDom,
          smul_sub, Submodule.coe_sub]
      rw [he]
      calc
        _ ≤ β k * ‖v k - (f : Lp ℝ 2 m)‖ := D.scaled_resolvent_form_norm_le _ (hβ k) (hβ1 k) _
        _ ≤ β k * ((β k)⁻¹ ^ 2) := mul_le_mul_of_nonneg_left (hvd k).le (hβ k).le
        _ = (β k)⁻¹ := by field_simp
    have hzero : Tendsto (fun k => D.form.formToDomain.symm (g k) - q k) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero (fun k => norm_nonneg _) hdist
        (tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
    have hq : Tendsto q atTop (𝓝 (D.form.formToDomain.symm f)) := D.tendsto_scaled_resolvent_form f
    simpa only [sub_add_cancel, zero_add] using hzero.add hq

end DprBridge.BH1991.DirichletForm
