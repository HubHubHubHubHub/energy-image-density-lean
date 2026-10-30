import DprBridge.BH1991Printed
import ErrorCalculus.Dirichlet.ApproximatingForm
import Foundations.Sections.Basic

/-!
# Normal contractions from the BH Markov axiom

## Main results
The printed BH Markov axiom implies normal contractions on the original closed, densely defined
form. The result does not require locality, a constant in the domain or sigma-finiteness. Under
property (R), the adapter provides the unique carré du champ.

References: Bouleau–Hirsch (1991), ch. I, I.3.3.1–2 and I.4.1.2–3; ch. V, p. 185; Notes, p. 302;
Eriksson-Bique–Murugan, arXiv:2510.13659v1, §4.2. The local calculus and normal-current reduction
are developed in the subsequent BH modules.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ErrorCalculus
open scoped NNReal ENNReal
universe u

namespace DprBridge.BH1991.DirichletForm
variable {X : Type u} [MeasurableSpace X] {m : Measure X} (D : DirichletForm m)

/-- Positive upper truncations follow by rescaling the printed Markov axiom. -/
theorem exists_upper_truncation (c : ℝ) (hc : 0 < c) (f : D.form.dom) :
    ∃ g : D.form.dom,
      (⇑(g : Lp ℝ 2 m) =ᵐ[m] fun x => min ((f : Lp ℝ 2 m) x) c) ∧
      D.form.E g g ≤ D.form.E f f := by
  obtain ⟨g, hg, hE⟩ := D.markov (c⁻¹ • f)
  refine ⟨c • g, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul c (g : Lp ℝ 2 m), hg,
      Lp.coeFn_smul c⁻¹ (f : Lp ℝ 2 m)] with x hx hy hz
    change (c • (g : Lp ℝ 2 m)) x = _
    rw [hx]
    change c * (g : Lp ℝ 2 m) x = _
    rw [hy]
    change c * min ((c⁻¹ • (f : Lp ℝ 2 m)) x) 1 = _
    rw [hz]
    change c * min (c⁻¹ * (f : Lp ℝ 2 m) x) 1 = _
    rw [mul_min_of_nonneg _ _ hc.le, mul_one, ← mul_assoc,
      mul_inv_cancel₀ hc.ne', one_mul]
  · rw [D.form.energy_smul_smul]
    have h := mul_le_mul_of_nonneg_left hE (sq_nonneg c)
    rw [D.form.energy_smul_smul] at h
    simpa only [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc.ne', one_pow, one_mul] using h

/-- A nonnegative upper truncation is pointwise dominated by the original modulus. -/
theorem abs_min_le_abs (t c : ℝ) (hc : 0 ≤ c) : |min t c| ≤ |t| := by
  by_cases ht : t ≤ c
  · rw [min_eq_left ht]
  · rw [min_eq_right (le_of_not_ge ht), abs_of_nonneg hc,
      abs_of_nonneg (hc.trans (le_of_not_ge ht))]
    exact le_of_not_ge ht

/-- The zero upper truncation follows from closedness and dominated L² convergence. -/
theorem exists_nonpositive_part (f : D.form.dom) :
    ∃ g : D.form.dom,
      (⇑(g : Lp ℝ 2 m) =ᵐ[m] fun x => min ((f : Lp ℝ 2 m) x) 0) ∧
      D.form.E g g ≤ D.form.E f f := by
  let c : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hc : ∀ n, 0 < c n := fun n => by dsimp [c]; positivity
  choose g hg hE using fun n => D.exists_upper_truncation (c n) (hc n) f
  have hmem : MemLp (fun x => min ((f : Lp ℝ 2 m) x) 0) 2 m :=
    (LipschitzWith.id.min_const 0).comp_memLp (by simp) (Lp.memLp _)
  let w : Lp ℝ 2 m := hmem.toLp _
  have hlim : Tendsto (fun n => (g n : Lp ℝ 2 m)) atTop (𝓝 w) := by
    have h := Foundations.tendsto_toLp_dominated m
      (fun n => Lp.memLp (g n : Lp ℝ 2 m)) hmem (Lp.memLp (f : Lp ℝ 2 m)).norm
      (fun n => ?_) ?_
    · have he : ∀ n, (Lp.memLp (g n : Lp ℝ 2 m)).toLp _ =
          (g n : Lp ℝ 2 m) := fun n => Lp.ext (Lp.memLp _).coeFn_toLp
      simpa only [he] using h
    · filter_upwards [hg n] with x hx
      simpa only [hx, Real.norm_eq_abs] using abs_min_le_abs
        ((f : Lp ℝ 2 m) x) (c n) (hc n).le
    · filter_upwards [ae_all_iff.2 hg] with x hx
      have ht : Tendsto c atTop (𝓝 (0 : ℝ)) := by
        simpa [c, one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat :
            Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
      simpa only [hx] using (tendsto_const_nhds (x := (f : Lp ℝ 2 m) x)).min ht
  obtain ⟨hw, he⟩ := D.closed.mem_dom_of_tendsto_of_energy_le hlim hE
  exact ⟨⟨w, hw⟩, hmem.coeFn_toLp, he⟩

/-- Positive parts are energy contractions, without any constant in the domain. -/
theorem exists_positive_part (f : D.form.dom) :
    ∃ g : D.form.dom,
      (⇑(g : Lp ℝ 2 m) =ᵐ[m] fun x => max ((f : Lp ℝ 2 m) x) 0) ∧
      D.form.E g g ≤ D.form.E f f := by
  obtain ⟨g, hg, he⟩ := D.exists_nonpositive_part (-f)
  refine ⟨-g, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_neg (g : Lp ℝ 2 m), hg,
      Lp.coeFn_neg (f : Lp ℝ 2 m)] with x hx hy hz
    change (-(g : Lp ℝ 2 m)) x = _
    rw [hx]
    change -(g : Lp ℝ 2 m) x = _
    rw [hy]
    change -(min ((-(f : Lp ℝ 2 m)) x) 0) = _
    rw [hz]
    change -min (-((f : Lp ℝ 2 m) x)) 0 = _
    rcases le_total 0 ((f : Lp ℝ 2 m) x) with h | h
    · rw [min_eq_left (neg_nonpos.mpr h), neg_neg, max_eq_left h]
    · rw [min_eq_right (neg_nonneg.mpr h), neg_zero, max_eq_right h]
  · simpa only [map_neg, LinearMap.neg_apply, neg_neg] using he

/-- The usual unit clamp is derived from the raw upper truncation. -/
theorem exists_unit_clamp (f : D.form.dom) :
    ∃ g : D.form.dom,
      (⇑(g : Lp ℝ 2 m) =ᵐ[m] fun x => min (max ((f : Lp ℝ 2 m) x) 0) 1) ∧
      D.form.E g g ≤ D.form.E f f := by
  obtain ⟨p, hp, hEp⟩ := D.exists_positive_part f
  obtain ⟨g, hg, hEg⟩ := D.markov p
  refine ⟨g, ?_, hEg.trans hEp⟩
  filter_upwards [hg, hp] with x hx hy
  rw [hx, hy]

/-- A chosen positive part, used only through its almost-everywhere specification. -/
def positivePart (f : D.form.dom) : D.form.dom :=
  (D.exists_positive_part f).choose

/-- Representative identity for the chosen positive part. -/
theorem coe_positivePart (f : D.form.dom) :
    ⇑(D.positivePart f : Lp ℝ 2 m) =ᵐ[m]
      fun x => max ((f : Lp ℝ 2 m) x) 0 :=
  (D.exists_positive_part f).choose_spec.1

/-- The chosen positive part decreases energy. -/
theorem energy_positivePart_le (f : D.form.dom) :
    D.form.E (D.positivePart f) (D.positivePart f) ≤ D.form.E f f :=
  (D.exists_positive_part f).choose_spec.2

/-- The negative part is the positive part of the opposite. -/
def negativePart (f : D.form.dom) : D.form.dom := D.positivePart (-f)

/-- Representative identity for the chosen negative part. -/
theorem coe_negativePart (f : D.form.dom) :
    ⇑(D.negativePart f : Lp ℝ 2 m) =ᵐ[m]
      fun x => max (-((f : Lp ℝ 2 m) x)) 0 := by
  filter_upwards [D.coe_positivePart (-f), Lp.coeFn_neg (f : Lp ℝ 2 m)] with x hx hy
  exact hx.trans (congrArg (fun t : ℝ => max t 0) hy)

/-- The signed decomposition is an equality in the form domain. -/
theorem positivePart_sub_negativePart (f : D.form.dom) :
    D.positivePart f - D.negativePart f = f := by
  apply QuadForm.dom_ext_ae
  filter_upwards [Lp.coeFn_sub (D.positivePart f : Lp ℝ 2 m)
    (D.negativePart f : Lp ℝ 2 m), D.coe_positivePart f, D.coe_negativePart f] with x hx hp hn
  change ((D.positivePart f : Lp ℝ 2 m) - D.negativePart f) x = _
  rw [hx]
  change (D.positivePart f : Lp ℝ 2 m) x - (D.negativePart f : Lp ℝ 2 m) x = _
  rw [hp, hn]
  rcases le_total 0 ((f : Lp ℝ 2 m) x) with h | h <;>
    simp [h, neg_nonpos.mpr, neg_nonneg.mpr]

/-- A small-parameter quadratic inequality detects the sign of the linear coefficient. -/
theorem nonpos_of_quadratic_bounds {a b : ℝ} (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 < t → 2 * t * a ≤ t ^ 2 * b) : a ≤ 0 := by
  by_contra ha
  have ha : 0 < a := lt_of_not_ge ha
  let t := a / (b + 1)
  have ht : 0 < t := div_pos ha (by linarith)
  have htb : t * (b + 1) = a := by dsimp [t]; field_simp
  have hh := h t ht
  nlinarith [sq_nonneg t]

/-- Disjoint nonnegative domain elements have nonpositive mutual energy. -/
theorem energy_nonpos_of_disjoint (p q : D.form.dom)
    (hp : ∀ᵐ x ∂m, 0 ≤ (p : Lp ℝ 2 m) x)
    (hq : ∀ᵐ x ∂m, 0 ≤ (q : Lp ℝ 2 m) x)
    (hpq : ∀ᵐ x ∂m, (p : Lp ℝ 2 m) x * (q : Lp ℝ 2 m) x = 0) :
    D.form.E p q ≤ 0 := by
  apply nonpos_of_quadratic_bounds (D.form.nonneg q)
  intro t ht
  have hid : D.positivePart (p - t • q) = p := by
    apply QuadForm.dom_ext_ae
    filter_upwards [D.coe_positivePart (p - t • q),
      Lp.coeFn_sub (p : Lp ℝ 2 m) (t • (q : Lp ℝ 2 m)),
      Lp.coeFn_smul t (q : Lp ℝ 2 m), hp, hq, hpq] with x hx hs hm hp hq hpq
    rw [hx]
    change max (((p : Lp ℝ 2 m) - t • (q : Lp ℝ 2 m)) x) 0 = _
    rw [hs]
    change max ((p : Lp ℝ 2 m) x - (t • (q : Lp ℝ 2 m)) x) 0 = _
    rw [hm]
    change max ((p : Lp ℝ 2 m) x - t * (q : Lp ℝ 2 m) x) 0 = _
    rcases mul_eq_zero.mp hpq with h | h
    · rw [h, zero_sub, max_eq_right (neg_nonpos.mpr (mul_nonneg ht.le hq))]
    · rw [h, mul_zero, sub_zero, max_eq_left hp]
  have he := D.energy_positivePart_le (p - t • q)
  rw [hid] at he
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at he
  rw [D.form.symm q p] at he
  nlinarith

/-- The positive and negative parts have nonpositive mutual energy. -/
theorem energy_positive_negative_nonpos (f : D.form.dom) :
    D.form.E (D.positivePart f) (D.negativePart f) ≤ 0 := by
  apply D.energy_nonpos_of_disjoint
  · filter_upwards [D.coe_positivePart f] with x hx
    rw [hx]
    exact le_max_right _ _
  · filter_upwards [D.coe_negativePart f] with x hx
    rw [hx]
    exact le_max_right _ _
  · filter_upwards [D.coe_positivePart f, D.coe_negativePart f] with x hp hn
    rw [hp, hn]
    rcases le_total 0 ((f : Lp ℝ 2 m) x) with h | h
    · rw [max_eq_right (neg_nonpos.mpr h), mul_zero]
    · rw [max_eq_right h, zero_mul]

/-- Absolute value is an energy contraction for the raw BH form. -/
theorem exists_absolute_value (f : D.form.dom) :
    ∃ g : D.form.dom,
      (⇑(g : Lp ℝ 2 m) =ᵐ[m] fun x => |(f : Lp ℝ 2 m) x|) ∧
      D.form.E g g ≤ D.form.E f f := by
  refine ⟨D.positivePart f + D.negativePart f, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add (D.positivePart f : Lp ℝ 2 m)
      (D.negativePart f : Lp ℝ 2 m), D.coe_positivePart f, D.coe_negativePart f] with x hx hp hn
    change ((D.positivePart f : Lp ℝ 2 m) + D.negativePart f) x = _
    rw [hx]
    change (D.positivePart f : Lp ℝ 2 m) x + (D.negativePart f : Lp ℝ 2 m) x = _
    rw [hp, hn]
    rcases le_total 0 ((f : Lp ℝ 2 m) x) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero, abs_of_nonneg h]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_add, abs_of_nonpos h]
  · have he := D.energy_positive_negative_nonpos f
    have hid := congrArg (fun v : D.form.dom => D.form.E v v)
      (D.positivePart_sub_negativePart f)
    simp only [map_sub, LinearMap.sub_apply] at hid
    rw [D.form.symm (D.negativePart f) (D.positivePart f)] at hid
    rw [D.form.energy_add_add]
    linarith

/--
Conditional on an energy-decreasing composition witness, a 1-Lipschitz map fixing the datum fixes
its scaled resolvent.
-/
theorem scaled_resolvent_fixed (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 m)
    {F : ℝ → ℝ} (hF : LipschitzWith 1 F)
    (hf : ∀ᵐ x ∂m, F (f x) = f x) (w : D.form.dom)
    (hw : ⇑(w : Lp ℝ 2 m) =ᵐ[m] fun x =>
      F ((D.form.betaResolventDom D.closed β hβ f : Lp ℝ 2 m) x))
    (hE : D.form.E w w ≤ D.form.E (D.form.betaResolventDom D.closed β hβ f)
      (D.form.betaResolventDom D.closed β hβ f)) :
    w = D.form.betaResolventDom D.closed β hβ f := by
  let v := D.form.betaResolventDom D.closed β hβ f
  have hn : ‖(w : Lp ℝ 2 m) - f‖ ≤ ‖(v : Lp ℝ 2 m) - f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hw, hf, Lp.coeFn_sub (w : Lp ℝ 2 m) f,
      Lp.coeFn_sub (v : Lp ℝ 2 m) f] with x hw hf hs ht
    have h := hF.dist_le_mul ((v : Lp ℝ 2 m) x) (f x)
    simpa only [hs, ht, Pi.sub_apply, hw, hf, NNReal.coe_one, one_mul,
      Real.dist_eq, Real.norm_eq_abs] using h
  apply D.form.eq_resolvent_of_le D.closed β hβ f w
  exact add_le_add hE
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hβ.le)

/-- The scaled resolvent preserves nonnegativity on an arbitrary measure space. -/
theorem scaled_resolvent_nonneg (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 m)
    (hf : ∀ᵐ x ∂m, 0 ≤ f x) :
    ∀ᵐ x ∂m, 0 ≤ (β • D.form.resolvent D.closed β hβ f) x := by
  let v := D.form.betaResolventDom D.closed β hβ f
  have he := D.scaled_resolvent_fixed β hβ f (LipschitzWith.id.max_const 0)
    (hf.mono fun _ h => max_eq_left h) (D.positivePart v)
    (D.coe_positivePart v) (D.energy_positivePart_le v)
  have h := D.coe_positivePart v
  rw [he] at h
  filter_upwards [h] with x hx
  change 0 ≤ (v : Lp ℝ 2 m) x
  rw [hx]
  exact le_max_right _ _

/-- Positive constant upper bounds are preserved without treating constants as L² elements. -/
theorem scaled_resolvent_le_const (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 m)
    (c : ℝ) (hc : 0 < c) (hf : ∀ᵐ x ∂m, f x ≤ c) :
    ∀ᵐ x ∂m, (β • D.form.resolvent D.closed β hβ f) x ≤ c := by
  let v := D.form.betaResolventDom D.closed β hβ f
  obtain ⟨w, hw, hE⟩ := D.exists_upper_truncation c hc v
  have he := D.scaled_resolvent_fixed β hβ f (LipschitzWith.id.min_const c)
    (hf.mono fun _ h => min_eq_left h) w hw hE
  rw [he] at hw
  filter_upwards [hw] with x hx
  change (v : Lp ℝ 2 m) x ≤ c
  rw [hx]
  exact min_le_right _ _

/-- The scaled resolvent is sub-Markovian for the printed BH structure. -/
theorem scaled_resolvent_submarkov (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 m)
    (hf : ∀ᵐ x ∂m, 0 ≤ f x ∧ f x ≤ 1) :
    ∀ᵐ x ∂m, 0 ≤ (β • D.form.resolvent D.closed β hβ f) x ∧
      (β • D.form.resolvent D.closed β hβ f) x ≤ 1 :=
  (D.scaled_resolvent_nonneg β hβ f (hf.mono fun _ h => h.1)).and
    (D.scaled_resolvent_le_const β hβ f 1 zero_lt_one (hf.mono fun _ h => h.2))

/-- Positivity and linearity imply order preservation of the scaled resolvent. -/
theorem scaled_resolvent_mono (β : ℝ) (hβ : 0 < β) (f g : Lp ℝ 2 m)
    (hfg : ∀ᵐ x ∂m, f x ≤ g x) :
    ∀ᵐ x ∂m, (β • D.form.resolvent D.closed β hβ f) x ≤
      (β • D.form.resolvent D.closed β hβ g) x := by
  have hnon : ∀ᵐ x ∂m, 0 ≤ (g - f) x := by
    filter_upwards [hfg, Lp.coeFn_sub g f] with x hx hs
    simpa only [hs, Pi.sub_apply, sub_nonneg] using hx
  have h := D.scaled_resolvent_nonneg β hβ (g - f) hnon
  rw [map_sub, smul_sub] at h
  filter_upwards [h, Lp.coeFn_sub (β • D.form.resolvent D.closed β hβ g)
    (β • D.form.resolvent D.closed β hβ f)] with x hx hs
  rw [hs] at hx
  exact sub_nonneg.mp hx

/-- The scaled resolvent preserves any positive uniform absolute bound. -/
theorem scaled_resolvent_abs_le (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 m)
    (c : ℝ) (hc : 0 < c) (hf : ∀ᵐ x ∂m, |f x| ≤ c) :
    ∀ᵐ x ∂m, |(β • D.form.resolvent D.closed β hβ f) x| ≤ c := by
  have hu := D.scaled_resolvent_le_const β hβ f c hc
    (hf.mono fun _ h => (le_abs_self _).trans h)
  have hneg : ∀ᵐ x ∂m, (-f) x ≤ c := by
    filter_upwards [hf, Lp.coeFn_neg f] with x hx hn
    rw [hn]
    exact (neg_le_abs _).trans hx
  have hl := D.scaled_resolvent_le_const β hβ (-f) c hc hneg
  rw [map_neg, smul_neg] at hl
  filter_upwards [hu, hl, Lp.coeFn_neg (β • D.form.resolvent D.closed β hβ f)] with x hu hl hn
  rw [hn] at hl
  change -(β • D.form.resolvent D.closed β hβ f) x ≤ c at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- The raw resolvent supplies the exact weak generator pair, with the negative sign. -/
theorem isGeneratorPair_resolvent (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 m) :
    D.IsGeneratorPair (D.form.resolventDom D.closed β hβ f)
      (β • D.form.resolvent D.closed β hβ f - f) := by
  intro v
  have he := D.form.resolvent_spec D.closed β hβ f v
  rw [D.form.symm] at he
  have hi : (∫ x, (v : Lp ℝ 2 m) x *
      (β • D.form.resolvent D.closed β hβ f - f) x ∂m) =
      inner ℝ (β • D.form.resolvent D.closed β hβ f - f) (v : Lp ℝ 2 m) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact ae_of_all _ fun _ => by simp
  rw [hi, inner_sub_left, real_inner_smul_left]
  linarith

/-- Multiplying a generator pair by a scalar preserves the weak generator identity. -/
theorem IsGeneratorPair.smul {g : D.form.dom} {a : Lp ℝ 2 m}
    (h : D.IsGeneratorPair g a) (c : ℝ) : D.IsGeneratorPair (c • g) (c • a) := by
  intro v
  rw [map_smul, smul_eq_mul, h v]
  have hi : (∫ x, (v : Lp ℝ 2 m) x * (c • a) x ∂m) =
      c * ∫ x, (v : Lp ℝ 2 m) x * a x ∂m := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c a] with x hx
    rw [hx]
    change (v : Lp ℝ 2 m) x * (c * a x) = _
    ring
  rw [hi]
  ring

/-- The scaled resolvent has generator value β(βRβf-f). -/
theorem isGeneratorPair_scaled_resolvent (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 m) :
    D.IsGeneratorPair (D.form.betaResolventDom D.closed β hβ f)
      (β • (β • D.form.resolvent D.closed β hβ f - f)) :=
  IsGeneratorPair.smul D (D.isGeneratorPair_resolvent β hβ f) β

/-- A symmetric finite quadratic form splits into edge and killing energies. -/
theorem finite_energy_identity {ι : Type*} [Fintype ι] (a mass : ι → ℝ)
    (w : ι → ι → ℝ) (hw : ∀ i j, w i j = w j i) :
    (∑ i, mass i * a i ^ 2) - ∑ i, ∑ j, w i j * a i * a j =
      (1 / 2 : ℝ) * (∑ i, ∑ j, w i j * (a i - a j) ^ 2) +
        ∑ i, (mass i - ∑ j, w i j) * a i ^ 2 := by
  have hs : (∑ i, ∑ j, w i j * a j ^ 2) = ∑ i, ∑ j, w i j * a i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hw j i]
  have he : (∑ i, ∑ j, w i j * (a i - a j) ^ 2) =
      (∑ i, ∑ j, w i j * a i ^ 2) + (∑ i, ∑ j, w i j * a j ^ 2) -
        2 * (∑ i, ∑ j, w i j * a i * a j) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, hs]
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  ring

/-- Normal contractions decrease every finite edge-and-killing energy. -/
theorem finite_energy_contraction {ι : Type*} [Fintype ι] (a mass : ι → ℝ)
    (w : ι → ι → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (hm : ∀ i, ∑ j, w i j ≤ mass i)
    {F : ℝ → ℝ} (hF : LipschitzWith 1 F) (h0 : F 0 = 0) :
    (∑ i, mass i * (F (a i)) ^ 2) - ∑ i, ∑ j, w i j * F (a i) * F (a j) ≤
      (∑ i, mass i * a i ^ 2) - ∑ i, ∑ j, w i j * a i * a j := by
  rw [finite_energy_identity (fun i => F (a i)) mass w hw,
    finite_energy_identity a mass w hw]
  have hdist (x y : ℝ) : (F x - F y)^2 ≤ (x-y)^2 := by
    have h := hF.dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
    simpa only [sq_abs] using hsq
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hdist _ _) (hw0 i j)
  · apply Finset.sum_le_sum
    intro i _
    have hsq : (F (a i))^2 ≤ (a i)^2 := by simpa [h0] using hdist (a i) 0
    exact mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr (hm i))

/-- Finite sums of L² representatives agree almost everywhere with pointwise sums. -/
theorem coe_fintype_sum {ι : Type*} [Fintype ι] (v : ι → Lp ℝ 2 m) :
    ⇑(∑ i, v i : Lp ℝ 2 m) =ᵐ[m] fun x => ∑ i, v i x := by
  classical
  have h (s : Finset ι) : ⇑(∑ i ∈ s, v i : Lp ℝ 2 m) =ᵐ[m] fun x => ∑ i ∈ s, v i x := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx
      exact hx
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (v i) (∑ j ∈ s, v j), ih] with x hx hy
      simp only [hx, Pi.add_apply, hy]
  exact h Finset.univ

/-- The scaled resolvent as a continuous linear operator on the original L² space. -/
def scaledResolvent (β : ℝ) (hβ : 0 < β) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  β • D.form.resolvent D.closed β hβ

/-- Normal contractions decrease the resolvent energy of a finite indicator family. -/
theorem finite_indicator_contraction {ι : Type*} [Fintype ι]
    (β : ℝ) (hβ : 0 < β) (e : ι → Lp ℝ 2 m)
    (he : ∀ i, ∀ᵐ x ∂m, e i x = 0 ∨ e i x = 1)
    (hs : ∀ᵐ x ∂m, (∑ i, e i x) ≤ 1)
    (ho : ∀ i j, i ≠ j → inner ℝ (e i) (e j) = 0)
    (a : ι → ℝ) {F : ℝ → ℝ} (hF : LipschitzWith 1 F) (h0 : F 0 = 0) :
    inner ℝ ((∑ i, F (a i) • e i) -
      D.scaledResolvent β hβ (∑ i, F (a i) • e i)) (∑ i, F (a i) • e i) ≤
    inner ℝ ((∑ i, a i • e i) -
      D.scaledResolvent β hβ (∑ i, a i • e i)) (∑ i, a i • e i) := by
  classical
  let T := D.scaledResolvent β hβ
  let mass : ι → ℝ := fun i => inner ℝ (e i) (e i)
  let w : ι → ι → ℝ := fun i j => inner ℝ (T (e i)) (e j)
  have he0 (i) : ∀ᵐ x ∂m, 0 ≤ e i x := (he i).mono fun x h => by rcases h with h | h <;> simp [h]
  have hT0 (i) : ∀ᵐ x ∂m, 0 ≤ T (e i) x := D.scaled_resolvent_nonneg β hβ _ (he0 i)
  have hw (i j) : w i j = w j i := by
    dsimp [w, T, scaledResolvent]
    rw [smul_apply, smul_apply,
      real_inner_smul_left, real_inner_smul_left,
      D.form.resolvent_symm D.closed β hβ, real_inner_comm (e i)]
  have hw0 (i j) : 0 ≤ w i j := by
    rw [show w i j = inner ℝ (T (e i)) (e j) from rfl, L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [hT0 i, he0 j] with x hi hj
    change 0 ≤ e j x * T (e i) x
    exact mul_nonneg hj hi
  have hsum : ∀ᵐ x ∂m, (∑ i, e i : Lp ℝ 2 m) x ≤ 1 := by
    filter_upwards [coe_fintype_sum e, hs] with x hx hy
    simpa only [hx, Finset.sum_apply] using hy
  have hTsum : ∀ᵐ x ∂m, T (∑ i, e i) x ≤ 1 :=
    D.scaled_resolvent_le_const β hβ _ 1 zero_lt_one hsum
  have hm (i) : ∑ j, w i j ≤ mass i := by
    have hid : (∑ j, w i j) = inner ℝ (T (∑ j, e j)) (e i) := by
      simp only [map_sum, sum_inner]
      exact Finset.sum_congr rfl fun j _ => hw i j
    rw [hid]
    dsimp only [mass]
    rw [L2.inner_def, L2.inner_def]
    change (∫ x, e i x * T (∑ j, e j) x ∂m) ≤ ∫ x, e i x * e i x ∂m
    apply integral_mono_ae ((Lp.memLp _).integrable_mul (Lp.memLp _))
      ((Lp.memLp _).integrable_mul (Lp.memLp _))
    filter_upwards [he i, hTsum] with x hi ht
    change e i x * T (∑ j, e j) x ≤ e i x * e i x
    rcases hi with hi | hi
    · simp [hi]
    · simpa only [hi, one_mul, mul_one] using ht
  have hdiag (b : ι → ℝ) :
      inner ℝ (∑ i, b i • e i) (∑ i, b i • e i) = ∑ i, mass i * b i ^ 2 := by
    simp only [sum_inner, inner_sum, real_inner_smul_left, inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · dsimp [mass]
      ring
    · intro j _ hji
      rw [ho j i hji]
      ring
    · simp
  have hcross (b : ι → ℝ) :
      inner ℝ (T (∑ i, b i • e i)) (∑ i, b i • e i) =
        ∑ i, ∑ j, w i j * b i * b j := by
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      inner_smul_right, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show inner ℝ (T (e j)) (e i) = inner ℝ (T (e i)) (e j) from hw j i]
    dsimp [w]
    ring
  change inner ℝ ((∑ i, F (a i) • e i) - T (∑ i, F (a i) • e i)) _ ≤
    inner ℝ ((∑ i, a i • e i) - T (∑ i, a i • e i)) _
  rw [inner_sub_left, inner_sub_left, hdiag, hdiag, hcross, hcross]
  exact finite_energy_contraction a mass w hw hw0 hm hF h0

/-- A simple function is the sum of its nonzero fibers, also after a zero-preserving map. -/
theorem sum_nonzero_fibers (s : SimpleFunc X ℝ) (b : ℝ → ℝ) (hb : b 0 = 0) (x : X) :
    ∑ i : ↥(s.range.erase 0), b i.val * (s ⁻¹' {i.val}).indicator (fun _ => (1 : ℝ)) x =
      b (s x) := by
  classical
  by_cases hx : s x = 0
  · rw [hx, hb]
    apply Finset.sum_eq_zero
    intro i _
    have hi := (Finset.mem_erase.mp i.property).1
    have hxi : x ∉ s ⁻¹' {i.val} := by simpa [hx] using hi.symm
    rw [Set.indicator_of_notMem hxi, mul_zero]
  · let k : ↥(s.range.erase 0) := ⟨s x, Finset.mem_erase.mpr ⟨hx, s.mem_range_self x⟩⟩
    rw [Finset.sum_eq_single k]
    · rw [Set.indicator_of_mem (show x ∈ s ⁻¹' {k.val} from rfl), mul_one]
    · intro j _ hj
      have hxi : x ∉ s ⁻¹' {j.val} := by
        intro h
        apply hj
        exact Subtype.ext (show j.val = k.val from h.symm)
      rw [Set.indicator_of_notMem hxi, mul_zero]
    · simp

/-- Normal contractions decrease the resolvent energy of every L² simple function. -/
theorem simple_resolvent_contraction (β : ℝ) (hβ : 0 < β)
    (s : SimpleFunc X ℝ) (hs : MemLp (⇑s) 2 m)
    {F : ℝ → ℝ} (hF : LipschitzWith 1 F) (h0 : F 0 = 0) :
    let v := hs.toLp s
    let w := (hF.comp_memLp h0 hs).toLp (fun x => F (s x))
    inner ℝ (w - D.scaledResolvent β hβ w) w ≤
      inner ℝ (v - D.scaledResolvent β hβ v) v := by
  classical
  let I := ↥(s.range.erase 0)
  have hi0 (i : I) : i.val ≠ 0 := (Finset.mem_erase.mp i.property).1
  have hmeas (i : I) : MeasurableSet (s ⁻¹' {i.val}) := s.measurable (measurableSet_singleton _)
  have hfin (i : I) : m (s ⁻¹' {i.val}) ≠ ∞ :=
    (SimpleFunc.measure_preimage_lt_top_of_memLp (by norm_num) (by norm_num) s hs i.val (hi0 i)).ne
  let e : I → Lp ℝ 2 m := fun i => indicatorConstLp 2 (hmeas i) (hfin i) 1
  have hei (i : I) : ⇑(e i) =ᵐ[m] (s ⁻¹' {i.val}).indicator (fun _ => (1 : ℝ)) :=
    indicatorConstLp_coeFn
  have hrep (b : ℝ → ℝ) (hb : b 0 = 0) :
      ⇑(∑ i : I, b i.val • e i : Lp ℝ 2 m) =ᵐ[m] fun x => b (s x) := by
    filter_upwards [coe_fintype_sum (fun i : I => b i.val • e i), ae_all_iff.2 hei,
      ae_all_iff.2 (fun i : I => Lp.coeFn_smul (b i.val) (e i))] with x hsum hind hsmul
    rw [hsum]
    calc
      (∑ i : I, (b i.val • e i) x) =
          ∑ i : I, b i.val * (s ⁻¹' {i.val}).indicator (fun _ => (1 : ℝ)) x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hsmul i]
        change b i.val * e i x = _
        rw [hind i]
      _ = b (s x) := sum_nonzero_fibers s b hb x
  have h01 (i : I) : ∀ᵐ x ∂m, e i x = 0 ∨ e i x = 1 := by
    filter_upwards [hei i] with x hx
    rw [hx]
    by_cases hi : x ∈ s ⁻¹' {i.val} <;> simp [hi]
  have hsum : ∀ᵐ x ∂m, (∑ i : I, e i x) ≤ 1 := by
    filter_upwards [ae_all_iff.2 hei] with x hx
    have hid := sum_nonzero_fibers s (fun t => if t = 0 then 0 else 1) (by simp) x
    have hh : (∑ i : I, e i x) = if s x = 0 then 0 else 1 := by
      calc
        _ = ∑ i : I, (if i.val = 0 then 0 else 1) *
            (s ⁻¹' {i.val}).indicator (fun _ => (1 : ℝ)) x := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [hi0 i, ↓reduceIte, one_mul, hx i]
        _ = _ := hid
    rw [hh]
    split_ifs <;> norm_num
  have horth (i j : I) (hij : i ≠ j) : inner ℝ (e i) (e j) = 0 := by
    rw [L2.inner_def]
    have hz : (fun x => inner ℝ (e i x) (e j x)) =ᵐ[m] fun _ => (0 : ℝ) := by
      filter_upwards [hei i, hei j] with x hi hj
      change e j x * e i x = 0
      rw [hi, hj]
      by_cases hxi : x ∈ s ⁻¹' {i.val}
      · have hxj : x ∉ s ⁻¹' {j.val} := by
          intro hxj
          apply hij
          exact Subtype.ext (hxi.symm.trans hxj)
        rw [Set.indicator_of_notMem hxj, zero_mul]
      · rw [Set.indicator_of_notMem hxi, mul_zero]
    rw [integral_congr_ae hz, integral_zero]
  have hv : (∑ i : I, i.val • e i) = hs.toLp s :=
    Lp.ext ((hrep id rfl).trans hs.coeFn_toLp.symm)
  have hw : (∑ i : I, F i.val • e i) = (hF.comp_memLp h0 hs).toLp (fun x => F (s x)) :=
    Lp.ext ((hrep F h0).trans (hF.comp_memLp h0 hs).coeFn_toLp.symm)
  have h := D.finite_indicator_contraction β hβ e h01 hsum horth (fun i : I => i.val) hF h0
  simpa only [hv, hw] using h

/-- L² approximation extends the finite-fiber resolvent inequality to all L² data. -/
theorem resolvent_energy_contraction (β : ℝ) (hβ : 0 < β)
    {F : ℝ → ℝ} (hF : LipschitzWith 1 F) (h0 : F 0 = 0)
    (f w : Lp ℝ 2 m) (hw : ⇑w =ᵐ[m] fun x => F (f x)) :
    inner ℝ (w - D.scaledResolvent β hβ w) w ≤
      inner ℝ (f - D.scaledResolvent β hβ f) f := by
  let hf := (Lp.stronglyMeasurable f).measurable
  let s : ℕ → SimpleFunc X ℝ := fun n =>
    SimpleFunc.approxOn f hf (Set.range f ∪ {0}) 0 (by simp) n
  have hs (n) : MemLp (⇑(s n)) 2 m := SimpleFunc.memLp_approxOn_range hf (Lp.memLp f) n
  let v : ℕ → Lp ℝ 2 m := fun n => (hs n).toLp (s n)
  let z : ℕ → Lp ℝ 2 m := fun n =>
    (hF.comp_memLp h0 (hs n)).toLp (fun x => F (s n x))
  have hv : Tendsto v atTop (𝓝 f) := by
    have ht := SimpleFunc.tendsto_approxOn_range_Lp (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      hf (Lp.memLp f)
    have hid : (Lp.memLp f).toLp f = f := Lp.ext (Lp.memLp f).coeFn_toLp
    simpa only [hid] using ht
  have hb (n) : ‖z n - w‖ ≤ ‖v n - f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (z n) w, Lp.coeFn_sub (v n) f,
      (hs n).coeFn_toLp, (hF.comp_memLp h0 (hs n)).coeFn_toLp, hw] with x hz hv hs ht hw
    have h := hF.dist_le_mul (s n x) (f x)
    change (v n) x = s n x at hs
    change (z n) x = F (s n x) at ht
    simpa only [hz, hv, Pi.sub_apply, hs, ht, hw, NNReal.coe_one, one_mul,
      Real.dist_eq, Real.norm_eq_abs] using h
  have hz : Tendsto z atTop (𝓝 w) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun n => norm_nonneg _) hb (tendsto_iff_norm_sub_tendsto_zero.mp hv))
  have hvE := (hv.sub ((D.scaledResolvent β hβ).continuous.tendsto f |>.comp hv)).inner (𝕜 := ℝ) hv
  have hzE := (hz.sub ((D.scaledResolvent β hβ).continuous.tendsto w |>.comp hz)).inner (𝕜 := ℝ) hz
  apply le_of_tendsto_of_tendsto hzE hvE
  exact Eventually.of_forall fun n => D.simple_resolvent_contraction β hβ (s n) (hs n) hF h0

/--
BH 1991, I.3.3.1, scalar case: the printed Markov axiom implies every normal contraction.
-/
theorem normal_contraction {F : ℝ → ℝ}
    (hF : LipschitzWith 1 F) (h0 : F 0 = 0)
    (f : D.form.dom) (w : Lp ℝ 2 m)
    (hw : ⇑w =ᵐ[m] fun x => F ((f : Lp ℝ 2 m) x)) :
    ∃ hw' : w ∈ D.form.dom,
      D.form.E ⟨w, hw'⟩ ⟨w, hw'⟩ ≤ D.form.E f f := by
  apply D.form.mem_dom_energy_le_of_approxForm_bounded D.closed D.dense w (D.form.E f f)
  intro n
  have h := D.resolvent_energy_contraction (QuadForm.resolventParameter n)
    (QuadForm.resolventParameter_pos n) hF h0 (f : Lp ℝ 2 m) w hw
  have h' := mul_le_mul_of_nonneg_left h (QuadForm.resolventParameter_pos n).le
  exact h'.trans (D.form.approxForm_le_energy D.closed _ _ f)

/-- The capacity structure retains the original form and its original closedness proof. -/
@[reducible] def toCapacity : ErrorCalculus.Capacity.DirichletForm m where
  form := D.form
  closed := D.closed
  contraction := D.normal_contraction

/-- The adapter does not replace the quadratic form. -/
theorem toCapacity_form : D.toCapacity.form = D.form := rfl

/-- The capacity inclusion has dense range because the original BH domain is dense. -/
theorem denseRange_toCapacity : DenseRange D.toCapacity.toLp := by
  have he : Set.range D.toCapacity.toLp = (D.form.dom : Set (Lp ℝ 2 m)) := by
    ext f
    constructor
    · rintro ⟨v, rfl⟩
      exact (D.form.formToDomain v).property
    · intro hf
      exact ⟨D.form.formToDomain.symm ⟨f, hf⟩, rfl⟩
  change Dense (Set.range D.toCapacity.toLp)
  rw [he]
  exact D.dense

/-- Essential boundedness is unchanged by the form-preserving adapter. -/
theorem bounded_iff_toCapacity (f : D.form.FormSpace) :
    D.Bounded (D.form.formToDomain f) ↔ f ∈ D.toCapacity.bddSpace := by
  change (∃ C : ℝ, ∀ᵐ x ∂m, ‖(D.toCapacity.toLp f) x‖ ≤ C) ↔
    (∃ C : ℝ, ∀ᵐ x ∂m, |(D.toCapacity.toLp f) x| ≤ C)
  simp only [Real.norm_eq_abs]

/--
BH 1991, I.3.3.2: bounded domain elements have a product in the original domain.
-/
theorem bounded_product (f g : D.form.dom)
    (hf : D.Bounded f) (hg : D.Bounded g) :
    ∃ p : D.form.dom,
      ⇑(p : Lp ℝ 2 m) =ᵐ[m]
        fun x => (f : Lp ℝ 2 m) x * (g : Lp ℝ 2 m) x := by
  have hf' : D.form.formToDomain.symm f ∈ D.toCapacity.bddSpace :=
    (D.bounded_iff_toCapacity _).mp (by simpa using hf)
  have hg' : D.form.formToDomain.symm g ∈ D.toCapacity.bddSpace :=
    (D.bounded_iff_toCapacity _).mp (by simpa using hg)
  exact ⟨D.form.formToDomain (D.toCapacity.mulS (D.form.formToDomain.symm f)
    (D.form.formToDomain.symm g)), D.toCapacity.coeFn_toLp_mulS hf' hg'⟩

/-- The printed existential product identity is equivalent to the capacity (R) identity. -/
theorem admitsCarreDuChamp_iff_toCapacity :
    D.AdmitsCarreDuChamp ↔ D.toCapacity.AdmitsCarreDuChamp := by
  constructor
  · rintro ⟨H, hH, hd, hR⟩
    have hH' : H ≤ D.toCapacity.bddSpace := fun x hx =>
      (D.bounded_iff_toCapacity x).mp (hH x hx)
    refine ⟨H, hH', hd, ?_⟩
    intro x hx
    obtain ⟨ft, hft⟩ := hR x hx
    refine ⟨ft, ?_⟩
    intro z hz
    obtain ⟨p, q, hp, hq, he⟩ := hft (D.form.formToDomain z)
      ((D.bounded_iff_toCapacity z).mpr hz)
    have hp' : D.toCapacity.mulS x z = D.form.formToDomain.symm p :=
      D.toCapacity.mulS_eq_of_rep (hH' hx) hz hp
    have hq' : D.toCapacity.mulS x x = D.form.formToDomain.symm q :=
      D.toCapacity.mulS_eq_of_rep (hH' hx) (hH' hx) (by
        change ⇑(q : Lp ℝ 2 m) =ᵐ[m] fun y =>
          (D.form.formToDomain x : Lp ℝ 2 m) y * (D.form.formToDomain x : Lp ℝ 2 m) y
        simpa only [pow_two] using hq)
    rw [hp', hq', D.toCapacity.ener_apply, D.toCapacity.ener_apply]
    exact he
  · rintro ⟨H, hH, hd, hR⟩
    refine ⟨H, (fun x hx => (D.bounded_iff_toCapacity x).mpr (hH hx)), hd, ?_⟩
    intro x hx
    obtain ⟨ft, hft⟩ := hR x hx
    refine ⟨ft, ?_⟩
    intro h hh
    let z := D.form.formToDomain.symm h
    have hz : z ∈ D.toCapacity.bddSpace :=
      (D.bounded_iff_toCapacity z).mp (by simpa [z] using hh)
    refine ⟨D.form.formToDomain (D.toCapacity.mulS x z),
      D.form.formToDomain (D.toCapacity.mulS x x),
      D.toCapacity.coeFn_toLp_mulS (hH hx) hz, ?_, ?_⟩
    · have hq := D.toCapacity.coeFn_toLp_mulS (hH hx) (hH hx)
      change ⇑(D.form.formToDomain (D.toCapacity.mulS x x) : Lp ℝ 2 m) =ᵐ[m]
        fun y => (D.form.formToDomain x : Lp ℝ 2 m) y *
          (D.form.formToDomain x : Lp ℝ 2 m) y at hq
      simpa only [pow_two] using hq
    · have he := hft z hz
      rw [D.toCapacity.ener_apply, D.toCapacity.ener_apply] at he
      exact he

/--
Conditional on property (R), a carré du champ exists in the original BH structure. Source: BH
1991, I.4.1.3.
-/
theorem nonempty_carreDuChamp (hR : D.AdmitsCarreDuChamp) :
    Nonempty D.CarreDuChamp := by
  obtain ⟨G, hG⟩ := D.toCapacity.exists_isCarreDuChamp D.denseRange_toCapacity
    (D.admitsCarreDuChamp_iff_toCapacity.mp hR)
  refine ⟨{ Γ := G
            symm := D.toCapacity.isCarreDuChamp_symm D.denseRange_toCapacity hG
            nonneg := ?_
            product := ?_ }⟩
  · intro f
    exact (Lp.coeFn_nonneg _).mpr
      (D.toCapacity.isCarreDuChamp_nonneg D.denseRange_toCapacity hG f)
  · intro f g h hf hg hh
    have hf' := (D.bounded_iff_toCapacity f).mp hf
    have hg' := (D.bounded_iff_toCapacity g).mp hg
    have hh' := (D.bounded_iff_toCapacity h).mp hh
    refine ⟨D.form.formToDomain (D.toCapacity.mulS f h),
      D.form.formToDomain (D.toCapacity.mulS g h),
      D.form.formToDomain (D.toCapacity.mulS f g),
      D.toCapacity.coeFn_toLp_mulS hf' hh', D.toCapacity.coeFn_toLp_mulS hg' hh',
      D.toCapacity.coeFn_toLp_mulS hf' hg', ?_⟩
    have he := hG f hf' g hg' h hh'
    simp only [D.toCapacity.ener_apply] at he
    exact he

/-- Every BH carré du champ satisfies the capacity characteristic identity. -/
theorem carreDuChamp_toCapacity (G : D.CarreDuChamp) :
    D.toCapacity.IsCarreDuChamp G.Γ := by
  intro f hf g hg h hh
  obtain ⟨p, q, r, hp, hq, hr, he⟩ := G.product f g h
    ((D.bounded_iff_toCapacity f).mpr hf) ((D.bounded_iff_toCapacity g).mpr hg)
    ((D.bounded_iff_toCapacity h).mpr hh)
  have hp' : D.toCapacity.mulS f h = D.form.formToDomain.symm p :=
    D.toCapacity.mulS_eq_of_rep hf hh hp
  have hq' : D.toCapacity.mulS g h = D.form.formToDomain.symm q :=
    D.toCapacity.mulS_eq_of_rep hg hh hq
  have hr' : D.toCapacity.mulS f g = D.form.formToDomain.symm r :=
    D.toCapacity.mulS_eq_of_rep hf hg hr
  rw [hp', hq', hr', D.toCapacity.ener_apply, D.toCapacity.ener_apply,
    D.toCapacity.ener_apply]
  exact he

/--
BH 1991, I.4.1.3: the carré du champ is unique as a continuous bilinear operator.
-/
theorem carreDuChamp_unique (G G' : D.CarreDuChamp) : G.Γ = G'.Γ :=
  D.toCapacity.isCarreDuChamp_unique D.denseRange_toCapacity
    (D.carreDuChamp_toCapacity G) (D.carreDuChamp_toCapacity G')

/-!
Subsequent results: the local energy integral and a common positive-semidefinite gamma matrix are
proved in `DprBridge.BH1991GammaLocality`; the L1 generator core in `DprBridge.BH1991ResolventCore`;
the centered chain rule and actual normal currents with their Dirac boundary in
`DprBridge.BH1991ChainCurrents`; the equivalent finite reference and its RN densities, the kernel
projection argument and the countable certificates in `DprBridge.BH1991PrintedProof`. No
unconditional printed BH EID theorem is declared in this module.
-/
end DprBridge.BH1991.DirichletForm

#print axioms DprBridge.BH1991.DirichletForm.exists_upper_truncation
#print axioms DprBridge.BH1991.DirichletForm.abs_min_le_abs
#print axioms DprBridge.BH1991.DirichletForm.exists_nonpositive_part
#print axioms DprBridge.BH1991.DirichletForm.exists_positive_part
#print axioms DprBridge.BH1991.DirichletForm.exists_unit_clamp
#print axioms DprBridge.BH1991.DirichletForm.positivePart
#print axioms DprBridge.BH1991.DirichletForm.coe_positivePart
#print axioms DprBridge.BH1991.DirichletForm.energy_positivePart_le
#print axioms DprBridge.BH1991.DirichletForm.negativePart
#print axioms DprBridge.BH1991.DirichletForm.coe_negativePart
#print axioms DprBridge.BH1991.DirichletForm.positivePart_sub_negativePart
#print axioms DprBridge.BH1991.DirichletForm.nonpos_of_quadratic_bounds
#print axioms DprBridge.BH1991.DirichletForm.energy_nonpos_of_disjoint
#print axioms DprBridge.BH1991.DirichletForm.energy_positive_negative_nonpos
#print axioms DprBridge.BH1991.DirichletForm.exists_absolute_value
#print axioms DprBridge.BH1991.DirichletForm.scaled_resolvent_fixed
#print axioms DprBridge.BH1991.DirichletForm.scaled_resolvent_nonneg
#print axioms DprBridge.BH1991.DirichletForm.scaled_resolvent_le_const
#print axioms DprBridge.BH1991.DirichletForm.scaled_resolvent_submarkov
#print axioms DprBridge.BH1991.DirichletForm.scaled_resolvent_mono
#print axioms DprBridge.BH1991.DirichletForm.scaled_resolvent_abs_le
#print axioms DprBridge.BH1991.DirichletForm.isGeneratorPair_resolvent
#print axioms DprBridge.BH1991.DirichletForm.IsGeneratorPair.smul
#print axioms DprBridge.BH1991.DirichletForm.isGeneratorPair_scaled_resolvent
#print axioms DprBridge.BH1991.DirichletForm.finite_energy_identity
#print axioms DprBridge.BH1991.DirichletForm.finite_energy_contraction
#print axioms DprBridge.BH1991.DirichletForm.coe_fintype_sum
#print axioms DprBridge.BH1991.DirichletForm.scaledResolvent
#print axioms DprBridge.BH1991.DirichletForm.finite_indicator_contraction
#print axioms DprBridge.BH1991.DirichletForm.sum_nonzero_fibers
#print axioms DprBridge.BH1991.DirichletForm.simple_resolvent_contraction
#print axioms DprBridge.BH1991.DirichletForm.resolvent_energy_contraction
#print axioms DprBridge.BH1991.DirichletForm.normal_contraction
#print axioms DprBridge.BH1991.DirichletForm.toCapacity
#print axioms DprBridge.BH1991.DirichletForm.toCapacity_form
#print axioms DprBridge.BH1991.DirichletForm.denseRange_toCapacity
#print axioms DprBridge.BH1991.DirichletForm.bounded_iff_toCapacity
#print axioms DprBridge.BH1991.DirichletForm.bounded_product
#print axioms DprBridge.BH1991.DirichletForm.admitsCarreDuChamp_iff_toCapacity
#print axioms DprBridge.BH1991.DirichletForm.nonempty_carreDuChamp
#print axioms DprBridge.BH1991.DirichletForm.carreDuChamp_toCapacity
#print axioms DprBridge.BH1991.DirichletForm.carreDuChamp_unique

#check @DprBridge.BH1991.DirichletForm.normal_contraction
#check @DprBridge.BH1991.DirichletForm.nonempty_carreDuChamp
