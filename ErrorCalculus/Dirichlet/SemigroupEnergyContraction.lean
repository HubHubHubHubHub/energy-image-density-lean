import ErrorCalculus.Dirichlet.SemigroupEnergy

noncomputable section
open Filter Topology Set
namespace ErrorCalculus

/--
If E ≥ 0 and aₙ is bounded above with aₙ² ≤ E aₙ₊₁ for all n, then a₀ ≤ E. Iteration would otherwise
force growth incompatible with boundedness.
-/
theorem le_of_bounded_iterated_sq {a : ℕ → ℝ} {E C : ℝ} (hE : 0 ≤ E)
    (hb : ∀ n, a n ≤ C) (hs : ∀ n, (a n)^2 ≤ a (n+1) * E) : a 0 ≤ E := by
  by_cases hzero : E = 0
  · have h := hs 0
    rw [hzero] at h ⊢
    nlinarith [sq_nonneg (a 0)]
  have hpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
  by_contra hn
  have hgap : 0 < a 0 - E := sub_pos.mpr (lt_of_not_ge hn)
  have hstep (n : ℕ) : 2 * a n - E ≤ a (n+1) := by
    have h := hs n
    have hh := sq_nonneg (a n - E)
    nlinarith
  have hgrowth (n : ℕ) : a 0 + (n : ℝ) * (a 0 - E) ≤ a n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := hstep n
      have hp : 0 ≤ (n : ℝ) * (a 0 - E) := mul_nonneg (Nat.cast_nonneg n) hgap.le
      push_cast
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - a 0) / (a 0 - E))
  have hh := (div_lt_iff₀ hgap).mp hn
  linarith [hgrowth n, hb n]

namespace QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (Q : QuadForm H) (hQ : Q.IsClosed) (hd : Dense (Q.dom : Set H))

/-- direct resolvent proof of commutation on the generator domain. -/
theorem generator_semigroup {t : ℝ} (ht : 0 ≤ t) (u : (Q.formResolvent hQ hd).dom) :
    (Q.formResolvent hQ hd).generator ⟨Q.semigroup hQ hd t u, Q.semigroup_mem_dom hQ hd ht u⟩ =
      Q.semigroup hQ hd t ((Q.formResolvent hQ hd).generator u) := by
  let R := Q.formResolvent hQ hd
  obtain ⟨y, hy⟩ := u.property
  have hu : u = ⟨R.G 1 y, R.mem_dom_G zero_lt_one y⟩ := Subtype.ext hy.symm
  have hc := congrArg (fun T : H →L[ℝ] H => T y)
    (Q.semigroup_commute_resolvent hQ hd zero_lt_one ht).eq
  change Q.semigroup hQ hd t (Q.resolvent hQ 1 zero_lt_one y) =
    Q.resolvent hQ 1 zero_lt_one (Q.semigroup hQ hd t y) at hc
  have hc' : Q.semigroup hQ hd t (R.G 1 y) = R.G 1 (Q.semigroup hQ hd t y) := by
    simpa only [R, Q.formResolvent_G hQ hd zero_lt_one] using hc
  have hv : (⟨Q.semigroup hQ hd t u, Q.semigroup_mem_dom hQ hd ht u⟩ : R.dom) =
      ⟨R.G 1 (Q.semigroup hQ hd t y), R.mem_dom_G zero_lt_one _⟩ := by
    apply Subtype.ext
    exact (congrArg (Q.semigroup hQ hd t) hy.symm).trans hc'
  change R.generator _ = Q.semigroup hQ hd t (R.generator u)
  rw [hv, R.generator_G_one, hu, R.generator_G_one, map_sub, hc']

/-- Ambient expression for the diagonal energy of the orbit on nonnegative times.
Its definition on all real times makes interval integration convenient. -/
def semigroupEnergy (u : (Q.formResolvent hQ hd).dom) (t : ℝ) : ℝ :=
  -inner ℝ (Q.semigroup hQ hd t ((Q.formResolvent hQ hd).generator u))
    (Q.semigroup hQ hd t u)

/-- The ambient expression is exactly the form energy, with the domain proof explicit. -/
theorem semigroupEnergy_eq {t : ℝ} (ht : 0 ≤ t) (u : (Q.formResolvent hQ hd).dom) :
    Q.semigroupEnergy hQ hd u t =
      Q.E ⟨Q.semigroup hQ hd t u, Q.formResolvent_dom_le hQ hd (Q.semigroup_mem_dom hQ hd ht u)⟩
        ⟨Q.semigroup hQ hd t u, Q.formResolvent_dom_le hQ hd (Q.semigroup_mem_dom hQ hd ht u)⟩ := by
  rw [Q.energy_eq_neg_inner_generator hQ hd
    ⟨Q.semigroup hQ hd t u, Q.semigroup_mem_dom hQ hd ht u⟩,
    Q.generator_semigroup hQ hd ht]
  rfl

theorem semigroupEnergy_double {t : ℝ} (ht : 0 ≤ t) (u : (Q.formResolvent hQ hd).dom) :
    Q.semigroupEnergy hQ hd u t =
      -inner ℝ (Q.semigroup hQ hd (2*t) ((Q.formResolvent hQ hd).generator u)) (u : H) := by
  rw [show 2*t = t+t by ring, Q.semigroup_add hQ hd ht ht, mul_apply_eq_comp,
    Q.semigroup_symm hQ hd ht]
  rfl

/-- The diagonal energy equals the polarized energy at double time. -/
theorem energy_semigroup_eq {t : ℝ} (ht : 0 ≤ t) (u : (Q.formResolvent hQ hd).dom) :
    Q.semigroupEnergy hQ hd u t =
      Q.E ⟨Q.semigroup hQ hd (2*t) u,
        Q.formResolvent_dom_le hQ hd (Q.semigroup_mem_dom hQ hd (by positivity) u)⟩
        ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩ := by
  rw [Q.energy_eq_neg_inner_generator hQ hd
    ⟨Q.semigroup hQ hd (2*t) u, Q.semigroup_mem_dom hQ hd (by positivity) u⟩,
    Q.generator_semigroup hQ hd (by positivity), Q.semigroupEnergy_double hQ hd ht]

@[simp] theorem semigroupEnergy_zero (u : (Q.formResolvent hQ hd).dom) :
    Q.semigroupEnergy hQ hd u 0 =
      Q.E ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩
        ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩ := by
  rw [Q.energy_eq_neg_inner_generator hQ hd]
  simp [semigroupEnergy]

theorem semigroupEnergy_nonneg {t : ℝ} (ht : 0 ≤ t) (u : (Q.formResolvent hQ hd).dom) :
    0 ≤ Q.semigroupEnergy hQ hd u t := by
  rw [Q.semigroupEnergy_eq hQ hd ht]
  exact Q.nonneg _

theorem semigroupEnergy_le_norm {t : ℝ} (ht : 0 ≤ t) (u : (Q.formResolvent hQ hd).dom) :
    Q.semigroupEnergy hQ hd u t ≤ ‖(Q.formResolvent hQ hd).generator u‖ * ‖(u : H)‖ := by
  unfold semigroupEnergy
  apply (neg_le_abs _).trans
  apply (abs_real_inner_le_norm _ _).trans
  exact mul_le_mul (Q.norm_semigroup_apply_le hQ hd ht _)
    (Q.norm_semigroup_apply_le hQ hd ht _) (norm_nonneg _) (norm_nonneg _)

theorem semigroupEnergy_sq_le {t : ℝ} (ht : 0 ≤ t) (u : (Q.formResolvent hQ hd).dom) :
    (Q.semigroupEnergy hQ hd u t)^2 ≤
      Q.semigroupEnergy hQ hd u (2*t) * Q.semigroupEnergy hQ hd u 0 := by
  rw [Q.energy_semigroup_eq hQ hd ht, Q.semigroupEnergy_eq hQ hd (by positivity),
    Q.semigroupEnergy_zero]
  have hc := Q.cauchy_schwarz
    ⟨Q.semigroup hQ hd (2*t) u,
      Q.formResolvent_dom_le hQ hd (Q.semigroup_mem_dom hQ hd (by positivity) u)⟩
    ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩
  have hs := (sq_le_sq₀ (abs_nonneg _) (by unfold seminorm; positivity)).mpr hc
  simpa only [sq_abs, mul_pow, seminorm, Real.sq_sqrt (Q.nonneg _)] using hs

/-- bounded iterated Cauchy--Schwarz contracts the form energy. -/
theorem energy_semigroup_le {t : ℝ} (ht : 0 ≤ t) (u : (Q.formResolvent hQ hd).dom) :
    Q.semigroupEnergy hQ hd u t ≤
      Q.E ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩
        ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩ := by
  let a : ℕ → ℝ := fun n => Q.semigroupEnergy hQ hd u ((2:ℝ)^n*t)
  have hh := le_of_bounded_iterated_sq
    (a := a) (E := Q.semigroupEnergy hQ hd u 0)
    (Q.semigroupEnergy_nonneg hQ hd le_rfl u)
    (fun n => Q.semigroupEnergy_le_norm hQ hd (by positivity) u)
    (fun n => by
      dsimp [a]
      convert Q.semigroupEnergy_sq_le hQ hd (show 0 ≤ (2:ℝ)^n*t by positivity) u using 1
      congr 2
      ring)
  simpa [a] using hh

/-- The energy decreases along each generator-domain orbit. -/
theorem energy_semigroup_antitone (u : (Q.formResolvent hQ hd).dom) :
    AntitoneOn (Q.semigroupEnergy hQ hd u) (Ici 0) := by
  intro s hs t ht hst
  let v : (Q.formResolvent hQ hd).dom :=
    ⟨Q.semigroup hQ hd s u, Q.semigroup_mem_dom hQ hd hs u⟩
  have hh := Q.energy_semigroup_le hQ hd (sub_nonneg.mpr hst) v
  rw [← Q.semigroupEnergy_eq hQ hd hs] at hh
  have he : Q.semigroupEnergy hQ hd v (t-s) = Q.semigroupEnergy hQ hd u t := by
    dsimp [semigroupEnergy, v]
    rw [Q.generator_semigroup hQ hd hs,
      ← mul_apply_eq_comp, ← Q.semigroup_add hQ hd (sub_nonneg.mpr hst) hs,
      ← mul_apply_eq_comp, ← Q.semigroup_add hQ hd (sub_nonneg.mpr hst) hs,
      sub_add_cancel]
  rwa [he] at hh

end QuadForm
end ErrorCalculus
