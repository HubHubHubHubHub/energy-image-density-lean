import ErrorCalculus.Dirichlet.LocalDirichletFormLipschitz
import ErrorCalculus.Dirichlet.ErrorStructure
import ErrorCalculus.Dirichlet.ProductRule
import ErrorCalculus.Dirichlet.CarreDuChampExistence

/-!
# bounded products, density of bounded elements, connection to `Capacity.DirichletForm`

## Main results
For a `LocalDirichletForm`: squares and products of essentially bounded elements in 𝔻 (BH 1991, cor.
I.3.3.2, p. 14, by squares then polarization); ℰ-orthogonal decomposition f = T_c f + (f − T_c f) by
(L₂) (BH I.5.1.3, p. 29) and convergence of the clamps Tₙ f → f for ℰ₁; connection to
`Capacity.DirichletForm` framework (same form, same domain; BH I.3.3.1, p = 1, K = 1), density of 𝔻
→ L² and separation by bounded test functions (`ae_eq_of_integral_mul_eq`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option maxHeartbeats 800000

namespace ErrorCalculus

/-! ## C. Bounded products (BH I.3.3.2) and density of bounded elements -/

/-- Symmetric clamping error: |((−n) ∨ (t ∧ n)) − t| ≤ |t|. -/
theorem abs_clamp_sub_le {n : ℝ} (hn : 0 ≤ n) (t : ℝ) : |max (-n) (min t n) - t| ≤ |t| := by
  rcases le_total t n with h | h
  · rw [min_eq_left h]
    rcases le_total (-n) t with h' | h'
    · rw [max_eq_right h', sub_self, abs_zero]
      exact abs_nonneg t
    · rw [max_eq_left h', abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      linarith
  · rw [min_eq_right h, max_eq_right (by linarith), abs_of_nonpos (by linarith),
      abs_of_nonneg (by linarith)]
    linarith

/-- Decomposition t − ((−n) ∨ (t ∧ n)) = (t − n)⁺ − (−t − n)⁺. -/
theorem sub_clamp_eq {n : ℝ} (hn : 0 ≤ n) (t : ℝ) :
    t - max (-n) (min t n) = max (t - n) 0 - max (-t - n) 0 := by
  rcases le_total t n with h | h
  · rw [min_eq_left h, max_eq_right (by linarith : t - n ≤ 0)]
    rcases le_total (-n) t with h' | h'
    · rw [max_eq_right h', max_eq_right (by linarith : -t - n ≤ 0)]
      ring
    · rw [max_eq_left h', max_eq_left (by linarith : 0 ≤ -t - n)]
      ring
  · rw [min_eq_right h, max_eq_right (by linarith), max_eq_left (by linarith : 0 ≤ t - n),
      max_eq_right (by linarith : -t - n ≤ 0)]
    ring

/-- The positive part of t − n is 1-Lipschitz in t. -/
theorem lipschitzWith_pos_part_sub (n : ℝ) : LipschitzWith 1 (fun t : ℝ => max (t - n) 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
  have h := abs_max_sub_max_le_abs (s - n) (t - n) 0
  rwa [show s - n - (t - n) = s - t by ring] at h

/-- The positive part of −t − n is 1-Lipschitz in t. -/
theorem lipschitzWith_neg_part_sub (n : ℝ) : LipschitzWith 1 (fun t : ℝ => max (-t - n) 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
  have h := abs_max_sub_max_le_abs (-s - n) (-t - n) 0
  rw [show -s - n - (-t - n) = -(s - t) by ring, abs_neg] at h
  exact h

/-- The map t ↦ ((−M) ∨ (t ∧ M))² is 2M-Lipschitz. -/
theorem lipschitzWith_clamp_sq {M : ℝ} (hM : 0 ≤ M) :
    LipschitzWith ⟨2 * M, by positivity⟩ (fun t : ℝ => (max (-M) (min t M)) ^ 2) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hc : LipschitzWith 1 (fun t : ℝ => max (-M) (min t M)) :=
    (LipschitzWith.id.min_const M).const_max (-M)
  have h1 := hc.dist_le_mul s t
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq] at h1
  rw [Real.dist_eq, Real.dist_eq]
  change _ ≤ 2 * M * |s - t|
  have bs : |max (-M) (min s M)| ≤ M :=
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have bt : |max (-M) (min t M)| ≤ M :=
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  rw [show (max (-M) (min s M)) ^ 2 - (max (-M) (min t M)) ^ 2 =
    (max (-M) (min s M) - max (-M) (min t M)) * (max (-M) (min s M) + max (-M) (min t M)) by
      ring, abs_mul]
  have h2 : |max (-M) (min s M) + max (-M) (min t M)| ≤ 2 * M :=
    (abs_add_le _ _).trans (by linarith)
  calc _ ≤ |s - t| * (2 * M) := mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)
    _ = 2 * M * |s - t| := by ring

namespace LocalDirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (D : LocalDirichletForm μ)

/-- Existence of an L² class of F ∘ f, for Lipschitz F (finite μ). -/
theorem exists_lp_comp {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) (f : Lp ℝ 2 μ) :
    ∃ w : Lp ℝ 2 μ, ⇑w =ᵐ[μ] fun x => F (f x) :=
  ErrorStructure.exists_composition (μ := μ) (fun _ : Fin 1 => f) (F := fun v => F (v 0))
    (hF.comp (LipschitzWith.eval 0))

/--
BH 1991, cor. I.3.3.2 (p. 14), case f = g, with the energy bound from I.3.3.1 (local route).

If |f| ≤ M a.e., every class w of f² lies in 𝔻 and ℰ(w) ≤ (2M)² ℰ(f).
-/
theorem exists_sq_mem {f : D.form.dom} {M : ℝ} (hM : ∀ᵐ x ∂μ, |(f : Lp ℝ 2 μ) x| ≤ M)
    (w : Lp ℝ 2 μ) (hw : ⇑w =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x ^ 2) :
    ∃ hw' : w ∈ D.form.dom, D.form.E ⟨w, hw'⟩ ⟨w, hw'⟩ ≤ (2 * M) ^ 2 * D.form.E f f := by
  haveI : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
  obtain ⟨x₀, hx₀⟩ := hM.exists
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hx₀
  have hw' : ⇑w =ᵐ[μ] fun x => (max (-M) (min ((f : Lp ℝ 2 μ) x) M)) ^ 2 := by
    filter_upwards [hw, hM] with x h1 h2
    rw [h1, min_eq_left (abs_le.1 h2).2, max_eq_right (abs_le.1 h2).1]
  obtain ⟨hd, hE⟩ := D.exists_mem_of_lipschitzWith (lipschitzWith_clamp_sq hM0) f w hw'
  exact ⟨hd, hE⟩

/-- L² class of the square of an essentially bounded class. -/
theorem exists_lp_sq {s : Lp ℝ 2 μ} {M : ℝ} (hM : ∀ᵐ x ∂μ, |s x| ≤ M) :
    ∃ q : Lp ℝ 2 μ, ⇑q =ᵐ[μ] fun x => s x ^ 2 := by
  have hm : MemLp (fun x => s x ^ 2) 2 μ := by
    refine MemLp.of_bound ((Lp.aestronglyMeasurable s).pow 2) (M ^ 2) ?_
    filter_upwards [hM] with x hx
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  exact ⟨hm.toLp _, hm.coeFn_toLp⟩

/--
BH 1991, cor. I.3.3.2 (p. 14), first assertion: 𝔻 ∩ L^∞ is an algebra (local route: squares, then
polarization).

If f, g ∈ 𝔻 are essentially bounded, every class w of f g lies in 𝔻.
-/
theorem mul_mem_of_aeBounded {f g : D.form.dom} (hf : AEBounded (μ := μ) ((f : Lp ℝ 2 μ) : Ω → ℝ))
    (hg : AEBounded (μ := μ) ((g : Lp ℝ 2 μ) : Ω → ℝ)) (w : Lp ℝ 2 μ)
    (hw : ⇑w =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (g : Lp ℝ 2 μ) x) : w ∈ D.form.dom := by
  obtain ⟨C₁, h₁⟩ := hf
  obtain ⟨C₂, h₂⟩ := hg
  have hs : ∀ᵐ x ∂μ, |((f + g : D.form.dom) : Lp ℝ 2 μ) x| ≤ C₁ + C₂ := by
    filter_upwards [h₁, h₂, Lp.coeFn_add (f : Lp ℝ 2 μ) (g : Lp ℝ 2 μ)] with x a b c
    rw [Submodule.coe_add, c, Pi.add_apply]
    rw [Real.norm_eq_abs] at a b
    exact (abs_add_le _ _).trans (add_le_add a b)
  have hd : ∀ᵐ x ∂μ, |((f - g : D.form.dom) : Lp ℝ 2 μ) x| ≤ C₁ + C₂ := by
    filter_upwards [h₁, h₂, Lp.coeFn_sub (f : Lp ℝ 2 μ) (g : Lp ℝ 2 μ)] with x a b c
    rw [Submodule.coe_sub, c, Pi.sub_apply]
    rw [Real.norm_eq_abs] at a b
    exact (abs_sub _ _).trans (add_le_add a b)
  obtain ⟨q₁, hq₁⟩ := exists_lp_sq (μ := μ) hs
  obtain ⟨q₂, hq₂⟩ := exists_lp_sq (μ := μ) hd
  obtain ⟨m₁, -⟩ := D.exists_sq_mem hs q₁ hq₁
  obtain ⟨m₂, -⟩ := D.exists_sq_mem hd q₂ hq₂
  have he : w = (1 / 4 : ℝ) • (q₁ - q₂) := by
    apply Lp.ext
    filter_upwards [hw, hq₁, hq₂, Lp.coeFn_smul (1 / 4 : ℝ) (q₁ - q₂), Lp.coeFn_sub q₁ q₂,
      Lp.coeFn_add (f : Lp ℝ 2 μ) (g : Lp ℝ 2 μ), Lp.coeFn_sub (f : Lp ℝ 2 μ) (g : Lp ℝ 2 μ)]
      with x a b c d e k l
    rw [d, Pi.smul_apply, e, Pi.sub_apply, b, c, a, Submodule.coe_add, Submodule.coe_sub, k, l,
      Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [he]
  exact D.form.dom.smul_mem _ (D.form.dom.sub_mem m₁ m₂)

/-- Bounds for the symmetric clamp. -/
theorem abs_clamp_le (n : ℕ) (f : D.form.dom) :
    ∀ᵐ x ∂μ, |((D.clamp (-(n : ℝ)) n f : D.form.dom) : Lp ℝ 2 μ) x| ≤ n := by
  filter_upwards [D.coeFn_clamp (-(n : ℝ)) n f] with x hx
  rw [hx]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/--
a consequence of (L₂) (BH 1991, I.5.1.3, p. 29): ℰ-orthogonal decomposition f = T_c(f) + (f −
T_c(f)), T_c(f) = (−c) ∨ (f ∧ c), c ≥ 0.

ℰ(f) = ℰ(T_c f) + ℰ(f − T_c f).
-/
theorem energy_eq_clamp_add {c : ℝ} (hc : 0 ≤ c) (f : D.form.dom) :
    D.form.E f f = D.form.E (D.clamp (-c) c f) (D.clamp (-c) c f) +
      D.form.E (f - D.clamp (-c) c f) (f - D.clamp (-c) c f) := by
  set T := D.clamp (-c) c f with hT
  obtain ⟨wP, hwP⟩ := exists_lp_comp (μ := μ) (lipschitzWith_pos_part_sub c) (f : Lp ℝ 2 μ)
  obtain ⟨wM, hwM⟩ := exists_lp_comp (μ := μ) (lipschitzWith_neg_part_sub c) (f : Lp ℝ 2 μ)
  obtain ⟨mP, -⟩ := D.exists_mem_of_lipschitzWith (lipschitzWith_pos_part_sub c) f wP hwP
  obtain ⟨mM, -⟩ := D.exists_mem_of_lipschitzWith (lipschitzWith_neg_part_sub c) f wM hwM
  set P : D.form.dom := ⟨wP, mP⟩
  set M : D.form.dom := ⟨wM, mM⟩
  have hdec : f - T = P - M := by
    apply QuadForm.dom_ext_ae
    filter_upwards [Lp.coeFn_sub (f : Lp ℝ 2 μ) (T : Lp ℝ 2 μ), Lp.coeFn_sub wP wM,
      D.coeFn_clamp (-c) c f, hwP, hwM] with x h1 h2 h3 h4 h5
    rw [Submodule.coe_sub, h1, Pi.sub_apply, Submodule.coe_sub, h2, Pi.sub_apply]
    change (f : Lp ℝ 2 μ) x - (T : Lp ℝ 2 μ) x = wP x - wM x
    rw [h3, h4, h5]
    exact sub_clamp_eq hc _
  have hP : D.form.E T P = 0 := by
    apply D.strongLocality T P (-c)
    filter_upwards [D.coeFn_clamp (-c) c f, hwP] with x a b
    change ((T : Lp ℝ 2 μ) x + -c) * wP x = 0
    rw [a, b]
    rcases le_total c ((f : Lp ℝ 2 μ) x) with h | h
    · rw [min_eq_right h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith : (f : Lp ℝ 2 μ) x - c ≤ 0)]
      ring
  have hM : D.form.E T M = 0 := by
    apply D.strongLocality T M c
    filter_upwards [D.coeFn_clamp (-c) c f, hwM] with x a b
    change ((T : Lp ℝ 2 μ) x + c) * wM x = 0
    rw [a, b]
    rcases le_total ((f : Lp ℝ 2 μ) x) (-c) with h | h
    · rw [min_eq_left (by linarith), max_eq_left h]
      ring
    · rw [max_eq_right (by linarith : -(f : Lp ℝ 2 μ) x - c ≤ 0)]
      ring
  have horth : D.form.E T (f - T) = 0 := by
    rw [hdec, map_sub, hP, hM, sub_zero]
  have h := D.form.energy_add_add T (f - T)
  rw [add_sub_cancel, horth, mul_zero, add_zero] at h
  exact h

/--
density of 𝔻 ∩ L^∞ in 𝔻 for the ℰ₁ norm (BH uses it without stating it, proofs of 4.1.3 and 6.1.1,
pp. 17 and 36): Tₙ(f) = (−n) ∨ (f ∧ n) → f in L² and ℰ(f − Tₙ f) → 0.
-/
theorem tendsto_clamp (f : D.form.dom) :
    Tendsto (fun n : ℕ => ((D.clamp (-(n : ℝ)) n f : D.form.dom) : Lp ℝ 2 μ)) atTop
        (𝓝 (f : Lp ℝ 2 μ)) ∧
      Tendsto (fun n : ℕ => D.form.E (f - D.clamp (-(n : ℝ)) n f)
        (f - D.clamp (-(n : ℝ)) n f)) atTop (𝓝 0) := by
  have hL : Tendsto (fun n : ℕ => ((D.clamp (-(n : ℝ)) n f : D.form.dom) : Lp ℝ 2 μ)) atTop
      (𝓝 (f : Lp ℝ 2 μ)) := by
    have h0 : Tendsto (fun n : ℕ => ((D.clamp (-(n : ℝ)) n f : D.form.dom) : Lp ℝ 2 μ) -
        (f : Lp ℝ 2 μ)) atTop (𝓝 0) := by
      apply lp_two_tendsto_zero_of_dominated _ (f : Lp ℝ 2 μ)
      · intro n
        filter_upwards [Lp.coeFn_sub ((D.clamp (-(n : ℝ)) n f : D.form.dom) : Lp ℝ 2 μ)
          (f : Lp ℝ 2 μ), D.coeFn_clamp (-(n : ℝ)) n f] with x a b
        rw [a, Pi.sub_apply, b]
        exact abs_clamp_sub_le (Nat.cast_nonneg n) _
      · have hall : ∀ᵐ x ∂μ, ∀ n : ℕ,
            (((D.clamp (-(n : ℝ)) n f : D.form.dom) : Lp ℝ 2 μ) - (f : Lp ℝ 2 μ)) x =
              max (-(n : ℝ)) (min ((f : Lp ℝ 2 μ) x) n) - (f : Lp ℝ 2 μ) x := by
          rw [ae_all_iff]
          intro n
          filter_upwards [Lp.coeFn_sub ((D.clamp (-(n : ℝ)) n f : D.form.dom) : Lp ℝ 2 μ)
            (f : Lp ℝ 2 μ), D.coeFn_clamp (-(n : ℝ)) n f] with x a b
          rw [a, Pi.sub_apply, b]
        filter_upwards [hall] with x hx
        simp only [hx]
        apply tendsto_atTop_of_eventually_const (i₀ := ⌈|(f : Lp ℝ 2 μ) x|⌉₊)
        intro n hn
        have hn' : |(f : Lp ℝ 2 μ) x| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
        rw [min_eq_left (abs_le.1 hn').2, max_eq_right (abs_le.1 hn').1, sub_self]
    have h := h0.add_const (f : Lp ℝ 2 μ)
    simp only [sub_add_cancel, zero_add] at h
    exact h
  refine ⟨hL, ?_⟩
  have hle : ∀ n : ℕ, D.form.E (D.clamp (-(n : ℝ)) n f) (D.clamp (-(n : ℝ)) n f) ≤
      D.form.E f f := fun n => D.energy_clamp_le _ _ f
  have hlim := D.closed.energy_le_liminf hL ⟨D.form.E f f, (Eventually.of_forall hle).frequently⟩
    f.2
  simp only [Subtype.coe_eta] at hlim
  have hbdd : IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => D.form.E (D.clamp (-(n : ℝ)) n f) (D.clamp (-(n : ℝ)) n f)) :=
    isBoundedUnder_of ⟨0, fun n => D.form.nonneg _⟩
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha (D.form.nonneg _),
    fun a ha => ?_⟩
  have hev := eventually_lt_of_lt_liminf (show D.form.E f f - a < liminf
    (fun n : ℕ => D.form.E (D.clamp (-(n : ℝ)) n f) (D.clamp (-(n : ℝ)) n f)) atTop by
      linarith) hbdd
  filter_upwards [hev] with n hn
  have := D.energy_eq_clamp_add (Nat.cast_nonneg n) f
  linarith

end LocalDirichletForm
end ErrorCalculus

namespace ErrorCalculus

/-! ## F (excerpt). Connection to the `Capacity.DirichletForm` framework -/

namespace LocalDirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (D : LocalDirichletForm μ)

/--
connection to `Capacity.DirichletForm` framework univariate normal contractions operate
(`exists_mem_of_lipschitzWith`, K = 1), which this framework takes as a field (BH I.3.3.1, p = 1).
Same form, same domain.
-/
def toDirichletForm : Capacity.DirichletForm μ where
  form := D.form
  closed := D.closed
  contraction {F} hF _ u w hw := by
    obtain ⟨hd, he⟩ := D.exists_mem_of_lipschitzWith hF u w hw
    refine ⟨hd, ?_⟩
    simpa using he

/-- Density axiom (i) gives density of 𝔻 → L². -/
theorem denseRange_toLp : DenseRange D.toDirichletForm.toLp := by
  have hr : Set.range D.toDirichletForm.toLp = (D.form.dom : Set (Lp ℝ 2 μ)) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      rw [Capacity.DirichletForm.toLp_apply]
      exact (D.form.formToDomain x).2
    · intro hv
      refine ⟨D.form.formToDomain.symm ⟨v, hv⟩, ?_⟩
      rw [Capacity.DirichletForm.toLp_apply]
      change ((D.form.formToDomain (D.form.formToDomain.symm ⟨v, hv⟩) : D.form.dom) :
        Lp ℝ 2 μ) = v
      rw [LinearEquiv.apply_symm_apply]
  rw [DenseRange, hr]
  exact D.dense

/--
test functions (BH 1991, proof of 4.1.3, p. 17, using density (i) and
`ae_eq_of_integral_mul_eq`): if k ∈ L¹ and ∫ h k dμ = 0 for every essentially bounded h ∈ 𝔻, then k
= 0 a.e.
-/
theorem ae_eq_zero_of_integral_mul_eq_zero (k : Lp ℝ 1 μ)
    (hk : ∀ h : D.form.dom, (∃ C : ℝ, ∀ᵐ x ∂μ, |(h : Lp ℝ 2 μ) x| ≤ C) →
      ∫ x, (h : Lp ℝ 2 μ) x * k x ∂μ = 0) : ⇑k =ᵐ[μ] 0 := by
  have h := D.toDirichletForm.ae_eq_of_integral_mul_eq D.denseRange_toLp
    (L1.integrable_coeFn k) (integrable_zero Ω ℝ μ) (fun z hz => ?_)
  · exact h
  · rw [Capacity.DirichletForm.mem_bddSpace, Capacity.DirichletForm.toLp_apply] at hz
    rw [Capacity.DirichletForm.toLp_apply, hk _ hz]
    simp

end LocalDirichletForm
end ErrorCalculus
