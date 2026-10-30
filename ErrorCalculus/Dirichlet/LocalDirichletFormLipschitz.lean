import ErrorCalculus.Dirichlet.LocalDirichletForm
import ErrorCalculus.Dirichlet.ExtensionLp
import ErrorCalculus.Dirichlet.LowerSemicontinuous

/-!
# piecewise affine interpolation and univariate Lipschitz calculus

## Main results
BH 1991, prop. I.3.3.1 (p. 14) for p = 1 and exercise 3.1 (pp. 14–15), proved for a
`LocalDirichletForm` using locality (L₂) in place of the semigroup: the piecewise affine interpolant
of F ∘ f is a combination of ℰ-orthogonal clamps, with energy at most K² ℰ(f); it converges to F ∘
f in L², and closedness concludes (`exists_mem_of_lipschitzWith`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option maxHeartbeats 800000

namespace ErrorCalculus

/-! ## B. Piecewise affine interpolation and univariate Lipschitz calculus -/

/-- Joining two adjacent clamps. -/
theorem clamp_add_clamp {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (t : ℝ) :
    max a (min t b) + max b (min t c) - b = max a (min t c) := by
  rcases le_total t b with h | h
  · rw [min_eq_left h, max_eq_left ((min_le_left t c).trans h), min_eq_left (h.trans hbc)]
    ring
  · rw [min_eq_right h, max_eq_right hab, max_eq_right (le_min h hbc),
      max_eq_right (le_trans hab (le_min h hbc))]
    ring

/-- Telescoping sum of clamps on the grid a + kδ. -/
theorem sum_clamp_telescope (a : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range N, (max (a + k * δ) (min x (a + (k + 1) * δ)) - (a + k * δ)) =
      max a (min x (a + N * δ)) - a := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, add_zero]
    rw [max_eq_left (min_le_right x a), sub_self]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h0 : (0 : ℝ) ≤ N * δ := mul_nonneg (Nat.cast_nonneg N) hδ
    have h1 : a ≤ a + N * δ := by linarith
    have h2 : a + N * δ ≤ a + (N + 1) * δ := by nlinarith
    have := clamp_add_clamp h1 h2 x
    linarith

/--
Interpolation sum: Σₖ sₖ ((tₖ ∨ (x ∧ tₖ₊₁)) − tₖ) on the grid tₖ = a + kδ, with slopes sₖ = (F(tₖ₊₁)
− F(tₖ))/δ.
-/
def interpSum (F : ℝ → ℝ) (a δ : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, (F (a + (k + 1) * δ) - F (a + k * δ)) / δ *
    (max (a + k * δ) (min x (a + (k + 1) * δ)) - (a + k * δ))

/--
Properties of the interpolant F(a) + interpSum: equal to F(a) to the left of the grid, equal to F(a
+ Nδ) to the right, and within 2Lδ of F on [a, a + Nδ].
-/
theorem interpSum_spec (F : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ x y, |F x - F y| ≤ L * |x - y|) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    (∀ x, x ≤ a → interpSum F a δ N x = 0) ∧
    (∀ x, a + N * δ ≤ x → F a + interpSum F a δ N x = F (a + N * δ)) ∧
    (∀ x, a ≤ x → x ≤ a + N * δ → |F a + interpSum F a δ N x - F x| ≤ 2 * L * δ) := by
  induction N with
  | zero =>
    refine ⟨fun x _ => by simp [interpSum], fun x _ => by simp [interpSum], fun x h1 h2 => ?_⟩
    have hx : x = a := le_antisymm (by simpa using h2) h1
    subst hx
    simp only [interpSum, Finset.range_zero, Finset.sum_empty, add_zero, sub_self, abs_zero]
    positivity
  | succ N ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have hs : ∀ x, interpSum F a δ (N + 1) x = interpSum F a δ N x +
        (F (a + (N + 1) * δ) - F (a + N * δ)) / δ *
          (max (a + N * δ) (min x (a + (N + 1) * δ)) - (a + N * δ)) := by
      intro x
      simp only [interpSum, Finset.sum_range_succ]
    have h0 : (0 : ℝ) ≤ N * δ := mul_nonneg (Nat.cast_nonneg N) hδ.le
    have ha : a ≤ a + N * δ := by linarith
    have hNN : a + N * δ ≤ a + (N + 1) * δ := by nlinarith
    push_cast
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx1 hx2 => ?_⟩
    · rw [hs, i1 x hx, max_eq_left ((min_le_left _ _).trans (hx.trans ha))]
      ring
    · rw [hs, ← add_assoc, i2 x (hNN.trans hx), min_eq_right hx, max_eq_right hNN]
      field_simp
      ring
    · rcases le_total x (a + N * δ) with h | h
      · rw [hs, max_eq_left ((min_le_left _ _).trans h), sub_self, mul_zero, add_zero]
        exact i3 x hx1 h
      · rw [hs, ← add_assoc, i2 x h, min_eq_left hx2, max_eq_right h]
        have hsl : |(F (a + (N + 1) * δ) - F (a + N * δ)) / δ| ≤ L := by
          rw [abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
          have h3 := hF (a + (N + 1) * δ) (a + N * δ)
          have e : |a + (N + 1) * δ - (a + N * δ)| = δ := by
            rw [show a + (N + 1) * δ - (a + N * δ) = δ by ring, abs_of_pos hδ]
          rw [e] at h3
          linarith
        have h1 := hF (a + N * δ) x
        have hxd : |a + N * δ - x| ≤ δ := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith
        have hxd2 : |x - (a + N * δ)| ≤ δ := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        have key : F (a + N * δ) + (F (a + (N + 1) * δ) - F (a + N * δ)) / δ * (x - (a + N * δ))
            - F x = (F (a + N * δ) - F x) +
              (F (a + (N + 1) * δ) - F (a + N * δ)) / δ * (x - (a + N * δ)) := by ring
        rw [key]
        calc _ ≤ |F (a + N * δ) - F x| +
              |(F (a + (N + 1) * δ) - F (a + N * δ)) / δ * (x - (a + N * δ))| :=
              abs_add_le _ _
          _ = |F (a + N * δ) - F x| +
              |(F (a + (N + 1) * δ) - F (a + N * δ)) / δ| * |x - (a + N * δ)| := by
              rw [abs_mul]
          _ ≤ L * δ + L * δ := add_le_add (h1.trans (mul_le_mul_of_nonneg_left hxd hL))
              (mul_le_mul hsl hxd2 (abs_nonneg _) hL)
          _ = 2 * L * δ := by ring

/-- Starting point of the n-th grid: −(n + 1). -/
def gridStart (n : ℕ) : ℝ := -((n : ℝ) + 1)

/-- Spacing of the n-th grid: 1/(n + 1). -/
def gridStep (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Number of cells in the n-th grid: 2(n + 1)². -/
def gridCount (n : ℕ) : ℕ := 2 * (n + 1) ^ 2

/-- Every grid spacing in the interpolation sequence is strictly positive. -/
theorem gridStep_pos (n : ℕ) : 0 < gridStep n := by
  unfold gridStep
  positivity

/-- The n-th grid covers [−(n + 1), n + 1]. -/
theorem gridStart_add_gridCount_mul_gridStep (n : ℕ) :
    gridStart n + gridCount n * gridStep n = (n : ℝ) + 1 := by
  unfold gridStart gridCount gridStep
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/--
Interpolation error on the n-th grid: at most 2L + L|x| everywhere, and at most 2L/(n + 1) for |x| ≤
n + 1.
-/
theorem abs_add_interpSum_grid_sub_le (F : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x y, |F x - F y| ≤ L * |x - y|)
    (n : ℕ) (x : ℝ) :
    |F (gridStart n) + interpSum F (gridStart n) (gridStep n) (gridCount n) x - F x| ≤
        2 * L + L * |x| ∧
      (|x| ≤ (n : ℝ) + 1 →
        |F (gridStart n) + interpSum F (gridStart n) (gridStep n) (gridCount n) x - F x| ≤
          2 * L * gridStep n) := by
  obtain ⟨i1, i2, i3⟩ := interpSum_spec F hL hF (gridStart n) (gridStep_pos n) (gridCount n)
  have he := gridStart_add_gridCount_mul_gridStep n
  have hst : gridStep n ≤ 1 := by
    unfold gridStep
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hs0 := gridStep_pos n
  have hmid : ∀ y, |y| ≤ (n : ℝ) + 1 →
      |F (gridStart n) + interpSum F (gridStart n) (gridStep n) (gridCount n) y - F y| ≤
        2 * L * gridStep n := by
    intro y hy
    have hy' := abs_le.1 hy
    apply i3 y
    · unfold gridStart
      linarith
    · rw [he]
      linarith
  refine ⟨?_, hmid x⟩
  rcases le_or_gt x (gridStart n) with h | h
  · rw [i1 x h, add_zero]
    have hx0 : x < 0 := by
      unfold gridStart at h
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h1 := hF (gridStart n) x
    have h2 : |gridStart n - x| ≤ |x| := by
      rw [abs_of_nonneg (by linarith), abs_of_neg hx0]
      unfold gridStart
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hL, abs_nonneg x]
  · rcases le_or_gt x ((n : ℝ) + 1) with h' | h'
    · have hm := hmid x (abs_le.2 ⟨by unfold gridStart at h; linarith, h'⟩)
      nlinarith [abs_nonneg x]
    · rw [i2 x (by rw [he]; exact h'.le), he]
      have h1 := hF ((n : ℝ) + 1) x
      have h2 : |(n : ℝ) + 1 - x| ≤ |x| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_of_pos (by linarith)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      nlinarith [mul_le_mul_of_nonneg_left h2 hL, abs_nonneg x]

/-- Pointwise convergence of the interpolant to F. -/
theorem tendsto_add_interpSum_grid_sub (F : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ x y, |F x - F y| ≤ L * |x - y|) (x : ℝ) :
    Tendsto (fun n => F (gridStart n) +
      interpSum F (gridStart n) (gridStep n) (gridCount n) x - F x) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 2 * L * gridStep n) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 * L)
    rw [mul_zero] at h
    exact h
  apply squeeze_zero_norm' _ hlim
  obtain ⟨N, hN⟩ := exists_nat_ge |x|
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Real.norm_eq_abs]
  apply (abs_add_interpSum_grid_sub_le F hL hF n x).2
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- Energy of a sum of pairwise ℰ-orthogonal vectors. -/
theorem QuadForm.energy_sum_of_orth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Q : QuadForm H) {ι : Type*} (s : Finset ι) (c : ι → Q.dom) (r : ι → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Q.E (c i) (c j) = 0) :
    Q.E (∑ i ∈ s, r i • c i) (∑ i ∈ s, r i • c i) = ∑ i ∈ s, r i ^ 2 * Q.E (c i) (c i) := by
  classical
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji => by rw [h j hj i hi hji]; ring)]
  ring

namespace LocalDirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (D : LocalDirichletForm μ)

/-- The clamps on the grid a + kδ are pairwise ℰ-orthogonal. -/
theorem energy_clamp_grid_eq_zero (a : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (f : D.form.dom) {i j : ℕ}
    (hij : i ≠ j) : D.form.E (D.clamp (a + i * δ) (a + (i + 1) * δ) f)
      (D.clamp (a + j * δ) (a + (j + 1) * δ) f) = 0 := by
  have step : ∀ {p q : ℕ}, p < q → D.form.E (D.clamp (a + p * δ) (a + (p + 1) * δ) f)
      (D.clamp (a + q * δ) (a + (q + 1) * δ) f) = 0 := by
    intro p q hpq
    have hq : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
    apply D.energy_clamp_clamp_eq_zero
    · nlinarith
    · nlinarith
    · nlinarith
  rcases lt_or_gt_of_ne hij with h | h
  · exact step h
  · rw [D.form.symm]
    exact step h

/--
The piecewise affine interpolant as an element of 𝔻: a combination of grid clamps and the constant
1.
-/
def interpElem (F : ℝ → ℝ) (a δ : ℝ) (N : ℕ) (f : D.form.dom) : D.form.dom :=
  ∑ k ∈ Finset.range N, ((F (a + (k + 1) * δ) - F (a + k * δ)) / δ) •
      D.clamp (a + k * δ) (a + (k + 1) * δ) f +
    (F a - ∑ k ∈ Finset.range N, (F (a + (k + 1) * δ) - F (a + k * δ)) / δ * (a + k * δ)) •
      D.one

/-- Representative of the sum Σₖ rₖ cₖ of elements of 𝔻. -/
theorem coeFn_sum_smul {ι : Type*} (s : Finset ι) (r : ι → ℝ) (c : ι → D.form.dom) :
    ⇑((∑ i ∈ s, r i • c i : D.form.dom) : Lp ℝ 2 μ) =ᵐ[μ]
      fun x => ∑ i ∈ s, r i * (c i : Lp ℝ 2 μ) x := by
  rw [Submodule.coe_sum]
  have h := lp_coeFn_sum s (fun i => ((r i • c i : D.form.dom) : Lp ℝ 2 μ))
  have h2 : ∀ᵐ x ∂μ, ∀ i ∈ s, ((r i • c i : D.form.dom) : Lp ℝ 2 μ) x =
      r i * (c i : Lp ℝ 2 μ) x :=
    (Filter.eventually_all_finset s).2 fun i _ => D.coeFn_smul_dom (c i) (r i)
  filter_upwards [h, h2] with x hx hx2
  rw [hx]
  exact Finset.sum_congr rfl hx2

/-- Representative of the interpolant: F(a) + interpSum ∘ f. -/
theorem coeFn_interpElem (F : ℝ → ℝ) (a δ : ℝ) (N : ℕ) (f : D.form.dom) :
    ⇑((D.interpElem F a δ N f : D.form.dom) : Lp ℝ 2 μ) =ᵐ[μ]
      fun x => F a + interpSum F a δ N ((f : Lp ℝ 2 μ) x) := by
  have h2 : ∀ᵐ x ∂μ, ∀ k ∈ Finset.range N,
      ((D.clamp (a + k * δ) (a + (k + 1) * δ) f : D.form.dom) : Lp ℝ 2 μ) x =
        max (a + k * δ) (min ((f : Lp ℝ 2 μ) x) (a + (k + 1) * δ)) :=
    (Filter.eventually_all_finset _).2 fun k _ => D.coeFn_clamp _ _ f
  rw [interpElem]
  filter_upwards [D.coeFn_add_smul_one _ _, D.coeFn_sum_smul _ _ _, h2] with x h1 h3 h4
  rw [h1, h3, Finset.sum_congr rfl fun k hk => by rw [h4 k hk]]
  simp only [interpSum, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Sum of grid clamps: the clamp to [a, a + Nδ] up to a constant. -/
theorem sum_clamp_eq (a : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) (f : D.form.dom) :
    ∑ k ∈ Finset.range N, (1 : ℝ) • D.clamp (a + k * δ) (a + (k + 1) * δ) f =
      D.clamp a (a + N * δ) f + (∑ k ∈ Finset.range N, (a + k * δ) - a) • D.one := by
  apply QuadForm.dom_ext_ae
  have h2 : ∀ᵐ x ∂μ, ∀ k ∈ Finset.range N,
      ((D.clamp (a + k * δ) (a + (k + 1) * δ) f : D.form.dom) : Lp ℝ 2 μ) x =
        max (a + k * δ) (min ((f : Lp ℝ 2 μ) x) (a + (k + 1) * δ)) :=
    (Filter.eventually_all_finset _).2 fun k _ => D.coeFn_clamp _ _ f
  filter_upwards [D.coeFn_sum_smul _ _ _, h2, D.coeFn_add_smul_one _ _,
    D.coeFn_clamp a (a + N * δ) f] with x h1 h3 h4 h5
  rw [h1, h4, h5, Finset.sum_congr rfl fun k hk => by rw [h3 k hk]]
  have ht := sum_clamp_telescope a hδ N ((f : Lp ℝ 2 μ) x)
  rw [Finset.sum_sub_distrib] at ht
  simp only [one_mul]
  linarith

/-- Energy of the interpolant: at most L² ℰ(f) if the slopes are bounded by L. -/
theorem energy_interpElem_le (F : ℝ → ℝ) {L : ℝ}
    (hF : ∀ x y, |F x - F y| ≤ L * |x - y|) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (f : D.form.dom) :
    D.form.E (D.interpElem F a δ N f) (D.interpElem F a δ N f) ≤ L ^ 2 * D.form.E f f := by
  have horth : ∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N, i ≠ j →
      D.form.E (D.clamp (a + i * δ) (a + (i + 1) * δ) f)
        (D.clamp (a + j * δ) (a + (j + 1) * δ) f) = 0 :=
    fun i _ j _ hij => D.energy_clamp_grid_eq_zero a hδ.le f hij
  rw [interpElem, D.energy_add_smul_one, QuadForm.energy_sum_of_orth _ _ _ _ horth]
  have hsl : ∀ k : ℕ, ((F (a + (k + 1) * δ) - F (a + k * δ)) / δ) ^ 2 ≤ L ^ 2 := by
    intro k
    have h3 := hF (a + (k + 1) * δ) (a + k * δ)
    have e : |a + (k + 1) * δ - (a + k * δ)| = δ := by
      rw [show a + (k + 1) * δ - (a + k * δ) = δ by ring, abs_of_pos hδ]
    rw [e] at h3
    have h4 : |(F (a + (k + 1) * δ) - F (a + k * δ)) / δ| ≤ L := by
      rw [abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
      linarith
    exact sq_le_sq' (abs_le.1 h4).1 (abs_le.1 h4).2
  have hsum := QuadForm.energy_sum_of_orth D.form (Finset.range N)
    (fun k => D.clamp (a + k * δ) (a + (k + 1) * δ) f) (fun _ => (1 : ℝ)) horth
  rw [D.sum_clamp_eq a hδ.le N f, D.energy_add_smul_one] at hsum
  simp only [one_pow, one_mul] at hsum
  calc ∑ k ∈ Finset.range N, ((F (a + (k + 1) * δ) - F (a + k * δ)) / δ) ^ 2 *
        D.form.E (D.clamp (a + k * δ) (a + (k + 1) * δ) f)
          (D.clamp (a + k * δ) (a + (k + 1) * δ) f)
      ≤ ∑ k ∈ Finset.range N, L ^ 2 * D.form.E (D.clamp (a + k * δ) (a + (k + 1) * δ) f)
          (D.clamp (a + k * δ) (a + (k + 1) * δ) f) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hsl k) (D.form.nonneg _)
    _ = L ^ 2 * D.form.E (D.clamp a (a + N * δ) f) (D.clamp a (a + N * δ) f) := by
        rw [← Finset.mul_sum, hsum]
    _ ≤ L ^ 2 * D.form.E f f :=
        mul_le_mul_of_nonneg_left (D.energy_clamp_le _ _ f) (sq_nonneg L)

/--
BH 1991, prop. I.3.3.1 (p. 14) for p = 1 and exercise 3.1 (pp. 14–15: under (M), T₁⁰ replaced by
T₁), proved here using locality (L₂) in place of the semigroup; arbitrary Lipschitz constant K
(functions in Λ₁, BH 5.1.1).

If F : ℝ → ℝ is K-Lipschitz and f ∈ 𝔻, every class w of F ∘ f lies in 𝔻 and ℰ(w) ≤ K² ℰ(f).
-/
theorem exists_mem_of_lipschitzWith {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F)
    (f : D.form.dom) (w : Lp ℝ 2 μ) (hw : ⇑w =ᵐ[μ] fun x => F ((f : Lp ℝ 2 μ) x)) :
    ∃ hw' : w ∈ D.form.dom, D.form.E ⟨w, hw'⟩ ⟨w, hw'⟩ ≤ (K : ℝ) ^ 2 * D.form.E f f := by
  have hK : (0 : ℝ) ≤ K := K.2
  have hF' : ∀ x y, |F x - F y| ≤ (K : ℝ) * |x - y| := by
    intro x y
    have h := hF.dist_le_mul x y
    rwa [Real.dist_eq, Real.dist_eq] at h
  set W : ℕ → D.form.dom := fun n =>
    D.interpElem F (gridStart n) (gridStep n) (gridCount n) f with hW
  have hE : ∀ n, D.form.E (W n) (W n) ≤ (K : ℝ) ^ 2 * D.form.E f f := fun n =>
    D.energy_interpElem_le F hF' _ (gridStep_pos n) _ f
  set g : Lp ℝ 2 μ := (2 * (K : ℝ)) • ((D.one : D.form.dom) : Lp ℝ 2 μ) +
    (K : ℝ) • |(f : Lp ℝ 2 μ)| with hg
  have hgx : ⇑g =ᵐ[μ] fun x => 2 * (K : ℝ) + (K : ℝ) * |(f : Lp ℝ 2 μ) x| := by
    filter_upwards [Lp.coeFn_add ((2 * (K : ℝ)) • ((D.one : D.form.dom) : Lp ℝ 2 μ))
      ((K : ℝ) • |(f : Lp ℝ 2 μ)|), Lp.coeFn_smul (2 * (K : ℝ)) ((D.one : D.form.dom) : Lp ℝ 2 μ),
      Lp.coeFn_smul (K : ℝ) |(f : Lp ℝ 2 μ)|, D.coeFn_one, Lp.coeFn_abs (f : Lp ℝ 2 μ)]
      with x h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, h5, smul_eq_mul, smul_eq_mul,
      mul_one]
  have hT0 : Tendsto (fun n => ((W n : D.form.dom) : Lp ℝ 2 μ) - w) atTop (𝓝 0) := by
    apply lp_two_tendsto_zero_of_dominated _ g
    · intro n
      filter_upwards [Lp.coeFn_sub ((W n : D.form.dom) : Lp ℝ 2 μ) w,
        D.coeFn_interpElem F (gridStart n) (gridStep n) (gridCount n) f, hw, hgx]
        with x h1 h2 h3 h4
      rw [h1, Pi.sub_apply, h2, h3, h4,
        abs_of_nonneg (show (0 : ℝ) ≤ 2 * (K : ℝ) + (K : ℝ) * |(f : Lp ℝ 2 μ) x| by positivity)]
      exact (abs_add_interpSum_grid_sub_le F hK hF' n _).1
    · have hall : ∀ᵐ x ∂μ, ∀ n : ℕ,
          (((W n : D.form.dom) : Lp ℝ 2 μ) - w) x =
            F (gridStart n) + interpSum F (gridStart n) (gridStep n) (gridCount n)
              ((f : Lp ℝ 2 μ) x) - F ((f : Lp ℝ 2 μ) x) := by
        rw [ae_all_iff]
        intro n
        filter_upwards [Lp.coeFn_sub ((W n : D.form.dom) : Lp ℝ 2 μ) w,
          D.coeFn_interpElem F (gridStart n) (gridStep n) (gridCount n) f, hw] with x h1 h2 h3
        rw [h1, Pi.sub_apply, h2, h3]
      filter_upwards [hall] with x hx
      simp only [hx]
      exact tendsto_add_interpSum_grid_sub F hK hF' _
  have hT : Tendsto (fun n => ((W n : D.form.dom) : Lp ℝ 2 μ)) atTop (𝓝 w) := by
    have h := hT0.add_const w
    simp only [sub_add_cancel, zero_add] at h
    exact h
  exact D.closed.mem_dom_of_tendsto_of_energy_le hT hE

end LocalDirichletForm
end ErrorCalculus
