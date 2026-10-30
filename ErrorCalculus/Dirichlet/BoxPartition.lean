import ErrorCalculus.Dirichlet.LocalCarreDuChampChain

/-!
# hat functions, grid partition of unity, approximants and uniform estimates

## Main results
Real-variable part (without a Dirichlet form) of to clause (b) of `BHFunctionalCalculus` (BH 1991,
th. I.6.1.2 and cor. I.6.1.3, pp. 36–37):

* Hat functions θ_a expressed by two clamps (`gridHat`) and their chosen slopes (`gridHatSlope`,
indicators of open grid cells, zero at nodes: the slopes from `clampRule`).
* Partition of unity for a grid of spacing δ on [a, a + Kδ], then on the box [a, a + Kδ]ᵐ
(`sum_gridHat_eq_one`, `sum_cellWeight_eq_one`), and zero sum of slopes, including at nodes
(`sum_gridHatSlope_eq_zero`, `sum_cellSlope_eq_zero`).
* Approximants G_δ(y) = Σ_k φ_k(y) L_k(y) and coefficients cᵢ^δ (`boxApprox`, `boxApproxCoeff`).
* Uniform estimates (`exists_abs_boxApproxCoeff_sub_le`): for F of class C¹ (`ContDiff ℝ 1 F`),
|cᵢ^δ − ∂ᵢF| ≤ 3ε and |G_δ − F| ≤ εδ on the box when δ ≤ δ₀(ε).

The module imports `LocalCarreDuChampChain` solely to reuse `abs_interpSlope_le` in
`sum_indicator_Ioo_le_one`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option maxHeartbeats 800000

namespace ErrorCalculus

/-! ## A. Real hat functions, grid partition of unity (real-variable parts of 3.2–3.3) -/

/--
Hat function with peak at a and half-width δ, expressed by two clamps: θ(t) = ((a − δ) ∨ (t ∧ a) − a
∨ (t ∧ (a + δ)) + δ)/δ.
-/
def gridHat (a δ t : ℝ) : ℝ := (max (a - δ) (min t a) - max a (min t (a + δ)) + δ) / δ

/--
Chosen slope of the hat function (given by `clampRule`): (1_{]a − δ, a[}(t) − 1_{]a, a + δ[}(t))/δ;
it is 0 at nodes a − δ, a, a + δ.
-/
def gridHatSlope (a δ t : ℝ) : ℝ :=
  ((Set.Ioo (a - δ) a).indicator 1 t - (Set.Ioo a (a + δ)).indicator 1 t) / δ

/-- θ ≥ 0 (δ > 0). -/
theorem gridHat_nonneg {δ : ℝ} (hδ : 0 < δ) (a t : ℝ) : 0 ≤ gridHat a δ t := by
  have h3 : -δ ≤ max (a - δ) (min t a) - max a (min t (a + δ)) := by
    rcases le_total t a with h | h
    · rw [max_eq_left ((min_le_left _ _).trans h)]
      linarith [le_max_left (a - δ) (min t a)]
    · rw [min_eq_right h, max_eq_right (by linarith : a - δ ≤ a)]
      linarith [max_le (by linarith : a ≤ a + δ) (min_le_right t (a + δ))]
  unfold gridHat
  rw [le_div_iff₀ hδ]
  linarith

/-- θ ≤ 1 (δ > 0). -/
theorem gridHat_le_one {δ : ℝ} (hδ : 0 < δ) (a t : ℝ) : gridHat a δ t ≤ 1 := by
  have h1 : max (a - δ) (min t a) ≤ a := max_le (by linarith) (min_le_right _ _)
  have h2 : a ≤ max a (min t (a + δ)) := le_max_left _ _
  unfold gridHat
  rw [div_le_iff₀ hδ]
  linarith

/-- For 0 ≤ δ, θ vanishes outside ]a − δ, a + δ[: δ ≤ |t − a| ⇒ θ(t) = 0. -/
theorem gridHat_eq_zero_of_le_abs {a δ t : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ |t - a|) :
    gridHat a δ t = 0 := by
  unfold gridHat
  rcases le_abs.1 h with h' | h'
  · rw [min_eq_right (by linarith : a ≤ t), max_eq_right (by linarith : a - δ ≤ a),
      min_eq_right (by linarith : a + δ ≤ t), max_eq_right (by linarith : a ≤ a + δ)]
    ring
  · rw [min_eq_left (by linarith : t ≤ a), max_eq_left (by linarith : t ≤ a - δ),
      min_eq_left (by linarith : t ≤ a + δ), max_eq_left (by linarith : t ≤ a)]
    ring

/-- The chosen slope vanishes outside ]a − δ, a + δ[. -/
theorem gridHatSlope_eq_zero_of_le_abs {a δ t : ℝ} (h : δ ≤ |t - a|) : gridHatSlope a δ t = 0 := by
  unfold gridHatSlope
  rw [Set.indicator_of_notMem, Set.indicator_of_notMem, sub_zero, zero_div]
  · intro hm
    rcases le_abs.1 h with h' | h' <;> linarith [hm.1, hm.2]
  · intro hm
    rcases le_abs.1 h with h' | h' <;> linarith [hm.1, hm.2]

/--
partition of unity on a grid in ℝ: for δ > 0, K ∈ ℕ and a ≤ t ≤ a + Kδ, Σ_{k ≤ K} θ_{a + kδ}(t) = 1
(θ_c = `gridHat c δ`).
-/
theorem sum_gridHat_eq_one {a δ : ℝ} (hδ : 0 < δ) (K : ℕ) {t : ℝ} (h1 : a ≤ t)
    (h2 : t ≤ a + K * δ) :
    ∑ k ∈ Finset.range (K + 1), gridHat (a + k * δ) δ t = 1 := by
  set c : ℕ → ℝ := fun k => max (a + k * δ - δ) (min t (a + k * δ)) with hc
  have e : ∀ k : ℕ, gridHat (a + k * δ) δ t = (c k - c (k + 1) + δ) / δ := by
    intro k
    have e2 : a + ((k + 1 : ℕ) : ℝ) * δ = a + k * δ + δ := by push_cast; ring
    simp only [gridHat, hc, e2, add_sub_cancel_right]
  have hc0 : c 0 = a := by
    simp only [hc, Nat.cast_zero, zero_mul, add_zero]
    rw [min_eq_right h1, max_eq_right (by linarith)]
  have hcK : c (K + 1) = a + K * δ := by
    have e2 : a + ((K + 1 : ℕ) : ℝ) * δ = a + K * δ + δ := by push_cast; ring
    simp only [hc, e2, add_sub_cancel_right]
    rw [min_eq_left (by linarith), max_eq_left h2]
  rw [Finset.sum_congr rfl (fun k _ => e k), ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_range_sub', Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc0, hcK,
    div_eq_one_iff_eq hδ.ne']
  push_cast
  ring

/--
sum of slopes: for K ∈ ℕ and a ≤ t ≤ a + Kδ, Σ_{k ≤ K} θ′_{a + kδ}(t) = 0, including at nodes (θ′_c
= `gridHatSlope c δ`; no assumption on δ: the sum telescopes).
-/
theorem sum_gridHatSlope_eq_zero {a δ : ℝ} (K : ℕ) {t : ℝ} (h1 : a ≤ t)
    (h2 : t ≤ a + K * δ) :
    ∑ k ∈ Finset.range (K + 1), gridHatSlope (a + k * δ) δ t = 0 := by
  set g : ℕ → ℝ := fun k => (Set.Ioo (a + k * δ - δ) (a + k * δ)).indicator 1 t with hg
  have e : ∀ k : ℕ, gridHatSlope (a + k * δ) δ t = (g k - g (k + 1)) / δ := by
    intro k
    have e2 : a + ((k + 1 : ℕ) : ℝ) * δ = a + k * δ + δ := by push_cast; ring
    simp only [gridHatSlope, hg, e2, add_sub_cancel_right]
  have hg0 : g 0 = 0 := by
    simp only [hg, Nat.cast_zero, zero_mul, add_zero]
    exact Set.indicator_of_notMem (fun h => by linarith [h.2]) _
  have hgK : g (K + 1) = 0 := by
    have e2 : a + ((K + 1 : ℕ) : ℝ) * δ = a + K * δ + δ := by push_cast; ring
    simp only [hg, e2, add_sub_cancel_right]
    exact Set.indicator_of_notMem (fun h => by linarith [h.1]) _
  rw [Finset.sum_congr rfl (fun k _ => e k), ← Finset.sum_div, Finset.sum_range_sub', hg0, hgK,
    sub_zero, zero_div]

/-- Node of cell k in the product grid of spacing δ starting at a. -/
def gridNode {m K : ℕ} (a δ : ℝ) (k : Fin m → Fin (K + 1)) : Fin m → ℝ :=
  fun i => a + ((k i : ℕ) : ℝ) * δ

/-- Weight of cell k: φ_k(y) = Πⱼ θ_{kⱼ}(yⱼ). -/
def cellWeight {m K : ℕ} (a δ : ℝ) (k : Fin m → Fin (K + 1)) (y : Fin m → ℝ) : ℝ :=
  ∏ j, gridHat (gridNode a δ k j) δ (y j)

/--
Chosen slope of φ_k in direction i: ∂ᵢφ_k(y) = θ′_{kᵢ}(yᵢ) Π_{j ≠ i} θ_{kⱼ}(yⱼ), written as a
product over all j.
-/
def cellSlope {m K : ℕ} (a δ : ℝ) (k : Fin m → Fin (K + 1)) (i : Fin m) (y : Fin m → ℝ) : ℝ :=
  ∏ j, if j = i then gridHatSlope (gridNode a δ k j) δ (y j) else gridHat (gridNode a δ k j) δ (y j)

/--
partition of unity on the box: for δ > 0 and y ∈ [a, a + Kδ]ᵐ, Σ_k φ_k(y) = 1, where the sum ranges
over k : {1..m} → {0..K} (φ_k = `cellWeight a δ k`).
-/
theorem sum_cellWeight_eq_one {m K : ℕ} {a δ : ℝ} (hδ : 0 < δ) {y : Fin m → ℝ}
    (hy : ∀ j, a ≤ y j ∧ y j ≤ a + K * δ) :
    ∑ k : Fin m → Fin (K + 1), cellWeight a δ k y = 1 := by
  have h := Fintype.prod_sum (fun (j : Fin m) (l : Fin (K + 1)) =>
    gridHat (a + ((l : ℕ) : ℝ) * δ) δ (y j))
  simp only [cellWeight, gridNode]
  rw [← h]
  refine Finset.prod_eq_one fun j _ => ?_
  exact (Fin.sum_univ_eq_sum_range (fun l : ℕ => gridHat (a + (l : ℝ) * δ) δ (y j)) (K + 1)).trans
    (sum_gridHat_eq_one hδ K (hy j).1 (hy j).2)

/--
sum of slopes on the box: for y ∈ [a, a + Kδ]ᵐ and every direction i, Σ_k ∂ᵢφ_k(y) = 0, including at
nodes (∂ᵢφ_k = `cellSlope a δ k i`; no assumption on δ).
-/
theorem sum_cellSlope_eq_zero {m K : ℕ} {a δ : ℝ} {y : Fin m → ℝ}
    (hy : ∀ j, a ≤ y j ∧ y j ≤ a + K * δ) (i : Fin m) :
    ∑ k : Fin m → Fin (K + 1), cellSlope a δ k i y = 0 := by
  have h := Fintype.prod_sum (fun (j : Fin m) (l : Fin (K + 1)) =>
    if j = i then gridHatSlope (a + ((l : ℕ) : ℝ) * δ) δ (y j)
    else gridHat (a + ((l : ℕ) : ℝ) * δ) δ (y j))
  simp only [cellSlope, gridNode]
  rw [← h]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp only [↓reduceIte]
  exact (Fin.sum_univ_eq_sum_range (fun l : ℕ => gridHatSlope (a + (l : ℝ) * δ) δ (y i))
    (K + 1)).trans
    (sum_gridHatSlope_eq_zero K (hy i).1 (hy i).2)

/-- Affine approximation in cell k: L_k(y) = A_k + Σᵢ B_{k,i} (yᵢ − x_{k,i}). -/
def cellAffine {m K : ℕ} (a δ : ℝ) (A : (Fin m → Fin (K + 1)) → ℝ)
    (B : (Fin m → Fin (K + 1)) → Fin m → ℝ) (k : Fin m → Fin (K + 1)) (y : Fin m → ℝ) : ℝ :=
  A k + ∑ i, B k i * (y i - gridNode a δ k i)

/-- Approximant: G_δ(y) = Σ_k φ_k(y) L_k(y). -/
def boxApprox {m K : ℕ} (a δ : ℝ) (A : (Fin m → Fin (K + 1)) → ℝ)
    (B : (Fin m → Fin (K + 1)) → Fin m → ℝ) (y : Fin m → ℝ) : ℝ :=
  ∑ k, cellWeight a δ k y * cellAffine a δ A B k y

/-- Coefficients: cᵢ^δ(y) = Σ_k (∂ᵢφ_k(y) L_k(y) + φ_k(y) B_{k,i}). -/
def boxApproxCoeff {m K : ℕ} (a δ : ℝ) (A : (Fin m → Fin (K + 1)) → ℝ)
    (B : (Fin m → Fin (K + 1)) → Fin m → ℝ) (i : Fin m) (y : Fin m → ℝ) : ℝ :=
  ∑ k, (cellSlope a δ k i y * cellAffine a δ A B k y + cellWeight a δ k y * B k i)

/-- |L(y)| ≤ |A| + Σᵢ |Bᵢ| (M + |x₀ᵢ|) if |yᵢ| ≤ M for every i. -/
theorem abs_affine_le {m : ℕ} (A : ℝ) (B x₀ y : Fin m → ℝ) {M : ℝ} (hy : ∀ i, |y i| ≤ M) :
    |A + ∑ i, B i * (y i - x₀ i)| ≤ |A| + ∑ i, |B i| * (M + |x₀ i|) := by
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hy i) le_rfl)) (abs_nonneg _)

/--
algebraic identity (values): for δ > 0, arbitrary data A_k, B_{k,i}, y ∈ [a, a + Kδ]ᵐ and any real
Φ, G_δ(y) − Φ = Σ_k φ_k(y) (L_k(y) − Φ).
-/
theorem boxApprox_sub_eq {m K : ℕ} {a δ : ℝ} (hδ : 0 < δ) (A : (Fin m → Fin (K + 1)) → ℝ)
    (B : (Fin m → Fin (K + 1)) → Fin m → ℝ) {y : Fin m → ℝ}
    (hy : ∀ j, a ≤ y j ∧ y j ≤ a + K * δ) (Φ : ℝ) :
    boxApprox a δ A B y - Φ = ∑ k, cellWeight a δ k y * (cellAffine a δ A B k y - Φ) := by
  have h1 := sum_cellWeight_eq_one (K := K) hδ hy
  simp only [boxApprox, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]

/--
algebraic identity (coefficients): for δ > 0, arbitrary data A_k, B_{k,i}, y ∈ [a, a + Kδ]ᵐ, every
direction i and all reals Φ and g, cᵢ^δ(y) − g = Σ_k ∂ᵢφ_k(y) (L_k(y) − Φ) + Σ_k φ_k(y) (B_{k,i} −
g) (Σ_k ∂ᵢφ_k = 0 and Σ_k φ_k = 1).
-/
theorem boxApproxCoeff_sub_eq {m K : ℕ} {a δ : ℝ} (hδ : 0 < δ) (A : (Fin m → Fin (K + 1)) → ℝ)
    (B : (Fin m → Fin (K + 1)) → Fin m → ℝ) {y : Fin m → ℝ}
    (hy : ∀ j, a ≤ y j ∧ y j ≤ a + K * δ) (i : Fin m) (Φ g : ℝ) :
    boxApproxCoeff a δ A B i y - g =
      ∑ k, cellSlope a δ k i y * (cellAffine a δ A B k y - Φ) +
        ∑ k, cellWeight a δ k y * (B k i - g) := by
  have h1 := sum_cellWeight_eq_one (K := K) hδ hy
  have h2 := sum_cellSlope_eq_zero (K := K) hy i
  simp only [boxApproxCoeff, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, h1, h2]
  ring

/-! ## B. Uniform estimates -/

/--
The open cells of a grid are disjoint: Σ_{k < N} 1_{]a + kδ, a + (k + 1)δ[}(t) ≤ 1 (reuse of
`abs_interpSlope_le`, for F = id).
-/
theorem sum_indicator_Ioo_le_one (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range N, (Set.Ioo (a + k * δ) (a + (k + 1) * δ)).indicator (1 : ℝ → ℝ) t ≤ 1 := by
  have h := abs_interpSlope_le (F := fun s => s) zero_le_one (fun x y => (one_mul _).ge) a hδ N t
  have e : interpSlope (fun s => s) a δ N t =
      ∑ k ∈ Finset.range N, (Set.Ioo (a + k * δ) (a + (k + 1) * δ)).indicator (1 : ℝ → ℝ) t := by
    unfold interpSlope
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show a + (k + 1) * δ - (a + k * δ) = δ by ring, div_self hδ.ne', one_mul]
  rw [e] at h
  exact (le_abs_self _).trans h

/-- Σ_{k ≤ K} |θ′_{a + kδ}(t)| ≤ 2/δ for every t (δ > 0). -/
theorem sum_abs_gridHatSlope_le (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (K : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range (K + 1), |gridHatSlope (a + k * δ) δ t| ≤ 2 / δ := by
  have h1 := sum_indicator_Ioo_le_one (a - δ) hδ (K + 1) t
  have h2 := sum_indicator_Ioo_le_one a hδ (K + 1) t
  have e1 : ∀ k : ℕ, Set.Ioo (a - δ + k * δ) (a - δ + (k + 1) * δ) =
      Set.Ioo (a + k * δ - δ) (a + k * δ) := fun k => by congr 1 <;> ring
  have e2 : ∀ k : ℕ, Set.Ioo (a + k * δ) (a + (k + 1) * δ) =
      Set.Ioo (a + k * δ) (a + k * δ + δ) := fun k => by congr 1; ring
  simp only [e1] at h1
  simp only [e2] at h2
  have hn : ∀ s : Set ℝ, 0 ≤ s.indicator (1 : ℝ → ℝ) t :=
    fun s => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hk : ∀ k ∈ Finset.range (K + 1), |gridHatSlope (a + k * δ) δ t| ≤
      ((Set.Ioo (a + k * δ - δ) (a + k * δ)).indicator 1 t +
        (Set.Ioo (a + k * δ) (a + k * δ + δ)).indicator 1 t) / δ := by
    intro k _
    unfold gridHatSlope
    rw [abs_div, abs_of_pos hδ]
    apply div_le_div_of_nonneg_right _ hδ.le
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (hn _), abs_of_nonneg (hn _)]
  refine (Finset.sum_le_sum hk).trans ?_
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ hδ.le
  linarith

/-- φ_k ≥ 0 (δ > 0). -/
theorem cellWeight_nonneg {m K : ℕ} {a δ : ℝ} (hδ : 0 < δ) (k : Fin m → Fin (K + 1))
    (y : Fin m → ℝ) : 0 ≤ cellWeight a δ k y :=
  Finset.prod_nonneg fun _ _ => gridHat_nonneg hδ _ _

/-- Localization for 0 ≤ δ: if φ_k(y) ≠ 0, then |yⱼ − x_{k,j}| < δ for every j. -/
theorem abs_sub_gridNode_lt_of_cellWeight_ne_zero {m K : ℕ} {a δ : ℝ} (hδ : 0 ≤ δ)
    {k : Fin m → Fin (K + 1)} {y : Fin m → ℝ} (h : cellWeight a δ k y ≠ 0) (j : Fin m) :
    |y j - gridNode a δ k j| < δ := by
  by_contra hc
  unfold cellWeight at h
  exact h (Finset.prod_eq_zero (Finset.mem_univ j) (gridHat_eq_zero_of_le_abs hδ (not_lt.1 hc)))

/-- Localization for 0 ≤ δ: if ∂ᵢφ_k(y) ≠ 0, then |yⱼ − x_{k,j}| < δ for every j. -/
theorem abs_sub_gridNode_lt_of_cellSlope_ne_zero {m K : ℕ} {a δ : ℝ} (hδ : 0 ≤ δ)
    {k : Fin m → Fin (K + 1)} {i : Fin m} {y : Fin m → ℝ} (h : cellSlope a δ k i y ≠ 0)
    (j : Fin m) : |y j - gridNode a δ k j| < δ := by
  by_contra hc
  unfold cellSlope at h
  apply h
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  split_ifs
  · exact gridHatSlope_eq_zero_of_le_abs (not_lt.1 hc)
  · exact gridHat_eq_zero_of_le_abs hδ (not_lt.1 hc)

/-- On the box, Σ_k |∂ᵢφ_k(y)| ≤ 2/δ (factorization, Σ_l θ_l = 1 in directions j ≠ i). -/
theorem sum_abs_cellSlope_le {m K : ℕ} {a δ : ℝ} (hδ : 0 < δ) {y : Fin m → ℝ}
    (hy : ∀ j, a ≤ y j ∧ y j ≤ a + K * δ) (i : Fin m) :
    ∑ k : Fin m → Fin (K + 1), |cellSlope a δ k i y| ≤ 2 / δ := by
  have h := Fintype.prod_sum (fun (j : Fin m) (l : Fin (K + 1)) =>
    |if j = i then gridHatSlope (a + ((l : ℕ) : ℝ) * δ) δ (y j)
      else gridHat (a + ((l : ℕ) : ℝ) * δ) δ (y j)|)
  simp only [cellSlope, gridNode, Finset.abs_prod]
  rw [← h, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have ha : ∀ c t : ℝ, |gridHat c δ t| = gridHat c δ t :=
    fun c t => abs_of_nonneg (gridHat_nonneg hδ c t)
  have e : ∀ j ∈ Finset.univ.erase i, (∑ l : Fin (K + 1),
      |if j = i then gridHatSlope (a + ((l : ℕ) : ℝ) * δ) δ (y j)
        else gridHat (a + ((l : ℕ) : ℝ) * δ) δ (y j)|) = 1 := by
    intro j hj
    simp only [if_neg (Finset.ne_of_mem_erase hj), ha]
    exact (Fin.sum_univ_eq_sum_range (fun l : ℕ => gridHat (a + (l : ℝ) * δ) δ (y j)) (K + 1)).trans
      (sum_gridHat_eq_one hδ K (hy j).1 (hy j).2)
  rw [Finset.prod_congr rfl e, Finset.prod_const_one, mul_one]
  simp only [↓reduceIte]
  exact (Fin.sum_univ_eq_sum_range (fun l : ℕ => |gridHatSlope (a + (l : ℝ) * δ) δ (y i)|)
    (K + 1)).le.trans (sum_abs_gridHatSlope_le a hδ K (y i))

/--
Mean value estimate: if ‖y − x‖ ≤ r and ‖DF(z) − DF(x)‖ ≤ ε on the closed ball B(x, r), then |F(x) +
Σᵢ ∂ᵢF(x)(yᵢ − xᵢ) − F(y)| ≤ ε r.
-/
theorem abs_affine_sub_le_of_fderiv {m : ℕ} {F : (Fin m → ℝ) → ℝ} (hF : Differentiable ℝ F)
    {x y : Fin m → ℝ} {r ε : ℝ} (hxy : ‖y - x‖ ≤ r)
    (hε : ∀ z ∈ Metric.closedBall x r, ‖fderiv ℝ F z - fderiv ℝ F x‖ ≤ ε) :
    |F x + ∑ i, fderiv ℝ F x (Pi.single i 1) * (y i - x i) - F y| ≤ ε * r := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hxy
  have hx : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr
  have hy : y ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hxy
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε x hx)
  have hmv := (convex_closedBall x r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hF z).hasFDerivAt.hasFDerivWithinAt) hε hx hy
  have hsum : ∑ i, fderiv ℝ F x (Pi.single i 1) * (y i - x i) = fderiv ℝ F x (y - x) := by
    have h := LinearMap.pi_apply_eq_sum_univ (fderiv ℝ F x : (Fin m → ℝ) →ₗ[ℝ] ℝ) (y - x)
    rw [ContinuousLinearMap.coe_coe] at h
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (fun j : Fin m => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
      funext j
      rw [Pi.single_apply]
      exact if_congr eq_comm rfl rfl
    rw [e, smul_eq_mul, mul_comm, Pi.sub_apply]
  rw [hsum, show F x + fderiv ℝ F x (y - x) - F y = -(F y - F x - fderiv ℝ F x (y - x)) by ring,
    abs_neg, ← Real.norm_eq_abs]
  exact hmv.trans (mul_le_mul_of_nonneg_left hxy hε0)

/--
For F : ℝᵐ → ℝ of class C¹ (`ContDiff ℝ 1 F`, with no Lipschitz assumption), real a, b and ε > 0,
there exists δ₀ > 0 such that, for every K ∈ ℕ and δ ∈ ]0, δ₀] with a + Kδ ≤ b, using the data A_k =
F(x_k) and B_{k,i} = ∂ᵢF(x_k) = DF(x_k)(eᵢ) (x_k = `gridNode a δ k`, eᵢ = `Pi.single i 1`), at every
point y of the box [a, a + Kδ]ᵐ: |cᵢ^δ(y) − ∂ᵢF(y)| ≤ 3ε for every i and |G_δ(y) − F(y)| ≤ εδ.
-/
theorem exists_abs_boxApproxCoeff_sub_le {m : ℕ} {F : (Fin m → ℝ) → ℝ} (hC : ContDiff ℝ 1 F)
    (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ (K : ℕ) (δ : ℝ), 0 < δ → δ ≤ δ₀ → a + K * δ ≤ b → ∀ y : Fin m → ℝ,
      (∀ j, a ≤ y j ∧ y j ≤ a + K * δ) →
      (∀ i, |boxApproxCoeff (K := K) a δ (fun k => F (gridNode a δ k))
          (fun k i => fderiv ℝ F (gridNode a δ k) (Pi.single i 1)) i y -
            fderiv ℝ F y (Pi.single i 1)| ≤ 3 * ε) ∧
      |boxApprox (K := K) a δ (fun k => F (gridNode a δ k))
          (fun k i => fderiv ℝ F (gridNode a δ k) (Pi.single i 1)) y - F y| ≤ ε * δ := by
  set S : Set (Fin m → ℝ) := Set.univ.pi fun _ => Set.Icc (a - 1) (b + 1) with hS
  have hSc : IsCompact S := isCompact_univ_pi fun _ => isCompact_Icc
  have hcont : Continuous (fderiv ℝ F) := hC.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ F := hC.differentiable one_ne_zero
  obtain ⟨η, hη, hU⟩ := Metric.uniformContinuousOn_iff.1
    (hSc.uniformContinuousOn_of_continuous hcont.continuousOn) ε hε
  refine ⟨min (η / 2) 1, lt_min (half_pos hη) one_pos, fun K δ hδ hδ₀ hKb y hy => ?_⟩
  have hδη : δ < η := lt_of_le_of_lt (hδ₀.trans (min_le_left _ _)) (half_lt_self hη)
  have hδ1 : δ ≤ 1 := hδ₀.trans (min_le_right _ _)
  set A : (Fin m → Fin (K + 1)) → ℝ := fun k => F (gridNode a δ k) with hA
  set B : (Fin m → Fin (K + 1)) → Fin m → ℝ :=
    fun k i => fderiv ℝ F (gridNode a δ k) (Pi.single i 1) with hB
  have hnode : ∀ (k : Fin m → Fin (K + 1)) (j : Fin m),
      a ≤ gridNode a δ k j ∧ gridNode a δ k j ≤ b := by
    intro k j
    have hk : ((k j : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 (k j).2
    have h0 : 0 ≤ ((k j : ℕ) : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
    have h1 : ((k j : ℕ) : ℝ) * δ ≤ K * δ := mul_le_mul_of_nonneg_right hk hδ.le
    simp only [gridNode]
    constructor <;> linarith
  have hball : ∀ k : Fin m → Fin (K + 1), ∀ z ∈ Metric.closedBall (gridNode a δ k) δ,
      ‖fderiv ℝ F z - fderiv ℝ F (gridNode a δ k)‖ ≤ ε := by
    intro k z hz
    have hzS : z ∈ S := by
      rw [hS, Set.mem_univ_pi]
      intro j
      have h1 : |z j - gridNode a δ k j| ≤ δ := by
        have h := norm_le_pi_norm (z - gridNode a δ k) j
        rw [Pi.sub_apply, Real.norm_eq_abs] at h
        exact h.trans (by rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hz)
      obtain ⟨h2, h3⟩ := hnode k j
      rw [abs_le] at h1
      rw [Set.mem_Icc]
      constructor <;> linarith [h1.1, h1.2]
    have hxS : gridNode a δ k ∈ S := by
      rw [hS, Set.mem_univ_pi]
      intro j
      obtain ⟨h2, h3⟩ := hnode k j
      rw [Set.mem_Icc]
      constructor <;> linarith
    rw [← dist_eq_norm]
    exact (hU z hzS _ hxS (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) hδη)).le
  have hnorm : ∀ k : Fin m → Fin (K + 1), (∀ j, |y j - gridNode a δ k j| < δ) →
      ‖y - gridNode a δ k‖ ≤ δ := fun k h =>
    (pi_norm_le_iff_of_nonneg hδ.le).2 fun j => by
      rw [Pi.sub_apply, Real.norm_eq_abs]
      exact (h j).le
  have hL : ∀ k : Fin m → Fin (K + 1), (∀ j, |y j - gridNode a δ k j| < δ) →
      |cellAffine a δ A B k y - F y| ≤ ε * δ :=
    fun k h => abs_affine_sub_le_of_fderiv hdiff (hnorm k h) (hball k)
  have hBk : ∀ k : Fin m → Fin (K + 1), (∀ j, |y j - gridNode a δ k j| < δ) → ∀ i,
      |B k i - fderiv ℝ F y (Pi.single i 1)| ≤ ε := by
    intro k h i
    have hyb : y ∈ Metric.closedBall (gridNode a δ k) δ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hnorm k h
    have h1 := hball k y hyb
    rw [show B k i - fderiv ℝ F y (Pi.single i 1) =
        (fderiv ℝ F (gridNode a δ k) - fderiv ℝ F y) (Pi.single i 1) by
      simp only [hB]; simp, ← Real.norm_eq_abs]
    calc ‖(fderiv ℝ F (gridNode a δ k) - fderiv ℝ F y) (Pi.single i 1)‖
        ≤ ‖fderiv ℝ F (gridNode a δ k) - fderiv ℝ F y‖ * ‖(Pi.single i 1 : Fin m → ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ F y - fderiv ℝ F (gridNode a δ k)‖ := by
          rw [Pi.norm_single, norm_one, mul_one, norm_sub_rev]
      _ ≤ ε := h1
  have hW := sum_cellWeight_eq_one (K := K) hδ hy
  constructor
  · intro i
    rw [boxApproxCoeff_sub_eq hδ A B hy i (F y) (fderiv ℝ F y (Pi.single i 1))]
    have t1 : ∀ k : Fin m → Fin (K + 1),
        |cellSlope a δ k i y * (cellAffine a δ A B k y - F y)| ≤
          |cellSlope a δ k i y| * (ε * δ) := by
      intro k
      rw [abs_mul]
      by_cases h0 : cellSlope a δ k i y = 0
      · rw [h0, abs_zero, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left
          (hL k (abs_sub_gridNode_lt_of_cellSlope_ne_zero hδ.le h0)) (abs_nonneg _)
    have t2 : ∀ k : Fin m → Fin (K + 1),
        |cellWeight a δ k y * (B k i - fderiv ℝ F y (Pi.single i 1))| ≤
          cellWeight a δ k y * ε := by
      intro k
      rw [abs_mul, abs_of_nonneg (cellWeight_nonneg hδ k y)]
      by_cases h0 : cellWeight a δ k y = 0
      · rw [h0, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left
          (hBk k (abs_sub_gridNode_lt_of_cellWeight_ne_zero hδ.le h0) i)
          (cellWeight_nonneg hδ k y)
    have hs1 := sum_abs_cellSlope_le (K := K) hδ hy i
    calc _ ≤ |∑ k, cellSlope a δ k i y * (cellAffine a δ A B k y - F y)| +
          |∑ k, cellWeight a δ k y * (B k i - fderiv ℝ F y (Pi.single i 1))| := abs_add_le _ _
      _ ≤ ∑ k, |cellSlope a δ k i y| * (ε * δ) + ∑ k, cellWeight a δ k y * ε :=
          add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => t1 k))
            ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => t2 k))
      _ = (∑ k, |cellSlope a δ k i y|) * (ε * δ) + (∑ k, cellWeight a δ k y) * ε := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ 2 / δ * (ε * δ) + 1 * ε := by
          rw [hW]
          exact add_le_add (mul_le_mul_of_nonneg_right hs1 (by positivity)) le_rfl
      _ = 3 * ε := by
          field_simp
          ring
  · rw [boxApprox_sub_eq hδ A B hy (F y)]
    have t3 : ∀ k : Fin m → Fin (K + 1),
        |cellWeight a δ k y * (cellAffine a δ A B k y - F y)| ≤ cellWeight a δ k y * (ε * δ) := by
      intro k
      rw [abs_mul, abs_of_nonneg (cellWeight_nonneg hδ k y)]
      by_cases h0 : cellWeight a δ k y = 0
      · rw [h0, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left
          (hL k (abs_sub_gridNode_lt_of_cellWeight_ne_zero hδ.le h0)) (cellWeight_nonneg hδ k y)
    calc _ ≤ ∑ k, cellWeight a δ k y * (ε * δ) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => t3 k)
      _ = ε * δ := by rw [← Finset.sum_mul, hW, one_mul]

end ErrorCalculus
