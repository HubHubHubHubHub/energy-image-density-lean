import ErrorCalculus.Dirichlet.BoxPartition

/-!
# chain-rule predicate, finite products, hat functions, approximants; `ChainRule` for m = 1

## Main results
For a local Dirichlet form `D : LocalDirichletForm μ` equipped with its carre du champ `G :
D.CarreDuChamp` (ℰ(f, f) = ∫ γ(f, f) dμ), using the proved `clampRule` and `leibnizRule`, toward
clause (b) of `BHFunctionalCalculus` (BH 1991, th. I.6.1.2 and cor. I.6.1.3, pp. 36–37; contract
`ChainRule`):

* Predicate `GammaChain u Φ c`: "Φ(u) is represented in 𝔻 and γ(Φ(u), v) = Σᵢ cᵢ(u) γ(uᵢ, v)",
stable under constants, coordinates, sums, scalar multiples and products of bounded factors
(`GammaChain.mul`, `GammaChain.finsetProd`: iterated Leibniz).
* Dimension-m part `ChainRuleDim m` of the contract (`chainRule_iff_forall_chainRuleDim`, by
`Iff.rfl`) and format reduction `chainRuleDim_of_gammaChain` (format part).
* **The m = 1 case of the contract in its exact format** (`chainRuleDim_one`), by the univariate
chain rule (`exists_mem_gamma_comp`).
* Hat functions by `clampRule` (`gammaChain_gridHat`,), cell weights (`gammaChain_cellWeight`,),
approximants G_δ(u) ∈ 𝔻 with γ(G_δ(u), v) = Σᵢ cᵢ^δ(u) γ(uᵢ, v) (`gammaChain_boxApprox`,).

The multivariate `ChainRule` is proved in `LocalCarreDuChampChainRule` and connected to
`BHFunctionalCalculus` by `DprBridge.ChainRuleBridge`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option maxHeartbeats 800000

namespace ErrorCalculus

namespace LocalDirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {D : LocalDirichletForm μ}

namespace CarreDuChamp
variable (G : D.CarreDuChamp)

/-! ## C. Chain-rule predicate, dimension-m part of the contract -/

/--
"Φ(u) lies in 𝔻 with γ(Φ(u), v) = Σᵢ cᵢ(u) γ(uᵢ, v)": there exists p ∈ 𝔻 equal a.e. to Φ(u) such
that, for every v ∈ 𝔻, γ(p, v) = Σᵢ cᵢ(u) γ(uᵢ, v) a.e.
-/
def GammaChain {m : ℕ} (u : Fin m → D.form.dom) (Φ : (Fin m → ℝ) → ℝ)
    (c : Fin m → (Fin m → ℝ) → ℝ) : Prop :=
  ∃ p : D.form.dom, (⇑(p : Lp ℝ 2 μ) =ᵐ[μ] fun x => Φ fun j => (u j : Lp ℝ 2 μ) x) ∧
    ∀ v : D.form.dom, ⇑(G.gamma p v) =ᵐ[μ]
      fun x => ∑ i, c i (fun j => (u j : Lp ℝ 2 μ) x) * G.gamma (u i) v x

/-- Dimension-m part of the `ChainRule` contract : the same statement, with fixed m. -/
def ChainRuleDim (m : ℕ) : Prop :=
  ∀ (u : Fin m → D.form.dom) (F : (Fin m → ℝ) → ℝ) (L : ℝ≥0),
    ContDiff ℝ 1 F → LipschitzWith L F →
    ∀ w : Lp ℝ 2 μ, (⇑w =ᵐ[μ] fun x => F (fun i => (u i : Lp ℝ 2 μ) x)) →
      ∃ hw : w ∈ D.form.dom, ∀ v : D.form.dom, ⇑(G.gamma ⟨w, hw⟩ v) =ᵐ[μ] fun x =>
        ∑ i, fderiv ℝ F (fun j => (u j : Lp ℝ 2 μ) x) (Pi.single i 1) * G.gamma (u i) v x

/--
`G.ChainRule ↔ ∀ m > 0, G.ChainRuleDim m`: the contract is the conjunction of its parts in
dimensions m > 0 (`Iff.rfl`, definitional equality).
Reference: Bouleau–Hirsch (1991), th. I.6.1.2 and cor. I.6.1.3.
-/
theorem chainRule_iff_forall_chainRuleDim : G.ChainRule ↔ ∀ m, 0 < m → G.ChainRuleDim m :=
  Iff.rfl

section GammaChainAPI
variable {G} {m : ℕ} {u : Fin m → D.form.dom}

/--
If `GammaChain u Φ c`, every class w ∈ L² equal a.e. to Φ(u) lies in 𝔻 and, for every v ∈ 𝔻, γ(w, v)
= Σᵢ cᵢ(u) γ(uᵢ, v) a.e.
-/
theorem GammaChain.exists_mem {Φ : (Fin m → ℝ) → ℝ} {c : Fin m → (Fin m → ℝ) → ℝ}
    (h : G.GammaChain u Φ c) (w : Lp ℝ 2 μ)
    (hw : ⇑w =ᵐ[μ] fun x => Φ fun j => (u j : Lp ℝ 2 μ) x) :
    ∃ hw' : w ∈ D.form.dom, ∀ v : D.form.dom, ⇑(G.gamma ⟨w, hw'⟩ v) =ᵐ[μ]
      fun x => ∑ i, c i (fun j => (u j : Lp ℝ 2 μ) x) * G.gamma (u i) v x := by
  obtain ⟨p, hp, hγ⟩ := h
  have e : w = (p : Lp ℝ 2 μ) := Lp.ext (hw.trans hp.symm)
  subst e
  exact ⟨p.2, hγ⟩

/-- Change of presentation of Φ and the coefficients. -/
theorem GammaChain.congr {Φ Φ' : (Fin m → ℝ) → ℝ} {c c' : Fin m → (Fin m → ℝ) → ℝ}
    (h : G.GammaChain u Φ c) (hΦ : ∀ y, Φ y = Φ' y) (hc : ∀ i y, c i y = c' i y) :
    G.GammaChain u Φ' c' := by
  have e1 : Φ = Φ' := funext hΦ
  have e2 : c = c' := funext fun i => funext (hc i)
  subst e1 e2
  exact h

/-- Sum of two chain-rule expressions. -/
theorem GammaChain.add {Φ₁ Φ₂ : (Fin m → ℝ) → ℝ} {c₁ c₂ : Fin m → (Fin m → ℝ) → ℝ}
    (h₁ : G.GammaChain u Φ₁ c₁) (h₂ : G.GammaChain u Φ₂ c₂) :
    G.GammaChain u (fun y => Φ₁ y + Φ₂ y) (fun i y => c₁ i y + c₂ i y) := by
  obtain ⟨p₁, hp₁, hγ₁⟩ := h₁
  obtain ⟨p₂, hp₂, hγ₂⟩ := h₂
  refine ⟨p₁ + p₂, ?_, fun v => ?_⟩
  · filter_upwards [Lp.coeFn_add (p₁ : Lp ℝ 2 μ) (p₂ : Lp ℝ 2 μ), hp₁, hp₂] with x h h1 h2
    rw [Submodule.coe_add, h, Pi.add_apply, h1, h2]
  · rw [map_add, LinearMap.add_apply]
    filter_upwards [Lp.coeFn_add (G.gamma p₁ v) (G.gamma p₂ v), hγ₁ v, hγ₂ v] with x h h1 h2
    rw [h, Pi.add_apply, h1, h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Scalar multiple of a chain-rule expression. -/
theorem GammaChain.const_mul {Φ : (Fin m → ℝ) → ℝ} {c : Fin m → (Fin m → ℝ) → ℝ}
    (h : G.GammaChain u Φ c) (r : ℝ) :
    G.GammaChain u (fun y => r * Φ y) (fun i y => r * c i y) := by
  obtain ⟨p, hp, hγ⟩ := h
  refine ⟨r • p, ?_, fun v => ?_⟩
  · filter_upwards [D.coeFn_smul_dom p r, hp] with x h1 h2
    rw [h1, h2]
  · rw [map_smul, LinearMap.smul_apply]
    filter_upwards [Lp.coeFn_smul r (G.gamma p v), hγ v] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/--
product of two bounded chain-rule expressions: if `GammaChain u Φ₁ c₁`, `GammaChain u Φ₂ c₂`,
|Φ₁(u)| ≤ C₁ and |Φ₂(u)| ≤ C₂ a.e., then Φ₁(u) Φ₂(u) has the chain rule γ(Φ₁(u) Φ₂(u), v) = Σᵢ (Φ₁
c₂ᵢ + Φ₂ c₁ᵢ)(u) γ(uᵢ, v).
-/
theorem GammaChain.mul {Φ₁ Φ₂ : (Fin m → ℝ) → ℝ} {c₁ c₂ : Fin m → (Fin m → ℝ) → ℝ}
    (h₁ : G.GammaChain u Φ₁ c₁) (h₂ : G.GammaChain u Φ₂ c₂) {C₁ C₂ : ℝ}
    (hb₁ : ∀ᵐ x ∂μ, |Φ₁ fun j => (u j : Lp ℝ 2 μ) x| ≤ C₁)
    (hb₂ : ∀ᵐ x ∂μ, |Φ₂ fun j => (u j : Lp ℝ 2 μ) x| ≤ C₂) :
    G.GammaChain u (fun y => Φ₁ y * Φ₂ y) (fun i y => Φ₁ y * c₂ i y + Φ₂ y * c₁ i y) := by
  obtain ⟨p₁, hp₁, hγ₁⟩ := h₁
  obtain ⟨p₂, hp₂, hγ₂⟩ := h₂
  have hB₁ : AEBounded (μ := μ) ((p₁ : Lp ℝ 2 μ) : Ω → ℝ) :=
    ⟨C₁, by filter_upwards [hp₁, hb₁] with x h1 h2; rw [Real.norm_eq_abs, h1]; exact h2⟩
  have hB₂ : AEBounded (μ := μ) ((p₂ : Lp ℝ 2 μ) : Ω → ℝ) :=
    ⟨C₂, by filter_upwards [hp₂, hb₂] with x h1 h2; rw [Real.norm_eq_abs, h1]; exact h2⟩
  obtain ⟨q, hq⟩ := D.exists_mul_mem_of_aeBounded hB₁ hB₂
  refine ⟨q, ?_, fun v => ?_⟩
  · filter_upwards [hq, hp₁, hp₂] with x h h1 h2
    rw [h, h1, h2]
  · filter_upwards [G.leibnizRule p₁ p₂ q v hB₁ hB₂ hq, hp₁, hp₂, hγ₁ v, hγ₂ v]
      with x h h1 h2 h3 h4
    rw [h, h1, h2, h3, h4, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

end GammaChainAPI

/-! ## D. Constants, coordinates, finite sums, finite products -/

/-- Constants: γ(r·1, v) = 0. -/
theorem gammaChain_const {m : ℕ} (u : Fin m → D.form.dom) (r : ℝ) :
    G.GammaChain u (fun _ => r) (fun _ _ => 0) := by
  refine ⟨r • D.one, ?_, fun v => ?_⟩
  · filter_upwards [D.coeFn_smul_dom D.one r, D.coeFn_one] with x h1 h2
    rw [h1, h2, mul_one]
  · rw [map_smul, LinearMap.smul_apply, G.gamma_one_left, smul_zero]
    filter_upwards [Lp.coeFn_zero ℝ 1 μ] with x hx
    rw [hx]
    simp

/-- Coordinates: Φ(y) = yᵢ, cⱼ = 1_{j = i}. -/
theorem gammaChain_coord {m : ℕ} (u : Fin m → D.form.dom) (i : Fin m) :
    G.GammaChain u (fun y => y i) (fun j _ => if j = i then 1 else 0) := by
  refine ⟨u i, Eventually.of_forall fun x => rfl, fun v => Eventually.of_forall fun x => ?_⟩
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Finite sums of chain-rule expressions. -/
theorem GammaChain.sum {m : ℕ} {u : Fin m → D.form.dom} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {Φ : ι → (Fin m → ℝ) → ℝ} {c : ι → Fin m → (Fin m → ℝ) → ℝ}
    (h : ∀ l ∈ s, G.GammaChain u (Φ l) (c l)) :
    G.GammaChain u (fun y => ∑ l ∈ s, Φ l y) (fun i y => ∑ l ∈ s, c l i y) := by
  induction s using Finset.induction_on with
  | empty => exact (G.gammaChain_const u 0).congr (fun y => by simp) (fun i y => by simp)
  | @insert b s hb ih =>
    have h' := (h b (Finset.mem_insert_self b s)).add
      (ih fun l hl => h l (Finset.mem_insert_of_mem hl))
    exact h'.congr (fun y => by rw [Finset.sum_insert hb]) (fun i y => by rw [Finset.sum_insert hb])

/--
finite products: if, for l ∈ s, `GammaChain u Φ_l c_l` and |Φ_l(u)| ≤ C_l a.e., then Π_{l ∈ s}
Φ_l(u) has chain-rule coefficients Σ_{l ∈ s} (Π_{l' ∈ s ∖ {l}} Φ_{l'}) c_l, and |Π_{l ∈ s} Φ_l(u)| ≤
Π_{l ∈ s} C_l a.e.
-/
theorem GammaChain.finsetProd {m : ℕ} {u : Fin m → D.form.dom} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {Φ : ι → (Fin m → ℝ) → ℝ} {c : ι → Fin m → (Fin m → ℝ) → ℝ} {C : ι → ℝ}
    (h : ∀ l ∈ s, G.GammaChain u (Φ l) (c l))
    (hb : ∀ l ∈ s, ∀ᵐ x ∂μ, |Φ l fun j => (u j : Lp ℝ 2 μ) x| ≤ C l) :
    G.GammaChain u (fun y => ∏ l ∈ s, Φ l y)
        (fun i y => ∑ l ∈ s, (∏ l' ∈ s.erase l, Φ l' y) * c l i y) ∧
      ∀ᵐ x ∂μ, |∏ l ∈ s, Φ l fun j => (u j : Lp ℝ 2 μ) x| ≤ ∏ l ∈ s, C l := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨(G.gammaChain_const u 1).congr (fun y => by simp) (fun i y => by simp), ?_⟩
    exact Eventually.of_forall fun x => by simp
  | @insert b s hbs ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun l hl => h l (Finset.mem_insert_of_mem hl))
      (fun l hl => hb l (Finset.mem_insert_of_mem hl))
    have hb' := hb b (Finset.mem_insert_self b s)
    refine ⟨((h b (Finset.mem_insert_self b s)).mul ih1 hb' ih2).congr
      (fun y => by rw [Finset.prod_insert hbs]) (fun i y => ?_), ?_⟩
    · have hsum : ∑ l ∈ s, (∏ l' ∈ (insert b s).erase l, Φ l' y) * c l i y =
          Φ b y * ∑ l ∈ s, (∏ l' ∈ s.erase l, Φ l' y) * c l i y := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [Finset.erase_insert_of_ne (by rintro rfl; exact hbs hl),
          Finset.prod_insert (fun e => hbs (Finset.mem_of_mem_erase e))]
        ring
      rw [Finset.sum_insert hbs, Finset.erase_insert hbs, hsum]
      ring
    · filter_upwards [hb', ih2] with x h1 h2
      rw [Finset.prod_insert hbs, Finset.prod_insert hbs, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

/--
For essentially bounded a₁, …, a_N ∈ 𝔻, the product Π aᵢ is represented in 𝔻 and, for every v ∈ 𝔻,
γ(Π aᵢ, v) = Σᵢ (Π_{j ≠ i} aⱼ) γ(aᵢ, v) a.e.
-/
theorem gammaChain_prod_coord {N : ℕ} (a : Fin N → D.form.dom)
    (ha : ∀ i, AEBounded (μ := μ) ((a i : Lp ℝ 2 μ) : Ω → ℝ)) :
    G.GammaChain a (fun y => ∏ i, y i) (fun i y => ∏ j ∈ Finset.univ.erase i, y j) := by
  choose C hC using ha
  have h := (GammaChain.finsetProd (G := G) (u := a) Finset.univ (Φ := fun l y => y l)
    (c := fun l j _ => if j = l then 1 else 0) (C := C) (fun l _ => G.gammaChain_coord a l)
    (fun l _ => by filter_upwards [hC l] with x hx; rwa [Real.norm_eq_abs] at hx)).1
  refine h.congr (fun y => rfl) (fun i y => ?_)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-! ## E. Hat functions and cell weights -/

/--
clamping a coordinate: for all real a, b, the expression a ∨ (uᵢ ∧ b) has the chain rule γ(a ∨ (uᵢ ∧
b), v) = 1_{]a, b[}(uᵢ) γ(uᵢ, v).
-/
theorem gammaChain_clamp {m : ℕ} (u : Fin m → D.form.dom) (i : Fin m) (a b : ℝ) :
    G.GammaChain u (fun y => max a (min (y i) b))
      (fun j y => if j = i then (Set.Ioo a b).indicator 1 (y i) else 0) := by
  refine ⟨D.clamp a b (u i), D.coeFn_clamp a b (u i), fun v => ?_⟩
  filter_upwards [G.clampRule (u i) v (D.clamp a b (u i)) a b (D.coeFn_clamp a b (u i))] with x h
  rw [h]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/--
a hat function of one coordinate: for all real a, δ (no assumption on δ), θ(uᵢ) has the chain rule
γ(θ(uᵢ), v) = θ′(uᵢ) γ(uᵢ, v), with θ = `gridHat a δ` and θ′ = `gridHatSlope a δ` (chosen slope,
zero at nodes).
-/
theorem gammaChain_gridHat {m : ℕ} (u : Fin m → D.form.dom) (i : Fin m) (a δ : ℝ) :
    G.GammaChain u (fun y => gridHat a δ (y i))
      (fun j y => if j = i then gridHatSlope a δ (y i) else 0) := by
  have h := (((G.gammaChain_clamp u i (a - δ) a).add
    ((G.gammaChain_clamp u i a (a + δ)).const_mul (-1))).add (G.gammaChain_const u δ)).const_mul δ⁻¹
  refine h.congr (fun y => ?_) (fun j y => ?_)
  · simp only [gridHat]
    ring
  · by_cases hj : j = i
    · simp only [if_pos hj, gridHatSlope]
      ring
    · simp only [if_neg hj]
      ring

/--
chain rule for weights: for δ > 0 and every cell k, the weight φ_k(u) = Πⱼ θ_{x_{k,j}}(uⱼ)
(`cellWeight`) has the chain rule γ(φ_k(u), v) = Σᵢ ∂ᵢφ_k(u) γ(uᵢ, v) (slopes `cellSlope`), and
|φ_k(u)| ≤ 1 a.e.
-/
theorem gammaChain_cellWeight {m K : ℕ} (u : Fin m → D.form.dom) {a δ : ℝ} (hδ : 0 < δ)
    (k : Fin m → Fin (K + 1)) :
    G.GammaChain u (cellWeight a δ k) (cellSlope a δ k) ∧
      ∀ᵐ x ∂μ, |cellWeight a δ k fun j => (u j : Lp ℝ 2 μ) x| ≤ 1 := by
  obtain ⟨h1, h2⟩ := GammaChain.finsetProd (G := G) (u := u) Finset.univ
    (Φ := fun l y => gridHat (gridNode a δ k l) δ (y l))
    (c := fun l j y => if j = l then gridHatSlope (gridNode a δ k l) δ (y l) else 0)
    (C := fun _ => 1) (fun l _ => G.gammaChain_gridHat u l _ δ)
    (fun l _ => Eventually.of_forall fun x =>
      (abs_of_nonneg (gridHat_nonneg hδ _ _)).le.trans (gridHat_le_one hδ _ _))
  refine ⟨h1.congr (fun y => rfl) (fun i y => ?_), ?_⟩
  · have e : ∀ j ∈ Finset.univ.erase i,
        (if j = i then gridHatSlope (gridNode a δ k j) δ (y j)
          else gridHat (gridNode a δ k j) δ (y j)) =
          gridHat (gridNode a δ k j) δ (y j) := fun j hj => if_neg (Finset.ne_of_mem_erase hj)
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [cellSlope, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      if_pos (rfl : i = i), Finset.prod_congr rfl e]
    ring
  · filter_upwards [h2] with x hx
    simpa only [cellWeight, Finset.prod_const_one] using hx

/-! ## F. Approximants -/

/-- Affine functions: γ(A + Σᵢ Bᵢ (uᵢ − x₀ᵢ), v) = Σᵢ Bᵢ γ(uᵢ, v). -/
theorem gammaChain_affine {m : ℕ} (u : Fin m → D.form.dom) (A : ℝ) (B x₀ : Fin m → ℝ) :
    G.GammaChain u (fun y => A + ∑ i, B i * (y i - x₀ i)) (fun j _ => B j) := by
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      G.GammaChain u (fun y => B i * (y i - x₀ i)) (fun j _ => B i * (if j = i then 1 else 0)) :=
    fun i _ => (((G.gammaChain_coord u i).add (G.gammaChain_const u (-x₀ i))).const_mul (B i)).congr
      (fun y => by ring) (fun j y => by ring)
  refine ((G.gammaChain_const u A).add (GammaChain.sum (G := G) Finset.univ hi)).congr
    (fun y => rfl) (fun j y => ?_)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, zero_add]

/--
approximants: for bounded u ∈ 𝔻ᵐ (|uᵢ| ≤ M a.e. for every i), δ > 0 and arbitrary data A_k, B_{k,i}
(no box hypothesis), the approximant G_δ(u) = Σ_k φ_k(u) L_k(u) (`boxApprox`) is represented in 𝔻
and γ(G_δ(u), v) = Σᵢ cᵢ^δ(u) γ(uᵢ, v), cᵢ^δ = Σ_k (∂ᵢφ_k L_k + φ_k B_{k,i}) (`boxApproxCoeff`).
-/
theorem gammaChain_boxApprox {m K : ℕ} (u : Fin m → D.form.dom) {M : ℝ}
    (hu : ∀ i, ∀ᵐ x ∂μ, |(u i : Lp ℝ 2 μ) x| ≤ M) {a δ : ℝ} (hδ : 0 < δ)
    (A : (Fin m → Fin (K + 1)) → ℝ) (B : (Fin m → Fin (K + 1)) → Fin m → ℝ) :
    G.GammaChain u (boxApprox a δ A B) (boxApproxCoeff a δ A B) := by
  have hu' : ∀ᵐ x ∂μ, ∀ i, |(u i : Lp ℝ 2 μ) x| ≤ M := ae_all_iff.2 hu
  have hk : ∀ k ∈ (Finset.univ : Finset (Fin m → Fin (K + 1))),
      G.GammaChain u (fun y => cellWeight a δ k y * cellAffine a δ A B k y)
        (fun i y => cellWeight a δ k y * B k i + cellAffine a δ A B k y * cellSlope a δ k i y) := by
    intro k _
    obtain ⟨h1, h2⟩ := G.gammaChain_cellWeight u hδ k
    have h3 : G.GammaChain u (cellAffine a δ A B k) (fun i _ => B k i) :=
      G.gammaChain_affine u (A k) (B k) (gridNode a δ k)
    have h4 : ∀ᵐ x ∂μ, |cellAffine a δ A B k fun j => (u j : Lp ℝ 2 μ) x| ≤
        |A k| + ∑ i, |B k i| * (M + |gridNode a δ k i|) := by
      filter_upwards [hu'] with x hx
      exact abs_affine_le (A k) (B k) (gridNode a δ k) _ hx
    exact h1.mul h3 h2 h4
  refine (GammaChain.sum (G := G) Finset.univ hk).congr (fun y => rfl) (fun i y => ?_)
  simp only [boxApproxCoeff]
  exact Finset.sum_congr rfl fun k _ => by ring

/-!
## G. The m = 1 case of the contract in its exact format; reduction to the chain-rule predicate
-/

/--
reduction: if, for every u ∈ 𝔻ᵐ and F : ℝᵐ → ℝ of class C¹ (`ContDiff ℝ 1 F`) and L-Lipschitz,
`GammaChain u F (∂F)` with ∂ᵢF(y) = DF(y)(eᵢ), then the dimension-m part `ChainRuleDim m` of the
contract `ChainRule` is proved.
-/
theorem chainRuleDim_of_gammaChain {m : ℕ}
    (h : ∀ (u : Fin m → D.form.dom) (F : (Fin m → ℝ) → ℝ) (L : ℝ≥0), ContDiff ℝ 1 F →
      LipschitzWith L F → G.GammaChain u F (fun i y => fderiv ℝ F y (Pi.single i 1))) :
    G.ChainRuleDim m :=
  fun u F L hC hL w hw => (h u F L hC hL).exists_mem w hw

/--
**the m = 1 case of the contract `ChainRule` in its exact format**: for u : Fin 1 → 𝔻 and F : (Fin 1
→ ℝ) → ℝ of class C¹ (`ContDiff ℝ 1 F`) and L-Lipschitz, every class w ∈ L² equal a.e. to F(u)
lies in 𝔻 and, for every v ∈ 𝔻, γ(w, v) = Σᵢ DF(u)(eᵢ) γ(uᵢ, v) a.e. (`fderiv ℝ F (u x) (Pi.single i
1)`). Derived from the univariate chain rule `exists_mem_gamma_comp` applied to f(t) = F(t, …),
f′(t) = DF((t))((1)).
Reference: Bouleau–Hirsch (1991), th. I.6.1.2 and cor. I.6.1.3.
-/
theorem chainRuleDim_one : G.ChainRuleDim 1 := by
  intro u F L hC hL w hw
  set f : ℝ → ℝ := fun t => F (fun _ => t) with hf
  have hfL : LipschitzWith L f := LipschitzWith.of_dist_le_mul fun s t => by
    have h := hL.dist_le_mul (fun _ : Fin 1 => s) (fun _ => t)
    rwa [dist_pi_const] at h
  have hd : ∀ t ∉ (∅ : Set ℝ),
      HasStrictDerivAt f (fderiv ℝ F (fun _ => t) (fun _ => 1)) t := by
    intro t _
    have h1 : HasStrictDerivAt (fun s : ℝ => (fun _ : Fin 1 => s)) (fun _ => (1 : ℝ)) t :=
      hasStrictDerivAt_pi.2 fun _ => hasStrictDerivAt_id t
    exact (hC.contDiffAt.hasStrictFDerivAt one_ne_zero).comp_hasStrictDerivAt t h1
  have hw' : ⇑w =ᵐ[μ] fun x => f ((u 0 : Lp ℝ 2 μ) x) := by
    filter_upwards [hw] with x hx
    rw [hx]
    congr 1
    funext i
    rw [Fin.fin_one_eq_zero i]
  obtain ⟨hm, hγ⟩ := G.exists_mem_gamma_comp
    (F' := fun t => fderiv ℝ F (fun _ => t) (fun _ => 1)) hfL Set.countable_empty hd (u 0) w hw'
  refine ⟨hm, fun v => ?_⟩
  have e1 : ∀ x, (fun j : Fin 1 => (u j : Lp ℝ 2 μ) x) = fun _ => (u 0 : Lp ℝ 2 μ) x :=
    fun x => funext fun j => by rw [Fin.fin_one_eq_zero j]
  have e2 : (Pi.single 0 1 : Fin 1 → ℝ) = fun _ => 1 :=
    funext fun j => by rw [Fin.fin_one_eq_zero j, Pi.single_eq_same]
  filter_upwards [hγ v] with x hx
  rw [hx, Fin.sum_univ_one, e1 x, e2]

/-! ## Format controls (`example`, no declaration) -/

/--
The theorem `chainRuleDim_one` has exactly the type of the `ChainRule` contract restricted to m = 1:
the full contract body copied at m = 1, under its hypothesis 0 < 1.
-/
example : 0 < 1 → ∀ (u : Fin 1 → D.form.dom) (F : (Fin 1 → ℝ) → ℝ) (L : ℝ≥0),
    ContDiff ℝ 1 F → LipschitzWith L F →
    ∀ w : Lp ℝ 2 μ, (⇑w =ᵐ[μ] fun x => F (fun i => (u i : Lp ℝ 2 μ) x)) →
      ∃ hw : w ∈ D.form.dom, ∀ v : D.form.dom, ⇑(G.gamma ⟨w, hw⟩ v) =ᵐ[μ] fun x =>
        ∑ i, fderiv ℝ F (fun j => (u j : Lp ℝ 2 μ) x) (Pi.single i 1) * G.gamma (u i) v x :=
  fun _ => G.chainRuleDim_one

/-- The dimension-1 part is, by definition, the contract body at m = 1. -/
example : G.ChainRuleDim 1 = ∀ (u : Fin 1 → D.form.dom) (F : (Fin 1 → ℝ) → ℝ) (L : ℝ≥0),
    ContDiff ℝ 1 F → LipschitzWith L F →
    ∀ w : Lp ℝ 2 μ, (⇑w =ᵐ[μ] fun x => F (fun i => (u i : Lp ℝ 2 μ) x)) →
      ∃ hw : w ∈ D.form.dom, ∀ v : D.form.dom, ⇑(G.gamma ⟨w, hw⟩ v) =ᵐ[μ] fun x =>
        ∑ i, fderiv ℝ F (fun j => (u j : Lp ℝ 2 μ) x) (Pi.single i 1) * G.gamma (u i) v x :=
  rfl

/-- The contract implies its m = 1 part, and the conjunction of all dimension parts recovers it. -/
example : (G.ChainRule → G.ChainRuleDim 1) ∧ ((∀ m, 0 < m → G.ChainRuleDim m) → G.ChainRule) :=
  ⟨fun h => h 1 one_pos, fun h => h⟩

end CarreDuChamp
end LocalDirichletForm

end ErrorCalculus
