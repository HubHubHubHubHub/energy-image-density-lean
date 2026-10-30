import ErrorCalculus.Dirichlet.LocalCarreDuChampClamp
import ErrorCalculus.Dirichlet.FiniteEnergyMeasure

/-!
# univariate chain rule and `LeibnizRule` for the generic carre du champ

## Main results
Same framework as `LocalCarreDuChampClamp` (`D : LocalDirichletForm μ`, `G : D.CarreDuChamp`, ℰ(f,
f) = ∫ γ(f, f) dμ):

* Slopes of the piecewise affine interpolants (`interpSlope`) and their convergence to F′(t) at
every irrational t where F is strictly differentiable (`tendsto_interpSlope_grid`).
* Piecewise affine chain rule γ(Iₙ(u), v) = Sₙ(u) γ(u, v) (`gamma_interpElem_ae_eq`) and tool
(W) for passage to the limit against the test functions (`tendsto_integral_mul_gamma`).
* Univariate chain rule for Lipschitz F, strictly differentiable outside a countable set
(`gamma_comp_ae_eq`, `exists_mem_gamma_comp`), a form more general than the m = 1 case of BH 1991,
th. I.6.1.2 and cor. I.6.1.3 (pp. 36–37); the C¹ ∩ Lip case (`gamma_comp_ae_eq_of_contDiff`); the
control F = |·| (`gamma_abs_ae_eq`).
* Squares of bounded functions (`gamma_sq_ae_eq`), then **`leibnizRule : G.LeibnizRule`** and
**`leibnizRuleStatement : LeibnizRuleStatement`**: the contract `LeibnizRule` is proved.

The multivariate chain rule is proved in `LocalCarreDuChampChainRule` and connected to
`BHFunctionalCalculus` by `DprBridge.ChainRuleBridge`. The chain rule for arbitrary Lipschitz F and
ordinary rather than strict differentiability are outside this module.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option maxHeartbeats 800000

namespace ErrorCalculus

/-! ## B. Slopes of the piecewise affine interpolant (grids) -/

/--
Slope of the interpolant of F on the grid a + kδ, k < N: Σₖ sₖ 1_{]tₖ, tₖ₊₁[}(t), sₖ = (F(tₖ₊₁) −
F(tₖ))/δ (0 at nodes and outside the grid).
-/
def interpSlope (F : ℝ → ℝ) (a δ : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, (F (a + (k + 1) * δ) - F (a + k * δ)) / δ *
    (Set.Ioo (a + k * δ) (a + (k + 1) * δ)).indicator 1 t

/-- On the open cell ]tₖ, tₖ₊₁[ (k < N), the slope is sₖ (the open cells are pairwise disjoint). -/
theorem interpSlope_eq_of_mem (F : ℝ → ℝ) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) {N k : ℕ} (hk : k < N)
    {t : ℝ} (ht : t ∈ Set.Ioo (a + k * δ) (a + (k + 1) * δ)) :
    interpSlope F a δ N t = (F (a + (k + 1) * δ) - F (a + k * δ)) / δ := by
  rw [interpSlope, Finset.sum_eq_single_of_mem k (Finset.mem_range.2 hk), Set.indicator_of_mem ht,
    Pi.one_apply, mul_one]
  intro j _ hjk
  rw [Set.indicator_of_notMem, mul_zero]
  intro hj
  have h1 : (j : ℝ) * δ < ((k : ℝ) + 1) * δ := by linarith [hj.1, ht.2]
  have h2 : (k : ℝ) * δ < ((j : ℝ) + 1) * δ := by linarith [hj.2, ht.1]
  have h1' : (j : ℝ) < k + 1 := lt_of_mul_lt_mul_right h1 hδ.le
  have h2' : (k : ℝ) < j + 1 := lt_of_mul_lt_mul_right h2 hδ.le
  have h1'' : j < k + 1 := by exact_mod_cast h1'
  have h2'' : k < j + 1 := by exact_mod_cast h2'
  omega

/-- If F is L-Lipschitz, then |slope| ≤ L everywhere. -/
theorem abs_interpSlope_le {F : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ x y, |F x - F y| ≤ L * |x - y|) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (t : ℝ) :
    |interpSlope F a δ N t| ≤ L := by
  by_cases h : ∃ k < N, t ∈ Set.Ioo (a + k * δ) (a + (k + 1) * δ)
  · obtain ⟨k, hk, ht⟩ := h
    rw [interpSlope_eq_of_mem F a hδ hk ht, abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
    have h3 := hF (a + (k + 1) * δ) (a + k * δ)
    rwa [show a + (k + 1) * δ - (a + k * δ) = δ by ring, abs_of_pos hδ] at h3
  · simp only [not_exists, not_and] at h
    rw [interpSlope, Finset.sum_eq_zero (fun k hk => by
      rw [Set.indicator_of_notMem (h k (Finset.mem_range.1 hk)), mul_zero]), abs_zero]
    exact hL

/-- The slope is a measurable function of t. -/
theorem measurable_interpSlope (F : ℝ → ℝ) (a δ : ℝ) (N : ℕ) :
    Measurable (interpSlope F a δ N) := by
  unfold interpSlope
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_one.indicator measurableSet_Ioo).const_mul _

/-- The nodes −(n + 1) + k/(n + 1) of the grids are rational. -/
theorem gridStart_add_mul_gridStep_mem_range_ratCast (n k : ℕ) :
    gridStart n + k * gridStep n ∈ Set.range ((↑) : ℚ → ℝ) :=
  ⟨-((n : ℚ) + 1) + k * (1 / ((n : ℚ) + 1)), by
    unfold gridStart gridStep
    push_cast
    ring⟩

/--
convergence of slopes (the interpolation route for BH 1991, th. I.6.1.2, p. 36): if F is strictly
differentiable at t with derivative d, and t is not the image of a rational number (hence not a node
of any grid), the slope `interpSlope` of the interpolant on the n-th grid at t tends to d as n → ∞.
-/
theorem tendsto_interpSlope_grid {F : ℝ → ℝ} {d t : ℝ} (hF : HasStrictDerivAt F d t)
    (ht : t ∉ Set.range ((↑) : ℚ → ℝ)) :
    Tendsto (fun n => interpSlope F (gridStart n) (gridStep n) (gridCount n) t) atTop (𝓝 d) := by
  set k : ℕ → ℕ := fun n => ⌊(t - gridStart n) / gridStep n⌋₊ with hk
  set a : ℕ → ℝ := fun n => gridStart n + (k n : ℝ) * gridStep n with ha
  set b : ℕ → ℝ := fun n => gridStart n + ((k n : ℝ) + 1) * gridStep n with hb
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt |t|
  have hev : ∀ n, N₀ ≤ n → a n < t ∧ t < b n ∧ k n < gridCount n := by
    intro n hn
    have hδ := gridStep_pos n
    have hn' : |t| < (n : ℝ) + 1 := by
      have : (N₀ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hst : gridStart n < t := by
      unfold gridStart
      linarith [neg_abs_le t]
    have hpos : 0 ≤ (t - gridStart n) / gridStep n := div_nonneg (by linarith) hδ.le
    have h1 : ((k n : ℕ) : ℝ) ≤ (t - gridStart n) / gridStep n := Nat.floor_le hpos
    have h2 : (t - gridStart n) / gridStep n < ((k n : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one ((t - gridStart n) / gridStep n)
    have h1' : (k n : ℝ) * gridStep n ≤ t - gridStart n := (le_div_iff₀ hδ).1 h1
    have h2' : t - gridStart n < ((k n : ℝ) + 1) * gridStep n := (div_lt_iff₀ hδ).1 h2
    have hne : a n ≠ t := fun h => ht (h ▸ gridStart_add_mul_gridStep_mem_range_ratCast n (k n))
    have hc := gridStart_add_gridCount_mul_gridStep n
    refine ⟨lt_of_le_of_ne (by simp only [ha]; linarith) hne, by simp only [hb]; linarith, ?_⟩
    have h3 : (k n : ℝ) * gridStep n < (gridCount n : ℝ) * gridStep n := by
      linarith [(abs_lt.1 hn').2]
    exact_mod_cast lt_of_mul_lt_mul_right h3 hδ.le
  have hS : ∀ n, N₀ ≤ n → interpSlope F (gridStart n) (gridStep n) (gridCount n) t =
      (F (b n) - F (a n)) / gridStep n := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := hev n hn
    exact interpSlope_eq_of_mem F _ (gridStep_pos n) h3 ⟨h1, h2⟩
  have hδ0 : Tendsto (fun n : ℕ => gridStep n) atTop (𝓝 0) := by
    unfold gridStep
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hba : ∀ n, b n - a n = gridStep n := fun n => by simp only [ha, hb]; ring
  have hat : Tendsto a atTop (𝓝 t) := by
    have hl : Tendsto (fun n => t - gridStep n) atTop (𝓝 t) := by
      simpa using (tendsto_const_nhds (x := t)).sub hδ0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop N₀] with n hn
      have := (hev n hn).2.1
      linarith [hba n]
    · filter_upwards [eventually_ge_atTop N₀] with n hn
      exact (hev n hn).1.le
  have hbt : Tendsto b atTop (𝓝 t) := by
    have hu : Tendsto (fun n => t + gridStep n) atTop (𝓝 t) := by
      simpa using (tendsto_const_nhds (x := t)).add hδ0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
    · filter_upwards [eventually_ge_atTop N₀] with n hn
      exact (hev n hn).2.1.le
    · filter_upwards [eventually_ge_atTop N₀] with n hn
      have := (hev n hn).1
      linarith [hba n]
  have hlo := (HasStrictFDerivAt.isLittleO hF).comp_tendsto (hbt.prodMk_nhds hat)
  have hdiv := hlo.tendsto_div_nhds_zero
  have hlim : Tendsto (fun n => (F (b n) - F (a n)) / gridStep n) atTop (𝓝 d) := by
    have h0 := hdiv.add_const d
    rw [zero_add] at h0
    refine h0.congr fun n => ?_
    simp only [Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, hba]
    have hδ := (gridStep_pos n).ne'
    field_simp
    ring
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop N₀] with n hn
  exact (hS n hn).symm

namespace LocalDirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (D : LocalDirichletForm μ)

/-! ## C. L² convergence of interpolants -/

/--
The interpolants (grids n) of F ∘ u converge to F ∘ u in L² (dominated convergence with bound 2K +
K|u|; extracted from the proof of `exists_mem_of_lipschitzWith`).
-/
theorem tendsto_interpElem_grid {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) (u : D.form.dom)
    (w : Lp ℝ 2 μ) (hw : ⇑w =ᵐ[μ] fun x => F ((u : Lp ℝ 2 μ) x)) :
    Tendsto (fun n => ((D.interpElem F (gridStart n) (gridStep n) (gridCount n) u : D.form.dom) :
      Lp ℝ 2 μ)) atTop (𝓝 w) := by
  have hK : (0 : ℝ) ≤ K := K.2
  have hF' : ∀ x y, |F x - F y| ≤ (K : ℝ) * |x - y| := by
    intro x y
    have h := hF.dist_le_mul x y
    rwa [Real.dist_eq, Real.dist_eq] at h
  set W : ℕ → D.form.dom := fun n =>
    D.interpElem F (gridStart n) (gridStep n) (gridCount n) u with hW
  set g : Lp ℝ 2 μ := (2 * (K : ℝ)) • ((D.one : D.form.dom) : Lp ℝ 2 μ) +
    (K : ℝ) • |(u : Lp ℝ 2 μ)| with hg
  have hgx : ⇑g =ᵐ[μ] fun x => 2 * (K : ℝ) + (K : ℝ) * |(u : Lp ℝ 2 μ) x| := by
    filter_upwards [Lp.coeFn_add ((2 * (K : ℝ)) • ((D.one : D.form.dom) : Lp ℝ 2 μ))
      ((K : ℝ) • |(u : Lp ℝ 2 μ)|), Lp.coeFn_smul (2 * (K : ℝ)) ((D.one : D.form.dom) : Lp ℝ 2 μ),
      Lp.coeFn_smul (K : ℝ) |(u : Lp ℝ 2 μ)|, D.coeFn_one, Lp.coeFn_abs (u : Lp ℝ 2 μ)]
      with x h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, h5, smul_eq_mul, smul_eq_mul,
      mul_one]
  have hT0 : Tendsto (fun n => ((W n : D.form.dom) : Lp ℝ 2 μ) - w) atTop (𝓝 0) := by
    apply lp_two_tendsto_zero_of_dominated _ g
    · intro n
      filter_upwards [Lp.coeFn_sub ((W n : D.form.dom) : Lp ℝ 2 μ) w,
        D.coeFn_interpElem F (gridStart n) (gridStep n) (gridCount n) u, hw, hgx]
        with x h1 h2 h3 h4
      rw [h1, Pi.sub_apply, h2, h3, h4,
        abs_of_nonneg (show (0 : ℝ) ≤ 2 * (K : ℝ) + (K : ℝ) * |(u : Lp ℝ 2 μ) x| by positivity)]
      exact (abs_add_interpSum_grid_sub_le F hK hF' n _).1
    · have hall : ∀ᵐ x ∂μ, ∀ n : ℕ,
          (((W n : D.form.dom) : Lp ℝ 2 μ) - w) x =
            F (gridStart n) + interpSum F (gridStart n) (gridStep n) (gridCount n)
              ((u : Lp ℝ 2 μ) x) - F ((u : Lp ℝ 2 μ) x) := by
        rw [ae_all_iff]
        intro n
        filter_upwards [Lp.coeFn_sub ((W n : D.form.dom) : Lp ℝ 2 μ) w,
          D.coeFn_interpElem F (gridStart n) (gridStep n) (gridCount n) u, hw] with x h1 h2 h3
        rw [h1, Pi.sub_apply, h2, h3]
      filter_upwards [hall] with x hx
      simp only [hx]
      exact tendsto_add_interpSum_grid_sub F hK hF' _
  have h := hT0.add_const w
  simp only [sub_add_cancel, zero_add] at h
  exact h

namespace CarreDuChamp
variable {D} (G : D.CarreDuChamp)

/-! ## F. Piecewise affine chain rule and tool (W) -/

/--
(piecewise affine chain rule, the route for BH 1991, th. I.6.1.2): for F : ℝ → ℝ, a, δ ∈ ℝ, N ∈ ℕ
and u, v ∈ 𝔻, the interpolant `interpElem` of F on the grid a + kδ (k < N) satisfies γ(Iₙ(u), v) =
Sₙ(u) γ(u, v) a.e., where Sₙ = `interpSlope` (linearity of γ, `clampRule` and γ(1, ·) = 0).
-/
theorem gamma_interpElem_ae_eq (F : ℝ → ℝ) (a δ : ℝ) (N : ℕ) (u v : D.form.dom) :
    ⇑(G.gamma (D.interpElem F a δ N u) v) =ᵐ[μ]
      fun x => interpSlope F a δ N ((u : Lp ℝ 2 μ) x) * G.gamma u v x := by
  have e : G.gamma (D.interpElem F a δ N u) v = ∑ k ∈ Finset.range N,
      ((F (a + (k + 1) * δ) - F (a + k * δ)) / δ) •
        G.gamma (D.clamp (a + k * δ) (a + (k + 1) * δ) u) v := by
    rw [interpElem, G.gamma_add_smul_one, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply]
  have hk : ∀ᵐ x ∂μ, ∀ k ∈ Finset.range N,
      G.gamma (D.clamp (a + k * δ) (a + (k + 1) * δ) u) v x =
        (Set.Ioo (a + k * δ) (a + (k + 1) * δ)).indicator 1 ((u : Lp ℝ 2 μ) x) * G.gamma u v x :=
    (Filter.eventually_all_finset _).2 fun k _ => G.clampRule u v _ _ _ (D.coeFn_clamp _ _ u)
  have hs : ∀ᵐ x ∂μ, ∀ k ∈ Finset.range N,
      (((F (a + (k + 1) * δ) - F (a + k * δ)) / δ) •
          G.gamma (D.clamp (a + k * δ) (a + (k + 1) * δ) u) v) x =
        (F (a + (k + 1) * δ) - F (a + k * δ)) / δ *
          G.gamma (D.clamp (a + k * δ) (a + (k + 1) * δ) u) v x :=
    (Filter.eventually_all_finset _).2 fun k _ =>
      (Lp.coeFn_smul _ _).mono fun x h => by rw [h, Pi.smul_apply, smul_eq_mul]
  rw [e]
  filter_upwards [lp_coeFn_sum _ _, hk, hs] with x h1 h2 h3
  rw [h1, interpSlope, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk' => ?_
  rw [h3 k hk', h2 k hk', mul_assoc]

/-- The pairing with Γ = 2γ: ⟨z, Γ(f, v)⟩ = 2 ∫ z γ(f, v). -/
theorem pair_toCLM (z : D.toDirichletForm.Space) (f v : D.form.dom) :
    D.toDirichletForm.pair z (G.toCLM (D.form.formToDomain.symm f) (D.form.formToDomain.symm v)) =
      2 * ∫ ω, D.toDirichletForm.toLp z ω * G.gamma f v ω ∂μ := by
  rw [Capacity.DirichletForm.pair, G.toCLM_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul (2 : ℝ) (G.gamma f v)] with ω h
  rw [h, Pi.smul_apply, smul_eq_mul]
  ring

/--
If the energies of xₙ are bounded and xₙ → y in L², then ∫ z γ(xₙ, v) → ∫ z γ(y, v) for every domain
element v and every bounded domain test z. The proof uses weak convergence against a continuous
form-space functional.
-/
theorem tendsto_integral_mul_gamma {x : ℕ → D.form.dom} {y : D.form.dom} {C : ℝ}
    (hE : ∀ n, D.form.E (x n) (x n) ≤ C)
    (hL : Tendsto (fun n => ((x n : D.form.dom) : Lp ℝ 2 μ)) atTop (𝓝 (y : Lp ℝ 2 μ)))
    {z : D.toDirichletForm.Space} (hz : z ∈ D.toDirichletForm.bddSpace) (v : D.form.dom) :
    Tendsto (fun n => ∫ ω, D.toDirichletForm.toLp z ω * G.gamma (x n) v ω ∂μ) atTop
      (𝓝 (∫ ω, D.toDirichletForm.toLp z ω * G.gamma y v ω ∂μ)) := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hL)
  have hR : ∀ n, ‖(D.form.formToDomain.symm (x n) : D.toDirichletForm.Space)‖ ≤
      Real.sqrt (B ^ 2 + C) := by
    intro n
    have h1 := D.form.formNorm_sq (x n)
    rw [QuadForm.formNorm] at h1
    have hb : ‖((x n : D.form.dom) : Lp ℝ 2 μ)‖ ≤ B := hB _ ⟨n, rfl⟩
    have hb2 : ‖((x n : D.form.dom) : Lp ℝ 2 μ)‖ ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [← Real.sqrt_sq (norm_nonneg (D.form.formToDomain.symm (x n)))]
    exact Real.sqrt_le_sqrt (by rw [h1]; linarith [hE n])
  have e : ∀ f : D.form.dom, D.toDirichletForm.toLp (D.form.formToDomain.symm f) =
      (f : Lp ℝ 2 μ) := by
    intro f
    change ((D.form.formToDomain (D.form.formToDomain.symm f) : D.form.dom) : Lp ℝ 2 μ) = _
    rw [LinearEquiv.apply_symm_apply]
  have hL' : Tendsto (fun n => D.toDirichletForm.toLp (D.form.formToDomain.symm (x n) :
      D.toDirichletForm.Space)) atTop
      (𝓝 (D.toDirichletForm.toLp (D.form.formToDomain.symm y : D.toDirichletForm.Space))) := by
    simp only [e]
    exact hL
  set T : D.toDirichletForm.Dual := (D.toDirichletForm.pairCLM hz).comp
    (G.toCLM.flip (D.form.formToDomain.symm v)) with hT
  have eT : ∀ f : D.form.dom, T (D.form.formToDomain.symm f) =
      2 * ∫ ω, D.toDirichletForm.toLp z ω * G.gamma f v ω ∂μ := by
    intro f
    change D.toDirichletForm.pair z
      (G.toCLM (D.form.formToDomain.symm f) (D.form.formToDomain.symm v)) = _
    exact G.pair_toCLM z f v
  have h := (D.toDirichletForm.tendsto_apply_of_bounded hR hL' T).const_mul (1 / 2 : ℝ)
  simp only [eT] at h
  have e2 : ∀ r : ℝ, (1 / 2 : ℝ) * (2 * r) = r := fun r => by ring
  simp only [e2] at h
  exact h

/-! ## G. Univariate chain rule -/

/--
The univariate chain rule in a form more general than the m = 1 case of BH 1991, th. I.6.1.2 and
cor. I.6.1.3 (pp. 36–37) (local interpolation route; not a literal quotation): let F be K-Lipschitz
and strictly differentiable with derivative F′(t) at every t outside a countable set N (arbitrary F′
on N). For u, v, w ∈ 𝔻 with w = F ∘ u a.e., γ(w, v) = F′(u) γ(u, v) a.e.
-/
theorem gamma_comp_ae_eq {F F' : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) {N : Set ℝ}
    (hN : N.Countable) (hd : ∀ t ∉ N, HasStrictDerivAt F (F' t) t) (u v w : D.form.dom)
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun x => F ((u : Lp ℝ 2 μ) x)) :
    ⇑(G.gamma w v) =ᵐ[μ] fun x => F' ((u : Lp ℝ 2 μ) x) * G.gamma u v x := by
  have hK : (0 : ℝ) ≤ K := K.2
  have hF' : ∀ x y, |F x - F y| ≤ (K : ℝ) * |x - y| := by
    intro x y
    have h := hF.dist_le_mul x y
    rwa [Real.dist_eq, Real.dist_eq] at h
  set W : ℕ → D.form.dom := fun n =>
    D.interpElem F (gridStart n) (gridStep n) (gridCount n) u with hW
  set S : ℕ → ℝ → ℝ := fun n => interpSlope F (gridStart n) (gridStep n) (gridCount n) with hS
  have hE : ∀ n, D.form.E (W n) (W n) ≤ (K : ℝ) ^ 2 * D.form.E u u := fun n =>
    D.energy_interpElem_le F hF' _ (gridStep_pos n) _ u
  have hT : Tendsto (fun n => ((W n : D.form.dom) : Lp ℝ 2 μ)) atTop (𝓝 (w : Lp ℝ 2 μ)) :=
    D.tendsto_interpElem_grid hF u (w : Lp ℝ 2 μ) hw
  have hγW : ∀ n, ⇑(G.gamma (W n) v) =ᵐ[μ] fun x => S n ((u : Lp ℝ 2 μ) x) * G.gamma u v x :=
    fun n => G.gamma_interpElem_ae_eq F _ _ _ u v
  set N' : Set ℝ := N ∪ Set.range ((↑) : ℚ → ℝ) with hN'
  have hN'c : N'.Countable := hN.union (Set.countable_range _)
  have hzero : ∀ᵐ x ∂μ, (u : Lp ℝ 2 μ) x ∈ N' → G.gamma u v x = 0 := by
    have h := (ae_ball_iff hN'c).2 (fun c (_ : c ∈ N') => G.ae_gamma_eq_zero_of_eq u v c)
    filter_upwards [h] with x hx hmem
    exact hx _ hmem rfl
  have hbd : ∀ n t, |S n t| ≤ K := fun n t =>
    abs_interpSlope_le hK hF' _ (gridStep_pos n) _ t
  have hpt : ∀ᵐ x ∂μ, Tendsto (fun n => S n ((u : Lp ℝ 2 μ) x) * G.gamma u v x) atTop
      (𝓝 (F' ((u : Lp ℝ 2 μ) x) * G.gamma u v x)) := by
    filter_upwards [hzero] with x hx
    by_cases hm : (u : Lp ℝ 2 μ) x ∈ N'
    · rw [hx hm]
      simp only [mul_zero]
      exact tendsto_const_nhds
    · have h1 : (u : Lp ℝ 2 μ) x ∉ N := fun h => hm (Or.inl h)
      have h2 : (u : Lp ℝ 2 μ) x ∉ Set.range ((↑) : ℚ → ℝ) := fun h => hm (Or.inr h)
      exact (tendsto_interpSlope_grid (hd _ h1) h2).mul_const _
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => S n ((u : Lp ℝ 2 μ) x) * G.gamma u v x) μ :=
    fun n => (((measurable_interpSlope _ _ _ _).comp_aemeasurable
      (Lp.aestronglyMeasurable (u : Lp ℝ 2 μ)).aemeasurable).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable _)
  have htm : AEStronglyMeasurable (fun x => F' ((u : Lp ℝ 2 μ) x) * G.gamma u v x) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas hpt
  have hgi : Integrable (fun x => G.gamma u v x) μ := L1.integrable_coeFn _
  have hlimb : ∀ᵐ x ∂μ,
      ‖F' ((u : Lp ℝ 2 μ) x) * G.gamma u v x‖ ≤ (K : ℝ) * ‖G.gamma u v x‖ := by
    filter_upwards [hpt] with x hx
    refine le_of_tendsto' hx.norm (fun n => ?_)
    rw [norm_mul, Real.norm_eq_abs (S n _)]
    exact mul_le_mul_of_nonneg_right (hbd n _) (norm_nonneg _)
  have hti : Integrable (fun x => F' ((u : Lp ℝ 2 μ) x) * G.gamma u v x) μ :=
    Integrable.mono' (hgi.norm.const_mul _) htm hlimb
  apply D.toDirichletForm.ae_eq_of_integral_mul_eq D.denseRange_toLp (L1.integrable_coeFn _) hti
  intro z hz
  have h1 := G.tendsto_integral_mul_gamma hE hT hz v
  obtain ⟨Cz, hCz⟩ := (Capacity.DirichletForm.mem_bddSpace _).1 hz
  have hcongr : ∀ n, ∫ ω, D.toDirichletForm.toLp z ω * G.gamma (W n) v ω ∂μ =
      ∫ ω, D.toDirichletForm.toLp z ω * (S n ((u : Lp ℝ 2 μ) ω) * G.gamma u v ω) ∂μ := fun n =>
    integral_congr_ae ((hγW n).mono fun ω h => by dsimp only; rw [h])
  have h2 : Tendsto (fun n => ∫ ω, D.toDirichletForm.toLp z ω * G.gamma (W n) v ω ∂μ) atTop
      (𝓝 (∫ ω, D.toDirichletForm.toLp z ω * (F' ((u : Lp ℝ 2 μ) ω) * G.gamma u v ω) ∂μ)) := by
    simp only [hcongr]
    refine tendsto_integral_of_dominated_convergence
      (fun ω => Cz * ((K : ℝ) * ‖G.gamma u v ω‖))
      (fun n => (Lp.aestronglyMeasurable _).mul (hmeas n)) ((hgi.norm.const_mul _).const_mul _)
      (fun n => ?_) ?_
    · filter_upwards [hCz] with ω hω
      rw [norm_mul, norm_mul, Real.norm_eq_abs (D.toDirichletForm.toLp z ω),
        Real.norm_eq_abs (S n _)]
      exact mul_le_mul hω (mul_le_mul_of_nonneg_right (hbd n _) (norm_nonneg _)) (by positivity)
        ((abs_nonneg _).trans hω)
    · filter_upwards [hpt] with ω hω
      exact hω.const_mul _
  exact tendsto_nhds_unique h1 h2

/--
univariate chain rule with membership (BH 1991, th. I.6.1.2 and cor. I.6.1.3 for m = 1, under the
hypotheses of `gamma_comp_ae_eq`: F K-Lipschitz, strictly differentiable outside a countable N): for
u ∈ 𝔻, every class w ∈ L² equal a.e. to F ∘ u lies in 𝔻 and γ(w, v) = F′(u) γ(u, v) a.e. for every v
∈ 𝔻.
-/
theorem exists_mem_gamma_comp {F F' : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) {N : Set ℝ}
    (hN : N.Countable) (hd : ∀ t ∉ N, HasStrictDerivAt F (F' t) t) (u : D.form.dom)
    (w : Lp ℝ 2 μ) (hw : ⇑w =ᵐ[μ] fun x => F ((u : Lp ℝ 2 μ) x)) :
    ∃ hw' : w ∈ D.form.dom, ∀ v : D.form.dom,
      ⇑(G.gamma ⟨w, hw'⟩ v) =ᵐ[μ] fun x => F' ((u : Lp ℝ 2 μ) x) * G.gamma u v x := by
  obtain ⟨hw', -⟩ := D.exists_mem_of_lipschitzWith hF u w hw
  exact ⟨hw', fun v => G.gamma_comp_ae_eq hF hN hd u v ⟨w, hw'⟩ hw⟩

/--
The univariate C¹ ∩ Lip case (BH 1991, th. I.6.1.2 and cor. I.6.1.3, pp. 36–37, m = 1): for F
of class C¹ and K-Lipschitz and u, v, w ∈ 𝔻 with w = F ∘ u a.e., γ(w, v) = F′(u) γ(u, v) a.e., where
F′
= `deriv F`.
-/
theorem gamma_comp_ae_eq_of_contDiff {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F)
    (hC : ContDiff ℝ 1 F) (u v w : D.form.dom)
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun x => F ((u : Lp ℝ 2 μ) x)) :
    ⇑(G.gamma w v) =ᵐ[μ] fun x => deriv F ((u : Lp ℝ 2 μ) x) * G.gamma u v x :=
  G.gamma_comp_ae_eq hF Set.countable_empty
    (fun _ _ => hC.contDiffAt.hasStrictDerivAt one_ne_zero) u v w hw

/--
non-vacuity control for the exceptional set N (F = |·|, not differentiable at 0, N = {0}): for u, v,
w ∈ 𝔻 with w = |u| a.e., γ(w, v) = sgn(u) γ(u, v) a.e. (with sgn(0) = −1, an irrelevant value: γ(u,
v) = 0 a.e. on {u = 0}).
-/
theorem gamma_abs_ae_eq (u v w : D.form.dom)
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun x => |(u : Lp ℝ 2 μ) x|) :
    ⇑(G.gamma w v) =ᵐ[μ] fun x => (if 0 < (u : Lp ℝ 2 μ) x then 1 else -1) * G.gamma u v x := by
  refine G.gamma_comp_ae_eq (F' := fun t => if 0 < t then 1 else -1) ErrorStructure.lipschitz_abs
    (Set.countable_singleton 0) (fun t ht => ?_) u v w hw
  rcases lt_or_gt_of_ne (show t ≠ 0 from ht) with h | h
  · rw [if_neg (not_lt.2 h.le)]
    apply (hasStrictDerivAt_id t).neg.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with s hs
    exact (abs_of_neg hs).symm
  · rw [if_pos h]
    apply (hasStrictDerivAt_id t).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with s hs
    exact (abs_of_pos hs).symm

end CarreDuChamp
end LocalDirichletForm

/-! ## H. `LeibnizRule` -/

/-- Strict derivative of t ↦ ((−R) ∨ (t ∧ R))² at t, |t| < R: 2t. -/
theorem hasStrictDerivAt_clamp_sq {R t : ℝ} (ht : |t| < R) :
    HasStrictDerivAt (fun s : ℝ => (max (-R) (min s R)) ^ 2) (2 * t) t := by
  have h := hasStrictDerivAt_pow 2 t
  have e : ((2 : ℕ) : ℝ) * t ^ (2 - 1) = 2 * t := by norm_num
  rw [e] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (abs_lt.1 ht).1 (abs_lt.1 ht).2] with s hs
  rw [min_eq_left hs.2.le, max_eq_right hs.1.le]

/-- Zero strict derivative of t ↦ ((−R) ∨ (t ∧ R))² at t, |t| > R ≥ 0. -/
theorem hasStrictDerivAt_clamp_sq_of_lt_abs {R t : ℝ} (hR : 0 ≤ R) (ht : R < |t|) :
    HasStrictDerivAt (fun s : ℝ => (max (-R) (min s R)) ^ 2) 0 t := by
  apply (hasStrictDerivAt_const t (R ^ 2)).congr_of_eventuallyEq
  rcases lt_abs.1 ht with h | h
  · filter_upwards [Ioi_mem_nhds h] with s hs
    have hs' : R < s := hs
    rw [min_eq_right hs'.le, max_eq_right (by linarith)]
  · filter_upwards [Iio_mem_nhds (show t < -R by linarith)] with s hs
    have hs' : s < -R := hs
    rw [min_eq_left (by linarith), max_eq_left hs'.le, neg_sq]

namespace LocalDirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {D : LocalDirichletForm μ}

namespace CarreDuChamp
variable (G : D.CarreDuChamp)

/--
squares (the case F(t) = t² of BH 1991, th. I.6.1.2, for bounded f): for f, q, v ∈ 𝔻 with |f| ≤ M
a.e. and q = f² a.e., γ(q, v) = 2 f γ(f, v) a.e. (chain rule for t ↦ ((−R) ∨ (t ∧ R))², R = M + 1,
strictly differentiable outside {−R, R}).
-/
theorem gamma_sq_ae_eq (f q v : D.form.dom) {M : ℝ} (hM : ∀ᵐ x ∂μ, |(f : Lp ℝ 2 μ) x| ≤ M)
    (hq : ⇑(q : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x ^ 2) :
    ⇑(G.gamma q v) =ᵐ[μ] fun x => 2 * (f : Lp ℝ 2 μ) x * G.gamma f v x := by
  haveI : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
  obtain ⟨x₀, hx₀⟩ := hM.exists
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hx₀
  set R : ℝ := M + 1 with hRdef
  have hR0 : 0 ≤ R := by linarith
  have hMR : M < R := by linarith
  have hF := lipschitzWith_clamp_sq hR0
  have hd : ∀ t ∉ ({-R, R} : Set ℝ), HasStrictDerivAt (fun s : ℝ => (max (-R) (min s R)) ^ 2)
      (if |t| < R then 2 * t else 0) t := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    by_cases h : |t| < R
    · rw [if_pos h]
      exact hasStrictDerivAt_clamp_sq h
    · rw [if_neg h]
      have hlt : R < |t| := lt_of_le_of_ne (not_lt.1 h) (fun e => by
        rcases (abs_eq hR0).1 e.symm with h1 | h1
        · exact ht.2 h1
        · exact ht.1 h1)
      exact hasStrictDerivAt_clamp_sq_of_lt_abs hR0 hlt
  have hqF : ⇑(q : Lp ℝ 2 μ) =ᵐ[μ] fun x => (max (-R) (min ((f : Lp ℝ 2 μ) x) R)) ^ 2 := by
    filter_upwards [hq, hM] with x h1 h2
    rw [h1, min_eq_left (by linarith [(abs_le.1 h2).2]),
      max_eq_right (by linarith [(abs_le.1 h2).1])]
  have h := G.gamma_comp_ae_eq hF ((Set.countable_singleton R).insert (-R)) hd f v q hqF
  filter_upwards [h, hM] with x h1 h2
  rw [h1, if_pos (by linarith)]

/--
The contract `LeibnizRule` of `LocalCarreDuChampLevels` is proved: (the case F(s, t) = s t of BH
1991, cor. I.6.1.3, pp. 36–37, for two bounded factors): for essentially bounded f, g ∈ 𝔻, p ∈ 𝔻
equal a.e. to f g and v ∈ 𝔻, γ(p, v) = f γ(g, v) + g γ(f, v) a.e. (squares, then polarization f g =
¼((f + g)² − (f − g)²)).
-/
theorem leibnizRule : G.LeibnizRule := by
  intro f g p v hf hg hp
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
  set Q₁ : D.form.dom := ⟨q₁, m₁⟩ with hQ₁
  set Q₂ : D.form.dom := ⟨q₂, m₂⟩ with hQ₂
  have hpQ : p = (1 / 4 : ℝ) • (Q₁ - Q₂) := by
    apply QuadForm.dom_ext_ae
    filter_upwards [hp, hq₁, hq₂, Lp.coeFn_smul (1 / 4 : ℝ) (q₁ - q₂), Lp.coeFn_sub q₁ q₂,
      Lp.coeFn_add (f : Lp ℝ 2 μ) (g : Lp ℝ 2 μ), Lp.coeFn_sub (f : Lp ℝ 2 μ) (g : Lp ℝ 2 μ)]
      with x a b c d e k l
    change (p : Lp ℝ 2 μ) x = ((1 / 4 : ℝ) • (q₁ - q₂)) x
    rw [d, Pi.smul_apply, e, Pi.sub_apply, b, c, a, Submodule.coe_add, Submodule.coe_sub, k, l,
      Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have e₁ := G.gamma_sq_ae_eq (f + g) Q₁ v hs hq₁
  have e₂ := G.gamma_sq_ae_eq (f - g) Q₂ v hd hq₂
  have hsv : G.gamma (f + g) v = G.gamma f v + G.gamma g v := by
    rw [map_add, LinearMap.add_apply]
  have hdv : G.gamma (f - g) v = G.gamma f v - G.gamma g v := by
    rw [map_sub, LinearMap.sub_apply]
  rw [hpQ, map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply]
  filter_upwards [e₁, e₂, Lp.coeFn_smul (1 / 4 : ℝ) (G.gamma Q₁ v - G.gamma Q₂ v),
    Lp.coeFn_sub (G.gamma Q₁ v) (G.gamma Q₂ v), Lp.coeFn_add (G.gamma f v) (G.gamma g v),
    Lp.coeFn_sub (G.gamma f v) (G.gamma g v), Lp.coeFn_add (f : Lp ℝ 2 μ) (g : Lp ℝ 2 μ),
    Lp.coeFn_sub (f : Lp ℝ 2 μ) (g : Lp ℝ 2 μ)] with x a1 a2 a3 a4 a5 a6 a7 a8
  have a7' : ((f + g : D.form.dom) : Lp ℝ 2 μ) x = (f : Lp ℝ 2 μ) x + (g : Lp ℝ 2 μ) x := by
    rw [Submodule.coe_add]
    exact a7
  have a8' : ((f - g : D.form.dom) : Lp ℝ 2 μ) x = (f : Lp ℝ 2 μ) x - (g : Lp ℝ 2 μ) x := by
    rw [Submodule.coe_sub]
    exact a8
  rw [hsv, a5, Pi.add_apply, a7'] at a1
  rw [hdv, a6, Pi.sub_apply, a8'] at a2
  rw [a3, Pi.smul_apply, a4, Pi.sub_apply, a1, a2, smul_eq_mul]
  ring

end CarreDuChamp

/-! ## I. Quantified version (contract `LeibnizRuleStatement`) -/

/--
The quantified contract `LeibnizRuleStatement` is proved: `CarreDuChamp.LeibnizRule` holds for every
probability space `(Ω : Type)`, every local Dirichlet form and every carre du champ datum.
-/
theorem leibnizRuleStatement : LeibnizRuleStatement := by
  intro Ω _ μ _ D G
  exact G.leibnizRule

end LocalDirichletForm
end ErrorCalculus
