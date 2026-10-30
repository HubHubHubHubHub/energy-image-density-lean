import ErrorCalculus.Dirichlet.LocalCarreDuChampMultivariate
import ErrorCalculus.Dirichlet.ClosureCalculusLimits
import Mathlib.Analysis.Normed.Group.Indicator

/-!
# multivariate chain rule: the `ChainRule` contract proved for every m

## Main results
For a local Dirichlet form `D : LocalDirichletForm μ` on a probability space, equipped with its
carre du champ `G : D.CarreDuChamp` (ℰ(f, f) = ∫ γ(f, f) dμ), using `clampRule` and the tensor
approximants : clause (b) of `BHFunctionalCalculus` (BH 1991, th. I.6.1.2 and cor. I.6.1.3, pp.
36–37, generic version):

* K — grids on the box [−R, R]ᵐ (spacing δₙ = 2R/(n + 1)) and convergence of the coefficients of the
tensor approximants on the box.
* L — tools: |γ(T f, T′ g)| ≤ |γ(f, g)| by applying `clampRule` twice, energy bound for a chain-rule
element without Cauchy–Schwarz, **passage to the limit in γ** (`exists_mem_gamma_eq_of_tendsto`,
`gammaChain_of_tendsto`).
* M — (bounded u): `gammaChain_of_aeBounded`.
* N — (arbitrary u, clamps): `gammaChain_fderiv`.
* O — : `chainRuleDim` (every dimension m), **`chainRule : G.ChainRule`** (the contract is proved)
and **`chainRuleStatement : ChainRuleStatement`**.

The bridge connection is proved in `DprBridge.ChainRuleBridge`. The sigma-finite BH setting is
treated in `DprBridge.BH1991PrintedProof`. The chain rule for arbitrary Lipschitz F and necessity of
the Lipschitz assumption (paper) are outside this module.
The indicator bounds use Mathlib's `norm_indicator_le_norm_self`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option maxHeartbeats 800000

namespace ErrorCalculus

/-! ## K. Grids on the box [−R, R]ᵐ (real-variable part) -/

/--
Spacing of the n-th grid on the box [−R, R]: δₙ = 2R/(n + 1) (n + 1 cells, nodes −R + kδₙ, k ≤ n +
1).
-/
def boxGridStep (R : ℝ) (n : ℕ) : ℝ := 2 * R / ((n : ℝ) + 1)

/-- δₙ > 0 if R > 0. -/
theorem boxGridStep_pos {R : ℝ} (hR : 0 < R) (n : ℕ) : 0 < boxGridStep R n := by
  unfold boxGridStep
  positivity

/-- The grid of spacing δₙ starting at −R with n + 1 cells ends at R. -/
theorem neg_add_mul_boxGridStep (R : ℝ) (n : ℕ) : -R + ((n + 1 : ℕ) : ℝ) * boxGridStep R n = R := by
  unfold boxGridStep
  push_cast
  field_simp
  ring

/-- δₙ → 0. -/
theorem tendsto_boxGridStep (R : ℝ) : Tendsto (boxGridStep R) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 2 * R * (1 / ((n : ℝ) + 1))) atTop (𝓝 (2 * R * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  unfold boxGridStep
  ring

/--
tensor approximants on the n-th grid of the box [−R, R]ᵐ, with data A_k = F(x_k), B_{k,i} =
∂ᵢF(x_k).
-/
def gridBoxApprox {m : ℕ} (F : (Fin m → ℝ) → ℝ) (R : ℝ) (n : ℕ) : (Fin m → ℝ) → ℝ :=
  boxApprox (K := n + 1) (-R) (boxGridStep R n) (fun k => F (gridNode (-R) (boxGridStep R n) k))
    (fun k i => fderiv ℝ F (gridNode (-R) (boxGridStep R n) k) (Pi.single i 1))

/-- Coefficients cᵢⁿ of the approximant `gridBoxApprox`. -/
def gridBoxApproxCoeff {m : ℕ} (F : (Fin m → ℝ) → ℝ) (R : ℝ) (n : ℕ) :
    Fin m → (Fin m → ℝ) → ℝ :=
  boxApproxCoeff (K := n + 1) (-R) (boxGridStep R n)
    (fun k => F (gridNode (-R) (boxGridStep R n) k))
    (fun k i => fderiv ℝ F (gridNode (-R) (boxGridStep R n) k) (Pi.single i 1))

/--
On the grids of the box [−R, R]ᵐ: for F of class C¹ (`ContDiff ℝ 1 F`), R > 0 and ε > 0,
there exists N such that, for every n ≥ N and every y with |yⱼ| ≤ R for all j, |cᵢⁿ(y) − ∂ᵢF(y)| ≤
3ε for
every i (∂ᵢF(y) = DF(y)(eᵢ), eᵢ = `Pi.single i 1`) and |Gₙ(y) − F(y)| ≤ ε δₙ. Neither Lipschitz
continuity nor bounded derivatives are assumed.
Reference: Bouleau–Hirsch (1991), th. I.6.1.2.
-/
theorem exists_abs_gridBoxApproxCoeff_sub_le {m : ℕ} {F : (Fin m → ℝ) → ℝ} (hC : ContDiff ℝ 1 F)
    {R : ℝ} (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ y : Fin m → ℝ, (∀ j, |y j| ≤ R) →
      (∀ i, |gridBoxApproxCoeff F R n i y - fderiv ℝ F y (Pi.single i 1)| ≤ 3 * ε) ∧
        |gridBoxApprox F R n y - F y| ≤ ε * boxGridStep R n := by
  obtain ⟨δ₀, hδ₀, H⟩ := exists_abs_boxApproxCoeff_sub_le hC (-R) R hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * R / δ₀)
  refine ⟨N, fun n hn y hy => ?_⟩
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hδle : boxGridStep R n ≤ δ₀ := by
    unfold boxGridStep
    rw [div_le_iff₀ hn1]
    have h1 : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h2 := (div_lt_iff₀ hδ₀).1 hN
    nlinarith [mul_le_mul_of_nonneg_right h1 hδ₀.le]
  have hK := neg_add_mul_boxGridStep R n
  exact H (n + 1) _ (boxGridStep_pos hR n) hδle hK.le y fun j => by
    rw [hK]
    exact abs_le.1 (hy j)

/--
pointwise convergence of the coefficients on the box: for F of class C¹ (`ContDiff ℝ 1 F`), R > 0,
y with |yⱼ| ≤ R for all j, and fixed i, cᵢⁿ(y) → ∂ᵢF(y) = DF(y)(eᵢ) as n → ∞ (including at nodes).
-/
theorem tendsto_gridBoxApproxCoeff {m : ℕ} {F : (Fin m → ℝ) → ℝ} (hC : ContDiff ℝ 1 F) {R : ℝ}
    (hR : 0 < R) {y : Fin m → ℝ} (hy : ∀ j, |y j| ≤ R) (i : Fin m) :
    Tendsto (fun n => gridBoxApproxCoeff F R n i y) atTop (𝓝 (fderiv ℝ F y (Pi.single i 1))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_abs_gridBoxApproxCoeff_sub_le hC hR (ε := ε / 6) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have h := (hN n hn y hy).1 i
  linarith

/-!
## Clamps, energy and passage to the limit

The derivative coefficients of an L-Lipschitz C¹ function are bounded by L. Mathlib's
`norm_indicator_le_norm_self` bounds indicators by one.
-/

namespace LocalDirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {D : LocalDirichletForm μ}

namespace CarreDuChamp
variable (G : D.CarreDuChamp)

/--
Applying the clamp rule twice and using symmetry gives γ(a ∨ (f ∧ b), c ∨ (g ∧ d)) = 1_{]a,b[}(f)
1_{]c,d[}(g) γ(f, g) almost everywhere.
-/
theorem gamma_clamp_clamp_ae_eq (f g : D.form.dom) (a b c d : ℝ) :
    ⇑(G.gamma (D.clamp a b f) (D.clamp c d g)) =ᵐ[μ] fun x =>
      (Set.Ioo a b).indicator 1 ((f : Lp ℝ 2 μ) x) *
        ((Set.Ioo c d).indicator 1 ((g : Lp ℝ 2 μ) x) * G.gamma f g x) := by
  have h1 := G.clampRule f (D.clamp c d g) (D.clamp a b f) a b (D.coeFn_clamp a b f)
  have h2 := G.clampRule g f (D.clamp c d g) c d (D.coeFn_clamp c d g)
  rw [G.symm g f] at h2
  rw [G.symm f (D.clamp c d g)] at h1
  filter_upwards [h1, h2] with x e1 e2
  rw [e1, e2]

/-- Clamping both arguments gives |γ(a ∨ (f ∧ b), c ∨ (g ∧ d))| ≤ |γ(f, g)| almost everywhere. -/
theorem abs_gamma_clamp_clamp_le (f g : D.form.dom) (a b c d : ℝ) :
    ∀ᵐ x ∂μ, |G.gamma (D.clamp a b f) (D.clamp c d g) x| ≤ |G.gamma f g x| := by
  filter_upwards [G.gamma_clamp_clamp_ae_eq f g a b c d] with x hx
  rw [hx, abs_mul, abs_mul]
  have hind : ∀ (s : Set ℝ) (t : ℝ), |s.indicator (1 : ℝ → ℝ) t| ≤ 1 := fun s t => by
    simpa only [Real.norm_eq_abs, Pi.one_apply, abs_one] using
      norm_indicator_le_norm_self (s := s) (1 : ℝ → ℝ) t
  have h3 := abs_nonneg (G.gamma f g x)
  have h4 := abs_nonneg ((Set.Ioo c d).indicator (1 : ℝ → ℝ) ((g : Lp ℝ 2 μ) x))
  have h6 := mul_le_of_le_one_left h3 (hind (Set.Ioo c d) ((g : Lp ℝ 2 μ) x))
  have h7 := mul_le_of_le_one_left (mul_nonneg h4 h3)
    (hind (Set.Ioo a b) ((f : Lp ℝ 2 μ) x))
  exact h7.trans h6

/--
energy of a chain-rule element, without Cauchy–Schwarz: for p ∈ 𝔻, u ∈ 𝔻ᵐ and arbitrary functions aᵢ
: Ω → ℝ (no measurability required), if γ(p, v) = Σᵢ aᵢ γ(uᵢ, v) a.e. for every v ∈ 𝔻 and |aᵢ| ≤ B
a.e. for every i, then ℰ(p) ≤ B² Σᵢ Σⱼ ∫ |γ(uⱼ, uᵢ)| dμ (ℰ(p) = ∫ γ(p, p), γ(p, p) = Σᵢⱼ aᵢ aⱼ γ(uⱼ,
uᵢ)).
-/
theorem energy_le_of_gamma_eq {m : ℕ} (u : Fin m → D.form.dom) (p : D.form.dom)
    (a : Fin m → Ω → ℝ) {B : ℝ}
    (hγ : ∀ v : D.form.dom, ⇑(G.gamma p v) =ᵐ[μ] fun x => ∑ i, a i x * G.gamma (u i) v x)
    (ha : ∀ i, ∀ᵐ x ∂μ, |a i x| ≤ B) :
    D.form.E p p ≤ B ^ 2 * ∑ i, ∑ j, ∫ x, |G.gamma (u j) (u i) x| ∂μ := by
  have hpt : ∀ᵐ x ∂μ, G.gamma p p x ≤ B ^ 2 * ∑ i, ∑ j, |G.gamma (u j) (u i) x| := by
    have h2 : ∀ᵐ x ∂μ, ∀ i, G.gamma p (u i) x = ∑ j, a j x * G.gamma (u j) (u i) x :=
      ae_all_iff.2 fun i => hγ (u i)
    filter_upwards [hγ p, h2, ae_all_iff.2 ha] with x h1 h3 h4
    rw [h1]
    have e : ∀ i, G.gamma (u i) p x = ∑ j, a j x * G.gamma (u j) (u i) x := fun i => by
      rw [G.symm (u i) p]
      exact h3 i
    simp only [e]
    calc ∑ i, a i x * ∑ j, a j x * G.gamma (u j) (u i) x
        ≤ ∑ i, |a i x * ∑ j, a j x * G.gamma (u j) (u i) x| :=
          Finset.sum_le_sum fun i _ => le_abs_self _
      _ ≤ ∑ i, B ^ 2 * ∑ j, |G.gamma (u j) (u i) x| := Finset.sum_le_sum fun i _ => by
          have hB : 0 ≤ B := (abs_nonneg _).trans (h4 i)
          rw [abs_mul, sq, mul_assoc]
          refine mul_le_mul (h4 i) ?_ (abs_nonneg _) hB
          rw [Finset.mul_sum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (h4 j) (abs_nonneg _)
      _ = B ^ 2 * ∑ i, ∑ j, |G.gamma (u j) (u i) x| := by rw [Finset.mul_sum]
  have hi : ∀ i, Integrable (fun x => ∑ j, |G.gamma (u j) (u i) x|) μ := fun i =>
    integrable_finsetSum _ fun j _ => (L1.integrable_coeFn _).abs
  have hint : Integrable (fun x => B ^ 2 * ∑ i, ∑ j, |G.gamma (u j) (u i) x|) μ :=
    (integrable_finsetSum _ fun i _ => hi i).const_mul _
  rw [G.energy_eq_integral p]
  refine (integral_mono_ae (L1.integrable_coeFn _) hint hpt).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hi i]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    integral_finsetSum _ fun j _ => (L1.integrable_coeFn _).abs

/--
passage to the limit in γ (closedness, tool (W) of dominated convergence, test functions): let pₙ ∈
𝔻 and w ∈ L² with pₙ → w in L² and ℰ(pₙ) ≤ C for every n, and g, h : 𝔻 → (Ω → ℝ) with h_v
integrable, |γ(pₙ, v)| ≤ h_v a.e. for every v and n, and γ(pₙ, v) → g_v a.e. for every v. Then w ∈ 𝔻
and γ(w, v) = g_v a.e. for every v ∈ 𝔻 (neither w ∈ 𝔻 nor measurability of g_v is assumed).
-/
theorem exists_mem_gamma_eq_of_tendsto {p : ℕ → D.form.dom} {w : Lp ℝ 2 μ} {C : ℝ}
    (hT : Tendsto (fun n => ((p n : D.form.dom) : Lp ℝ 2 μ)) atTop (𝓝 w))
    (hE : ∀ n, D.form.E (p n) (p n) ≤ C) (g h : D.form.dom → Ω → ℝ)
    (hh : ∀ v, Integrable (h v) μ) (hb : ∀ v n, ∀ᵐ x ∂μ, |G.gamma (p n) v x| ≤ h v x)
    (hlim : ∀ v, ∀ᵐ x ∂μ, Tendsto (fun n => G.gamma (p n) v x) atTop (𝓝 (g v x))) :
    ∃ hw : w ∈ D.form.dom, ∀ v : D.form.dom, ⇑(G.gamma ⟨w, hw⟩ v) =ᵐ[μ] g v := by
  obtain ⟨hw, -⟩ := D.closed.mem_dom_of_tendsto_of_energy_le hT hE
  refine ⟨hw, fun v => ?_⟩
  have htm : AEStronglyMeasurable (g v) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => Lp.aestronglyMeasurable _) (hlim v)
  have hgb : ∀ᵐ x ∂μ, ‖g v x‖ ≤ h v x := by
    filter_upwards [ae_all_iff.2 (hb v), hlim v] with x h1 h2
    exact le_of_tendsto' h2.norm fun n => by rw [Real.norm_eq_abs]; exact h1 n
  have hti : Integrable (g v) μ := Integrable.mono' (hh v) htm hgb
  apply D.toDirichletForm.ae_eq_of_integral_mul_eq D.denseRange_toLp (L1.integrable_coeFn _) hti
  intro z hz
  have h1 := G.tendsto_integral_mul_gamma (y := ⟨w, hw⟩) hE hT hz v
  obtain ⟨Cz, hCz⟩ := (Capacity.DirichletForm.mem_bddSpace _).1 hz
  have h2 : Tendsto (fun n => ∫ ω, D.toDirichletForm.toLp z ω * G.gamma (p n) v ω ∂μ) atTop
      (𝓝 (∫ ω, D.toDirichletForm.toLp z ω * g v ω ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => Cz * h v ω)
      (fun n => (Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _)) ((hh v).const_mul _)
      (fun n => ?_) ?_
    · filter_upwards [hCz, hb v n] with ω hω h3
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul hω h3 (abs_nonneg _) ((abs_nonneg _).trans hω)
    · filter_upwards [hlim v] with ω hω
      exact hω.const_mul _
  exact tendsto_nhds_unique h1 h2

/--
chain-rule form of passage to the limit: if w = Φ(u) a.e., pₙ → w in L², ℰ(pₙ) ≤ C for every n,
γ(pₙ, v) = Σᵢ aᵢⁿ γ(uᵢ, v) a.e. for all n and v, |aᵢⁿ| ≤ B a.e. for all n and i, and aᵢⁿ → cᵢ(u)
a.e. for every i, then `GammaChain u Φ c`. The aᵢⁿ : Ω → ℝ are arbitrary (no measurability is
required: the integrated sequence is γ(pₙ, v)).
-/
theorem gammaChain_of_tendsto {m : ℕ} {u : Fin m → D.form.dom} {Φ : (Fin m → ℝ) → ℝ}
    {c : Fin m → (Fin m → ℝ) → ℝ} {p : ℕ → D.form.dom} {w : Lp ℝ 2 μ} {C B : ℝ}
    (hw : ⇑w =ᵐ[μ] fun x => Φ fun j => (u j : Lp ℝ 2 μ) x)
    (hT : Tendsto (fun n => ((p n : D.form.dom) : Lp ℝ 2 μ)) atTop (𝓝 w))
    (hE : ∀ n, D.form.E (p n) (p n) ≤ C) (a : ℕ → Fin m → Ω → ℝ)
    (hγ : ∀ n (v : D.form.dom),
      ⇑(G.gamma (p n) v) =ᵐ[μ] fun x => ∑ i, a n i x * G.gamma (u i) v x)
    (ha : ∀ n i, ∀ᵐ x ∂μ, |a n i x| ≤ B)
    (hlim : ∀ i, ∀ᵐ x ∂μ,
      Tendsto (fun n => a n i x) atTop (𝓝 (c i fun j => (u j : Lp ℝ 2 μ) x))) :
    G.GammaChain u Φ c := by
  obtain ⟨hw', hγw⟩ := G.exists_mem_gamma_eq_of_tendsto hT hE
    (fun v x => ∑ i, c i (fun j => (u j : Lp ℝ 2 μ) x) * G.gamma (u i) v x)
    (fun v x => ∑ i, B * |G.gamma (u i) v x|)
    (fun v => integrable_finsetSum _ fun i _ => (L1.integrable_coeFn _).abs.const_mul B)
    (fun v n => by
      filter_upwards [hγ n v, ae_all_iff.2 (ha n)] with x h1 h2
      rw [h1]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (h2 i) (abs_nonneg _))
    (fun v => by
      filter_upwards [ae_all_iff.2 fun n => hγ n v, ae_all_iff.2 hlim] with x h1 h2
      simp only [h1]
      exact tendsto_finsetSum _ fun i _ => (h2 i).mul_const _)
  exact ⟨⟨w, hw'⟩, hw, hγw⟩

/-! ## M. bounded u -/

/--
(BH 1991, th. I.6.1.2, generic version, bounded u): for u ∈ 𝔻ᵐ with |uᵢ| ≤ M a.e. for every i, and F
of class C¹ (`ContDiff ℝ 1 F`) and L-Lipschitz (`LipschitzWith L F`), `GammaChain u F ∂F`:
there exists p ∈ 𝔻 equal a.e. to F(u) with γ(p, v) = Σᵢ ∂ᵢF(u) γ(uᵢ, v) a.e. for every v ∈ 𝔻 (∂ᵢF(y)
=
DF(y)(eᵢ)). Bounded derivatives are not assumed (|∂ᵢF| ≤ L follows from Lipschitz continuity).
Proof: tensor approximants on the grids of [−R, R]ᵐ, R = |M| + 1, with shifted sequence n ↦ n + N₀
so that |cᵢⁿ| ≤ L + 3 for every n; passage to the limit by `gammaChain_of_tendsto`.
-/
theorem gammaChain_of_aeBounded {m : ℕ} (u : Fin m → D.form.dom) {M : ℝ}
    (hu : ∀ i, ∀ᵐ x ∂μ, |(u i : Lp ℝ 2 μ) x| ≤ M) {F : (Fin m → ℝ) → ℝ} {L : ℝ≥0}
    (hC : ContDiff ℝ 1 F) (hL : LipschitzWith L F) :
    G.GammaChain u F (fun i y => fderiv ℝ F y (Pi.single i 1)) := by
  have hR : (0 : ℝ) < |M| + 1 := by positivity
  have hbox : ∀ᵐ x ∂μ, ∀ j, |(u j : Lp ℝ 2 μ) x| ≤ |M| + 1 := by
    filter_upwards [ae_all_iff.2 hu] with x hx j
    linarith [hx j, le_abs_self M]
  obtain ⟨N₀, hN₀⟩ := exists_abs_gridBoxApproxCoeff_sub_le hC hR one_pos
  have hch : ∀ n, G.GammaChain u (gridBoxApprox F (|M| + 1) n)
      (gridBoxApproxCoeff F (|M| + 1) n) :=
    fun n => G.gammaChain_boxApprox u hu (boxGridStep_pos hR n) _ _
  choose p hpΦ hpγ using hch
  obtain ⟨w, hw⟩ := ErrorStructure.exists_composition (μ := μ) (fun j => (u j : Lp ℝ 2 μ)) hL
  have hval : ∀ n, ∀ᵐ x ∂μ, |((p (n + N₀) : D.form.dom) : Lp ℝ 2 μ) x - w x| ≤
      boxGridStep (|M| + 1) (n + N₀) := by
    intro n
    filter_upwards [hpΦ (n + N₀), hw, hbox] with x h1 h2 h3
    rw [h1, h2]
    simpa only [one_mul] using (hN₀ (n + N₀) (Nat.le_add_left N₀ n) _ h3).2
  have hT : Tendsto (fun n => ((p (n + N₀) : D.form.dom) : Lp ℝ 2 μ)) atTop (𝓝 w) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      ((tendsto_boxGridStep (|M| + 1)).comp (tendsto_add_atTop_nat N₀))
    show _ ≤ boxGridStep (|M| + 1) (n + N₀)
    have h := Lp.norm_le_of_ae_bound (boxGridStep_pos hR (n + N₀)).le
      (f := ((p (n + N₀) : D.form.dom) : Lp ℝ 2 μ) - w) (by
        filter_upwards [Lp.coeFn_sub ((p (n + N₀) : D.form.dom) : Lp ℝ 2 μ) w, hval n]
          with x h1 h2
        rw [h1, Pi.sub_apply, Real.norm_eq_abs]
        exact h2)
    simpa [measureUnivNNReal] using h
  have hcoef : ∀ n i, ∀ᵐ x ∂μ,
      |gridBoxApproxCoeff F (|M| + 1) (n + N₀) i (fun j => (u j : Lp ℝ 2 μ) x)| ≤ (L : ℝ) + 3 := by
    intro n i
    filter_upwards [hbox] with x hx
    have h1 := (hN₀ (n + N₀) (Nat.le_add_left N₀ n) _ hx).1 i
    have h2 := fderiv_coefficient_bound hL (fun j => (u j : Lp ℝ 2 μ) x) i
    have h3 := abs_sub_abs_le_abs_sub
      (gridBoxApproxCoeff F (|M| + 1) (n + N₀) i fun j => (u j : Lp ℝ 2 μ) x)
      (fderiv ℝ F (fun j => (u j : Lp ℝ 2 μ) x) (Pi.single i 1))
    linarith
  have hE : ∀ n, D.form.E (p (n + N₀)) (p (n + N₀)) ≤
      ((L : ℝ) + 3) ^ 2 * ∑ i, ∑ j, ∫ x, |G.gamma (u j) (u i) x| ∂μ := fun n =>
    G.energy_le_of_gamma_eq u (p (n + N₀))
      (fun i x => gridBoxApproxCoeff F (|M| + 1) (n + N₀) i (fun j => (u j : Lp ℝ 2 μ) x))
      (hpγ (n + N₀)) (hcoef n)
  exact G.gammaChain_of_tendsto (p := fun n => p (n + N₀)) hw hT hE
    (fun n i x => gridBoxApproxCoeff F (|M| + 1) (n + N₀) i (fun j => (u j : Lp ℝ 2 μ) x))
    (fun n v => hpγ (n + N₀) v) hcoef
    (fun i => by
      filter_upwards [hbox] with x hx
      exact (tendsto_gridBoxApproxCoeff hC hR hx i).comp (tendsto_add_atTop_nat N₀))

/-! ## N. arbitrary u (clamps) -/

/--
(BH 1991, th. I.6.1.2, generic version): for every u ∈ 𝔻ᵐ (no boundedness) and F of class C¹
(`ContDiff ℝ 1 F`) and L-Lipschitz (`LipschitzWith L F`), `GammaChain u F ∂F`: there exists p ∈ 𝔻
equal a.e. to F(u) with γ(p, v) = Σᵢ ∂ᵢF(u) γ(uᵢ, v) a.e. for every v ∈ 𝔻. Proof: applied to clamps
Tₙuᵢ = (−n) ∨ (uᵢ ∧ n); energy bounded using |γ(Tₙuᵢ, Tₙuⱼ)| ≤ |γ(uᵢ, uⱼ)|; γ(Tₙuᵢ, v) =
1_{]−n,n[}(uᵢ) γ(uᵢ, v) by `clampRule`; eventually constant coefficients.
-/
theorem gammaChain_fderiv {m : ℕ} (u : Fin m → D.form.dom) {F : (Fin m → ℝ) → ℝ} {L : ℝ≥0}
    (hC : ContDiff ℝ 1 F) (hL : LipschitzWith L F) :
    G.GammaChain u F (fun i y => fderiv ℝ F y (Pi.single i 1)) := by
  have hch : ∀ n : ℕ, G.GammaChain (fun i => D.clamp (-(n : ℝ)) n (u i)) F
      (fun i y => fderiv ℝ F y (Pi.single i 1)) :=
    fun n => G.gammaChain_of_aeBounded _ (fun i => D.abs_clamp_le n (u i)) hC hL
  choose p hpΦ hpγ using hch
  obtain ⟨w, hw⟩ := ErrorStructure.exists_composition (μ := μ) (fun j => (u j : Lp ℝ 2 μ)) hL
  have hTc : ∀ᵐ x ∂μ, ∀ n : ℕ, ∀ i, ((D.clamp (-(n : ℝ)) n (u i) : D.form.dom) : Lp ℝ 2 μ) x =
      max (-(n : ℝ)) (min ((u i : Lp ℝ 2 μ) x) n) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun i => D.coeFn_clamp _ _ (u i)
  have hev : ∀ x, ∀ᶠ n : ℕ in atTop, ∀ i, |(u i : Lp ℝ 2 μ) x| < n := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt (∑ i, |(u i : Lp ℝ 2 μ) x|)
    filter_upwards [eventually_ge_atTop N] with n hn i
    have h1 : |(u i : Lp ℝ 2 μ) x| ≤ ∑ j, |(u j : Lp ℝ 2 μ) x| :=
      Finset.single_le_sum (fun j _ => abs_nonneg ((u j : Lp ℝ 2 μ) x)) (Finset.mem_univ i)
    have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hid : ∀ {n : ℕ} {t : ℝ}, |t| < n → max (-(n : ℝ)) (min t n) = t := fun h => by
    rw [min_eq_left (abs_lt.1 h).2.le, max_eq_right (abs_lt.1 h).1.le]
  -- (a) L² convergence: |F(Tₙu) − F(u)| ≤ L Σᵢ |uᵢ|, and F(Tₙu) = F(u) when n > maxᵢ |uᵢ|.
  have hgx : ∀ᵐ x ∂μ, ((L : ℝ) • ∑ i, |(u i : Lp ℝ 2 μ)|) x =
      (L : ℝ) * ∑ i, |(u i : Lp ℝ 2 μ) x| := by
    filter_upwards [Lp.coeFn_smul (L : ℝ) (∑ i, |(u i : Lp ℝ 2 μ)|),
      lp_coeFn_sum Finset.univ (fun i => |(u i : Lp ℝ 2 μ)|),
      ae_all_iff.2 fun i => Lp.coeFn_abs (u i : Lp ℝ 2 μ)] with x h1 h2 h3
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    simp only [h3]
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, (((p n : D.form.dom) : Lp ℝ 2 μ) - w) x =
      F (fun j => ((D.clamp (-(n : ℝ)) n (u j) : D.form.dom) : Lp ℝ 2 μ) x) -
        F (fun j => (u j : Lp ℝ 2 μ) x) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_sub ((p n : D.form.dom) : Lp ℝ 2 μ) w, hpΦ n, hw] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hT0 : Tendsto (fun n => ((p n : D.form.dom) : Lp ℝ 2 μ) - w) atTop (𝓝 0) := by
    apply lp_two_tendsto_zero_of_dominated _ ((L : ℝ) • ∑ i, |(u i : Lp ℝ 2 μ)|)
    · intro n
      filter_upwards [hall, hgx, hTc] with x h1 h4 h5
      rw [h1 n, h4]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) * ∑ i, |(u i : Lp ℝ 2 μ) x|)]
      have hd := hL.dist_le_mul (fun j => ((D.clamp (-(n : ℝ)) n (u j) : D.form.dom) : Lp ℝ 2 μ) x)
        (fun j => (u j : Lp ℝ 2 μ) x)
      rw [Real.dist_eq] at hd
      refine hd.trans (mul_le_mul_of_nonneg_left ?_ L.2)
      refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
      rw [Real.dist_eq, h5 n i]
      exact (abs_clamp_sub_le (Nat.cast_nonneg n) _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg ((u j : Lp ℝ 2 μ) x)) (Finset.mem_univ i))
    · filter_upwards [hall, hTc] with x h1 h2
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      rw [h1 n]
      have e : (fun j => ((D.clamp (-(n : ℝ)) n (u j) : D.form.dom) : Lp ℝ 2 μ) x) =
          fun j => (u j : Lp ℝ 2 μ) x := funext fun j => by rw [h2 n j, hid (hn j)]
      rw [e, sub_self]
  have hT : Tendsto (fun n => ((p n : D.form.dom) : Lp ℝ 2 μ)) atTop (𝓝 w) := by
    have h := hT0.add_const w
    simp only [sub_add_cancel, zero_add] at h
    exact h
  -- (b) Bounded energy, without Cauchy–Schwarz.
  have hE : ∀ n, D.form.E (p n) (p n) ≤
      (L : ℝ) ^ 2 * ∑ i, ∑ j, ∫ x, |G.gamma (u j) (u i) x| ∂μ := by
    intro n
    refine (G.energy_le_of_gamma_eq (fun i => D.clamp (-(n : ℝ)) n (u i)) (p n)
      (fun i x => fderiv ℝ F (fun j => ((D.clamp (-(n : ℝ)) n (u j) : D.form.dom) :
        Lp ℝ 2 μ) x) (Pi.single i 1)) (hpγ n)
      (fun i => Eventually.of_forall fun x => fderiv_coefficient_bound hL _ i)).trans ?_
    refine mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_) (sq_nonneg _)
    exact integral_mono_ae (L1.integrable_coeFn _).abs (L1.integrable_coeFn _).abs
      (G.abs_gamma_clamp_clamp_le (u j) (u i) _ _ _ _)
  -- (d) Coefficients: γ(Tₙuᵢ, v) = 1_{]−n,n[}(uᵢ) γ(uᵢ, v).
  have hγ : ∀ n (v : D.form.dom), ⇑(G.gamma (p n) v) =ᵐ[μ] fun x =>
      ∑ i, (fderiv ℝ F (fun j => ((D.clamp (-(n : ℝ)) n (u j) : D.form.dom) : Lp ℝ 2 μ) x)
        (Pi.single i 1) * (Set.Ioo (-(n : ℝ)) n).indicator 1 ((u i : Lp ℝ 2 μ) x)) *
          G.gamma (u i) v x := by
    intro n v
    filter_upwards [hpγ n v, ae_all_iff.2 fun i =>
      G.clampRule (u i) v (D.clamp (-(n : ℝ)) n (u i)) _ _ (D.coeFn_clamp _ _ (u i))] with x h1 h2
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2 i, mul_assoc]
  have hind : ∀ (s : Set ℝ) (t : ℝ), |s.indicator (1 : ℝ → ℝ) t| ≤ 1 := fun s t => by
    simpa only [Real.norm_eq_abs, Pi.one_apply, abs_one] using
      norm_indicator_le_norm_self (s := s) (1 : ℝ → ℝ) t
  have ha : ∀ (n : ℕ) i, ∀ᵐ x ∂μ,
      |fderiv ℝ F (fun j => ((D.clamp (-(n : ℝ)) n (u j) : D.form.dom) : Lp ℝ 2 μ) x)
        (Pi.single i 1) * (Set.Ioo (-(n : ℝ)) n).indicator 1 ((u i : Lp ℝ 2 μ) x)| ≤ (L : ℝ) :=
    fun n i => Eventually.of_forall fun x => by
      rw [abs_mul]
      calc _ ≤ (L : ℝ) * 1 := mul_le_mul (fderiv_coefficient_bound hL _ i)
            (hind _ _) (abs_nonneg _) L.2
        _ = L := mul_one _
  have hlim : ∀ i, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ =>
      fderiv ℝ F (fun j => ((D.clamp (-(n : ℝ)) n (u j) : D.form.dom) : Lp ℝ 2 μ) x)
        (Pi.single i 1) * (Set.Ioo (-(n : ℝ)) n).indicator 1 ((u i : Lp ℝ 2 μ) x)) atTop
      (𝓝 (fderiv ℝ F (fun j => (u j : Lp ℝ 2 μ) x) (Pi.single i 1))) := by
    intro i
    filter_upwards [hTc] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev x] with n hn
    have e : (fun j => ((D.clamp (-(n : ℝ)) n (u j) : D.form.dom) : Lp ℝ 2 μ) x) =
        fun j => (u j : Lp ℝ 2 μ) x := funext fun j => by rw [hx n j, hid (hn j)]
    have hmem : (u i : Lp ℝ 2 μ) x ∈ Set.Ioo (-(n : ℝ)) n := abs_lt.1 (hn i)
    rw [e, Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
  exact G.gammaChain_of_tendsto (p := p) hw hT hE _ hγ ha hlim

/-! ## O. the `ChainRule` contract for every m -/

/--
dimension-m part of the contract, for every m (including m = 0): for u ∈ 𝔻ᵐ and F : ℝᵐ → ℝ of class
C¹ (`ContDiff ℝ 1 F`) and L-Lipschitz (`LipschitzWith L F`), every class w ∈ L² equal a.e. to F(u)
lies in 𝔻 and γ(w, v) = Σᵢ ∂ᵢF(u) γ(uᵢ, v) a.e. for every v ∈ 𝔻 (the reduction
`chainRuleDim_of_gammaChain` ).
-/
theorem chainRuleDim (m : ℕ) : G.ChainRuleDim m :=
  G.chainRuleDim_of_gammaChain fun u _ _ hC hL => G.gammaChain_fderiv u hC hL

/--
**proves the contract `ChainRule`** (clause (b) of `BHFunctionalCalculus`, BH 1991, th. I.6.1.2 and
cor. I.6.1.3, pp. 36–37, generic version): for m > 0, u ∈ 𝔻ᵐ, F : ℝᵐ → ℝ of class C¹ (`ContDiff ℝ 1
F`) and L-Lipschitz (`LipschitzWith L F`), every class w ∈ L² equal a.e. to F(u) lies in 𝔻 and γ(w,
v) = Σᵢ ∂ᵢF(u) γ(uᵢ, v) a.e. for every v ∈ 𝔻 (∂ᵢF(y) = DF(y)(eᵢ)). Neither bounded u nor bounded
derivatives are assumed.
-/
theorem chainRule : G.ChainRule := fun m _ => G.chainRuleDim m

end CarreDuChamp

/--
**proves the quantified contract `ChainRuleStatement`** (BH 1991, th. I.6.1.2 and cor. I.6.1.3):
`CarreDuChamp.ChainRule` holds for every probability space `(Ω : Type)`, every local Dirichlet form
and every carre du champ datum.
-/
theorem chainRuleStatement : ChainRuleStatement := by
  intro Ω _ μ _ D G
  exact G.chainRule

end LocalDirichletForm

end ErrorCalculus
