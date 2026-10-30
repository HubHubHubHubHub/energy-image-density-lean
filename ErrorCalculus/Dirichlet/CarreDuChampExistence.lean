import ErrorCalculus.Dirichlet.CarreDuChampApprox
import ErrorCalculus.Dirichlet.DirichletFormTruncation

/-!
# Carre du champ (BH 1991, ch. I § 4.1), part 2: definition 4.1.2, proposition 4.1.3, named Γ

## Main results
Continuation of `ErrorCalculus.Dirichlet.CarreDuChampApprox` (prop. 4.1.1). Framework:
`DirichletForm μ`, for arbitrary μ; density of 𝔻 in L² (BH 1.1.1) is the named hypothesis `hd :
DenseRange D.toLp`, used only where needed.

* F. Test functions: approximation of indicators by 𝔻 ∩ L^∞ (start of the proof of 4.1.3),
uniqueness and positivity in L¹ using test functions, density of 𝔻 ∩ L^∞ in 𝔻.
* G. Continuity of h ↦ 2ℰ(fh, f) − ℰ(h, f²) in the L^∞ norm (`abs_bhS_self_le`), definition 4.1.2
(`AdmitsCarreDuChamp`, property (R)), characteristic property (`IsCarreDuChamp`); proposition 4.1.3:
existence, uniqueness, positivity, symmetry, ‖Γ(f, f)‖_{L¹} ≤ 2ℰ(f), pointwise Cauchy–Schwarz,
converse and characterization; ∫ Γ(f, f) = 2ℰ(f) only under the hypothesis "1 ∈ 𝔻, ℰ(1) = 0" (no
claim of ℰ = ½ ∫ Γ in general).
* Further results: the named carre du champ operator and its characterization lemmas, the literal
statement of 4.1.3, and 4.1.1 with the essential bound ‖h‖_{L^∞}.
* Products with arbitrary representatives: 4.1.1 and the BH form with arbitrary representatives of
the products.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity
namespace DirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## F. Test functions: approximation of indicators by 𝔻 ∩ L^∞ -/

section Generic

/-- A bilinear map bounded by ‖x‖² + ‖y‖² is bounded by 2 ‖x‖ ‖y‖ (homogeneity). -/
theorem norm_le_of_sq_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →ₗ[ℝ] E →ₗ[ℝ] F)
    (h : ∀ x y, ‖B x y‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2) (x y : E) : ‖B x y‖ ≤ 2 * ‖x‖ * ‖y‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have ha : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hb : 0 < ‖y‖ := norm_pos_iff.2 hy
  have h1 := h (‖x‖⁻¹ • x) (‖y‖⁻¹ • y)
  simp only [map_smul, LinearMap.smul_apply, norm_smul, norm_inv, norm_norm] at h1
  rw [inv_mul_cancel₀ ha.ne', inv_mul_cancel₀ hb.ne'] at h1
  have e : ‖B x y‖ = ‖x‖ * ‖y‖ * (‖x‖⁻¹ * (‖y‖⁻¹ * ‖B x y‖)) := by
    field_simp
  rw [e]
  have hp : 0 < ‖x‖ * ‖y‖ := mul_pos ha hb
  nlinarith

/-- Two continuous bilinear maps agreeing on a dense set are equal. -/
theorem clm₂_ext_of_dense {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set E} (hS : Dense S)
    {A B : E →L[ℝ] E →L[ℝ] F} (h : ∀ x ∈ S, ∀ y ∈ S, A x y = B x y) : A = B := by
  have h1 : Set.EqOn (⇑A) (⇑B) S := fun x hx => ContinuousLinearMap.ext fun y =>
    congrFun (Continuous.ext_on hS (A x).continuous (B x).continuous fun y hy => h x hx y hy) y
  exact DFunLike.coe_injective (Continuous.ext_on hS A.continuous B.continuous h1)

end Generic

variable (D : DirichletForm μ)

section TestFunctions

/-- Density of 𝔻 in L² (BH hypothesis 1.1.1), in the form. -/
theorem dense_dom (hd : DenseRange D.toLp) : Dense (D.form.dom : Set (Lp ℝ 2 μ)) := by
  have he : Set.range D.toLp = (D.form.dom : Set (Lp ℝ 2 μ)) := by
    ext f
    constructor
    · rintro ⟨x, rfl⟩
      exact (D.form.formToDomain x).2
    · intro hf
      exact ⟨D.form.formToDomain.symm ⟨f, hf⟩, by rw [toLp_apply, LinearEquiv.apply_symm_apply]⟩
  rw [← he]
  exact hd

/--
BH 1991, ch. I § 4.1, start of the proof of proposition 4.1.3 (p. 17): "any function k ∈ L¹ ∩ L^∞, k
≥ 0, is the almost everywhere limit of a uniformly bounded sequence of positive elements of 𝔻 ∩ L^∞
(λR_λ k → k in L², subsequence)", for k the indicator of a finite-measure set, under density of 𝔻 in
L².

Every indicator 1_A (μ(A) < ∞) is the a.e. limit of a sequence of elements of 𝔻 ∩ L^∞ taking
values in [0, 1].
-/
theorem exists_approx_indicator (hd : DenseRange D.toLp) {A : Set Ω} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) :
    ∃ z : ℕ → D.Space, (∀ n, z n ∈ D.bddSpace) ∧
      (∀ n, ∀ᵐ ω ∂μ, 0 ≤ D.toLp (z n) ω ∧ D.toLp (z n) ω ≤ 1) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => D.toLp (z n) ω) atTop
        (𝓝 (A.indicator (fun _ => (1 : ℝ)) ω)) := by
  set e : Lp ℝ 2 μ := indicatorConstLp 2 hA hμA (1 : ℝ) with he
  have hei : ⇑e =ᵐ[μ] A.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
  have he0 : ∀ᵐ ω ∂μ, 0 ≤ e ω := by
    filter_upwards [hei] with ω h
    rw [h]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have he1 : ∀ᵐ ω ∂μ, e ω ≤ 1 := by
    filter_upwards [hei] with ω h
    rw [h]
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem hω]; exact zero_le_one
  have hbp := QuadForm.resolventParameter_pos
  set w : ℕ → D.Space := fun n => D.form.formToDomain.symm
    (D.form.betaResolventDom D.closed (QuadForm.resolventParameter n) (hbp n) e) with hw
  have hwL : ∀ n, D.toLp (w n) = D.sres (QuadForm.resolventParameter n) (hbp n) e := by
    intro n
    rw [D.sres_apply, hw, toLp_apply, LinearEquiv.apply_symm_apply]
  have hb01 : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ D.toLp (w n) ω ∧ D.toLp (w n) ω ≤ 1 := by
    intro n
    filter_upwards [D.sres_nonneg _ (hbp n) e he0, D.sres_le _ (hbp n) e zero_le_one he1]
      with ω h1 h2
    rw [hwL n]
    exact ⟨h1, h2⟩
  have hL2 : Tendsto (fun n => D.toLp (w n)) atTop (𝓝 e) := by
    have h := D.form.tendsto_beta_resolvent D.closed (D.dense_dom hd) QuadForm.resolventParameter
      hbp QuadForm.tendsto_resolventParameter e
    refine h.congr fun n => ?_
    rw [hwL n, D.sres_eq]
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  refine ⟨fun n => w (ns n), fun n => ⟨1, ?_⟩, fun n => hb01 (ns n), ?_⟩
  · filter_upwards [hb01 (ns n)] with ω h
    exact abs_le.2 ⟨by linarith [h.1], h.2⟩
  · filter_upwards [hae, hei] with ω h1 h2
    rw [← h2]
    exact h1

/-- Dominated convergence along the approximants of 1_A. -/
theorem tendsto_integral_mul_approx {z : ℕ → D.Space}
    (hz : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ D.toLp (z n) ω ∧ D.toLp (z n) ω ≤ 1) {A : Set Ω}
    (hA : MeasurableSet A)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => D.toLp (z n) ω) atTop
      (𝓝 (A.indicator (fun _ => (1 : ℝ)) ω)))
    {φ : Ω → ℝ} (hφ : Integrable φ μ) :
    Tendsto (fun n => ∫ ω, D.toLp (z n) ω * φ ω ∂μ) atTop (𝓝 (∫ ω in A, φ ω ∂μ)) := by
  rw [← integral_indicator hA]
  refine tendsto_integral_of_dominated_convergence (fun ω => ‖φ ω‖)
    (fun n => (Lp.aestronglyMeasurable _).mul hφ.1) hφ.norm (fun n => ?_) ?_
  · filter_upwards [hz n] with ω h
    rw [norm_mul, Real.norm_eq_abs (D.toLp (z n) ω), abs_of_nonneg h.1]
    exact mul_le_of_le_one_left (norm_nonneg _) h.2
  · filter_upwards [hlim] with ω h
    have h2 := h.mul_const (φ ω)
    have heq : A.indicator (fun _ => (1 : ℝ)) ω * φ ω = A.indicator φ ω := by
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, one_mul]
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
    rw [heq] at h2
    exact h2

/-- The pairing ⟨h, G⟩ = ∫ h G (h ∈ 𝔻 ∩ L^∞, G ∈ L¹). -/
def pair (z : D.Space) (G : Lp ℝ 1 μ) : ℝ := ∫ ω, D.toLp z ω * G ω ∂μ

/-- The product of a bounded form representative and an L¹ function is integrable. -/
theorem integrable_pair {z : D.Space} (hz : z ∈ D.bddSpace) (G : Lp ℝ 1 μ) :
    Integrable (fun ω => D.toLp z ω * G ω) μ := by
  obtain ⟨C, hC⟩ := hz
  exact (L1.integrable_coeFn G).bdd_mul (Lp.aestronglyMeasurable _)
    (hC.mono fun ω h => by rwa [Real.norm_eq_abs])

/-- The pairing as a continuous linear form on L¹. -/
def pairCLM {z : D.Space} (hz : z ∈ D.bddSpace) : Lp ℝ 1 μ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun G => D.pair z G
      map_add' := fun G G' => by
        simp only [pair]
        rw [← integral_add (D.integrable_pair hz G) (D.integrable_pair hz G')]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add G G'] with ω h
        rw [h, Pi.add_apply]
        ring
      map_smul' := fun c G => by
        simp only [pair, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c G] with ω h
        rw [h, Pi.smul_apply, smul_eq_mul]
        ring }
    |Classical.choose hz| (fun G => by
      have hC := Classical.choose_spec hz
      change ‖D.pair z G‖ ≤ _
      rw [L1.norm_eq_integral_norm, ← integral_const_mul]
      refine norm_integral_le_of_norm_le ((L1.integrable_coeFn G).norm.const_mul _) ?_
      filter_upwards [hC] with ω h
      rw [norm_mul, Real.norm_eq_abs (D.toLp z ω)]
      exact mul_le_mul_of_nonneg_right (h.trans (le_abs_self _)) (norm_nonneg _))

/-- The continuous linear pairing evaluates to the integral pairing. -/
theorem pairCLM_apply {z : D.Space} (hz : z ∈ D.bddSpace) (G : Lp ℝ 1 μ) :
    D.pairCLM hz G = D.pair z G := rfl

/--
Uniqueness in L¹ using test functions from 𝔻 ∩ L^∞ (BH, proof of 4.1.3: "the uniqueness property
follows easily").
-/
theorem ae_eq_of_integral_mul_eq (hd : DenseRange D.toLp) {φ ψ : Ω → ℝ} (hφ : Integrable φ μ)
    (hψ : Integrable ψ μ)
    (h : ∀ z ∈ D.bddSpace, ∫ ω, D.toLp z ω * φ ω ∂μ = ∫ ω, D.toLp z ω * ψ ω ∂μ) :
    φ =ᵐ[μ] ψ := by
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ hφ hψ fun A hA hμA => ?_
  obtain ⟨z, hzb, hz01, hlim⟩ := D.exists_approx_indicator hd hA hμA.ne
  exact tendsto_nhds_unique (D.tendsto_integral_mul_approx hz01 hA hlim hφ)
    ((D.tendsto_integral_mul_approx hz01 hA hlim hψ).congr fun n => (h _ (hzb n)).symm)

/-- Positivity in L¹ using test functions taking values in [0, 1]. -/
theorem ae_nonneg_of_integral_mul_nonneg (hd : DenseRange D.toLp) {φ : Ω → ℝ}
    (hφ : Integrable φ μ)
    (h : ∀ z ∈ D.bddSpace, (∀ᵐ ω ∂μ, 0 ≤ D.toLp z ω ∧ D.toLp z ω ≤ 1) →
      0 ≤ ∫ ω, D.toLp z ω * φ ω ∂μ) : 0 ≤ᵐ[μ] φ := by
  refine ae_nonneg_of_forall_setIntegral_nonneg hφ fun A hA hμA => ?_
  obtain ⟨z, hzb, hz01, hlim⟩ := D.exists_approx_indicator hd hA hμA.ne
  exact ge_of_tendsto (D.tendsto_integral_mul_approx hz01 hA hlim hφ)
    (Eventually.of_forall fun n => h _ (hzb n) (hz01 n))

/--
An upper bound on the integral of a nonnegative L¹ class using test functions taking values in [0,
1].
-/
theorem integral_le_of_integral_mul_le (hd : DenseRange D.toLp) (G : Lp ℝ 1 μ)
    (hG0 : 0 ≤ᵐ[μ] ⇑G) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z ∈ D.bddSpace, (∀ᵐ ω ∂μ, 0 ≤ D.toLp z ω ∧ D.toLp z ω ≤ 1) →
      ∫ ω, D.toLp z ω * G ω ∂μ ≤ C) : ∫ ω, G ω ∂μ ≤ C := by
  refine (integrable_of_setIntegral_le (Lp.stronglyMeasurable G).measurable hG0
    (measure_level_ne_top one_ne_zero ENNReal.one_ne_top (Lp.memLp G)) hC
    fun A hA hμA => ⟨(L1.integrable_coeFn G).integrableOn, ?_⟩).2
  obtain ⟨z, hzb, hz01, hlim⟩ := D.exists_approx_indicator hd hA hμA
  exact le_of_tendsto (D.tendsto_integral_mul_approx hz01 hA hlim (L1.integrable_coeFn G))
    (Eventually.of_forall fun n => h _ (hzb n) (hz01 n))

/-- When the form domain is dense in L², bounded form tests distinguish L¹ classes. -/
theorem eq_of_pair_eq (hd : DenseRange D.toLp) {G G' : Lp ℝ 1 μ}
    (h : ∀ z ∈ D.bddSpace, D.pair z G = D.pair z G') : G = G' :=
  Lp.ext (D.ae_eq_of_integral_mul_eq hd (L1.integrable_coeFn G) (L1.integrable_coeFn G') h)

/-- The clamp (−n) ∨ (x ∧ n). -/
def truncS (n : ℕ) (x : D.Space) : D.Space :=
  D.contract (lipschitzWith_trunc n) (trunc_zero n) x

/-- Every symmetric integer truncation belongs to the bounded form subspace. -/
theorem truncS_mem (n : ℕ) (x : D.Space) : D.truncS n x ∈ D.bddSpace := by
  refine ⟨n, ?_⟩
  filter_upwards [D.coe_contractLp (lipschitzWith_trunc n)
    (trunc_zero n) x] with ω h
  rw [truncS, toLp_contract, h]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact abs_le.2 ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩

/--
BH 1991, ch. I § 4.1 (p. 17): 𝔻 ∩ L^∞ is dense in 𝔻 (the clamps converge in 𝔻; ), a fact used
implicitly by BH for uniqueness of Γ and passage from H to 𝔻 ∩ L^∞.

The space 𝔻 ∩ L^∞ is dense in 𝔻.
-/
theorem dense_bddSpace : Dense (D.bddSpace : Set D.Space) := fun x =>
  mem_closure_of_tendsto (D.tendsto_contract_trunc x)
    (Eventually.of_forall fun n => D.truncS_mem n x)

end TestFunctions

/-! ## G. Definition 4.1.2 and proposition 4.1.3 -/

section CarreDuChamp

/-- The BH form: ℰ(fh, g) + ℰ(gh, f) − ℰ(h, fg) (h = z, f = x, g = y). -/
def bhS (z x y : D.Space) : ℝ :=
  D.ener (D.mulS x z) y + D.ener (D.mulS y z) x - D.ener z (D.mulS x y)

/-- On bounded form elements, the extended BH expression equals the BH form. -/
theorem bhS_eq_bhForm (z x y : D.bddSpace) : D.bhS z x y = D.bhForm z x y := rfl

/-- The diagonal BH expression is 2ℰ(xz, x) − ℰ(z, x²). -/
theorem bhS_self (z x : D.Space) :
    D.bhS z x x = 2 * D.ener (D.mulS x z) x - D.ener z (D.mulS x x) := by
  rw [bhS]; ring

/-- The extended BH expression is symmetric in its two bounded energy arguments. -/
theorem bhS_symm {z x y : D.Space} (hz : z ∈ D.bddSpace) (hx : x ∈ D.bddSpace)
    (hy : y ∈ D.bddSpace) : D.bhS z x y = D.bhS z y x :=
  D.bhForm_symm ⟨z, hz⟩ ⟨x, hx⟩ ⟨y, hy⟩

/-- Consequence of 4.1.1: 0 ≤ ℰ(fh, f)·2 − ℰ(h, f²) ≤ 2Mℰ(f). -/
theorem bhS_self_nonneg_le {x z : D.Space} (hx : x ∈ D.bddSpace) (hz : z ∈ D.bddSpace) {M : ℝ}
    (hM : 0 ≤ M) (hz0 : ∀ᵐ ω ∂μ, 0 ≤ D.toLp z ω) (hzM : ∀ᵐ ω ∂μ, D.toLp z ω ≤ M) :
    0 ≤ D.bhS z x x ∧ D.bhS z x x ≤ 2 * M * D.ener x x := by
  have h := D.bh_4_1_1 (y := x) hx hz hM hz0 hzM LipschitzWith.id rfl (ae_of_all _ fun _ => rfl)
  rw [bhS_self]
  constructor <;> linarith [h.1, h.2.1, h.2.2]

/--
Continuity of (f, g) ↦ ℰ(fh, g) + ℰ(gh, f) − ℰ(h, fg) for 0 ≤ h ≤ M (Cauchy–Schwarz for the
nonnegative form, and 4.1.1).
-/
theorem abs_bhS_le_of_nonneg {z : D.Space} (hz : z ∈ D.bddSpace) {M : ℝ} (hM : 0 ≤ M)
    (hz0 : ∀ᵐ ω ∂μ, 0 ≤ D.toLp z ω) (hzM : ∀ᵐ ω ∂μ, D.toLp z ω ≤ M) {x y : D.Space}
    (hx : x ∈ D.bddSpace) (hy : y ∈ D.bddSpace) : |D.bhS z x y| ≤ 2 * M * ‖x‖ * ‖y‖ := by
  have hcs := LinearMap.BilinForm.apply_sq_le_of_symm (D.bhForm ⟨z, hz⟩)
    (fun a => (D.bhS_self_nonneg_le a.2 hz hM hz0 hzM).1) ⟨fun a b => D.bhForm_symm _ a b⟩
    ⟨x, hx⟩ ⟨y, hy⟩
  have hxx := D.bhS_self_nonneg_le hx hz hM hz0 hzM
  have hyy := D.bhS_self_nonneg_le hy hz hM hz0 hzM
  have ex := D.ener_self_le x
  have ey := D.ener_self_le y
  have hx2 : D.bhS z x x ≤ 2 * M * ‖x‖ ^ 2 := hxx.2.trans (by nlinarith)
  have hy2 : D.bhS z y y ≤ 2 * M * ‖y‖ ^ 2 := hyy.2.trans (by nlinarith)
  have h1 : (D.bhS z x y) ^ 2 ≤ (2 * M * ‖x‖ * ‖y‖) ^ 2 := by
    calc (D.bhS z x y) ^ 2 ≤ D.bhS z x x * D.bhS z y y := hcs
      _ ≤ (2 * M * ‖x‖ ^ 2) * (2 * M * ‖y‖ ^ 2) :=
          mul_le_mul hx2 hy2 hyy.1 (by positivity)
      _ = (2 * M * ‖x‖ * ‖y‖) ^ 2 := by ring
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 (by rwa [sq_abs])

/--
Decomposition h = h⁺ − h⁻ in 𝔻 ∩ L^∞ (contraction t ↦ t ∨ 0), with 0 ≤ h± ≤ M if |h| ≤ M, and
linearity in h of ℰ(fh, g) + ℰ(gh, f) − ℰ(h, fg).
-/
theorem bhS_decomp {z : D.Space} (hz : z ∈ D.bddSpace) {M : ℝ} (hM : 0 ≤ M)
    (hzM : ∀ᵐ ω ∂μ, |D.toLp z ω| ≤ M) :
    ∃ zp ∈ D.bddSpace, ∃ zm ∈ D.bddSpace,
      (∀ᵐ ω ∂μ, 0 ≤ D.toLp zp ω) ∧ (∀ᵐ ω ∂μ, D.toLp zp ω ≤ M) ∧
      (∀ᵐ ω ∂μ, 0 ≤ D.toLp zm ω) ∧ (∀ᵐ ω ∂μ, D.toLp zm ω ≤ M) ∧
      ∀ x ∈ D.bddSpace, ∀ y ∈ D.bddSpace, D.bhS z x y = D.bhS zp x y - D.bhS zm x y := by
  have hF : LipschitzWith 1 (fun t : ℝ => max t 0) := LipschitzWith.id.max_const 0
  have h0 : (fun t : ℝ => max t 0) 0 = 0 := max_self 0
  set zp := D.contract hF h0 z with hzpdef
  have hzp : zp ∈ D.bddSpace := D.contract_mem_bddSpace hF h0 hz
  have hzpe : ⇑(D.toLp zp) =ᵐ[μ] fun ω => max (D.toLp z ω) 0 := by
    rw [hzpdef, toLp_contract]; exact D.coe_contractLp hF h0 z
  set zm := zp - z with hzmdef
  have hzm : zm ∈ D.bddSpace := D.bddSpace.sub_mem hzp hz
  have hzme : ⇑(D.toLp zm) =ᵐ[μ] fun ω => max (D.toLp z ω) 0 - D.toLp z ω := by
    filter_upwards [hzpe, Lp.coeFn_sub (D.toLp zp) (D.toLp z)] with ω h1 h2
    rw [hzmdef, map_sub, h2, Pi.sub_apply, h1]
  refine ⟨zp, hzp, zm, hzm, ?_, ?_, ?_, ?_, fun x hx y hy => ?_⟩
  · filter_upwards [hzpe] with ω h; rw [h]; exact le_max_right _ _
  · filter_upwards [hzpe, hzM] with ω h1 h2; rw [h1]
    exact max_le ((le_abs_self _).trans h2) hM
  · filter_upwards [hzme] with ω h; rw [h]; linarith [le_max_left (D.toLp z ω) 0]
  · filter_upwards [hzme, hzM] with ω h1 h2; rw [h1]
    rcases le_total 0 (D.toLp z ω) with h3 | h3
    · rw [max_eq_left h3]; linarith
    · rw [max_eq_right h3]; linarith [neg_abs_le (D.toLp z ω)]
  have he : (⟨z, hz⟩ : D.bddSpace) = ⟨zp, hzp⟩ + (-1 : ℝ) • ⟨zm, hzm⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, hzmdef]
    module
  change D.bhForm ⟨z, hz⟩ ⟨x, hx⟩ ⟨y, hy⟩ =
    D.bhForm ⟨zp, hzp⟩ ⟨x, hx⟩ ⟨y, hy⟩ - D.bhForm ⟨zm, hzm⟩ ⟨x, hx⟩ ⟨y, hy⟩
  rw [he, D.bhForm_add, D.bhForm_smul]
  ring

/-- The same bound for h of arbitrary sign, |h| ≤ M (h = h⁺ − h⁻). -/
theorem abs_bhS_le {z : D.Space} (hz : z ∈ D.bddSpace) {M : ℝ} (hM : 0 ≤ M)
    (hzM : ∀ᵐ ω ∂μ, |D.toLp z ω| ≤ M) {x y : D.Space} (hx : x ∈ D.bddSpace)
    (hy : y ∈ D.bddSpace) : |D.bhS z x y| ≤ 4 * M * ‖x‖ * ‖y‖ := by
  obtain ⟨zp, hzp, zm, hzm, hp0, hpM, hm0, hmM, hdec⟩ := D.bhS_decomp hz hM hzM
  have hp := D.abs_bhS_le_of_nonneg hzp hM hp0 hpM hx hy
  have hm := D.abs_bhS_le_of_nonneg hzm hM hm0 hmM hx hy
  rw [hdec x hx y hy]
  have h1 := abs_le.1 hp
  have h2 := abs_le.1 hm
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

/--
BH 1991, ch. I § 4.1, proposition 4.1.1 and definition 4.1.2 (p. 17): for f ∈ 𝔻 ∩ L^∞, the linear
form h ↦ 2ℰ(fh, f) − ℰ(h, f²) on 𝔻 ∩ L^∞ is positive (4.1.1) and continuous for the L^∞ norm; (R)
additionally requires representation by an f̃ ∈ L¹. Continuity for the L¹ norm does not hold in
general.

If |h| ≤ M a.e., then |2ℰ(fh, f) − ℰ(h, f²)| ≤ 2M ℰ(f).
-/
theorem abs_bhS_self_le {z : D.Space} (hz : z ∈ D.bddSpace) {M : ℝ} (hM : 0 ≤ M)
    (hzM : ∀ᵐ ω ∂μ, |D.toLp z ω| ≤ M) {x : D.Space} (hx : x ∈ D.bddSpace) :
    |2 * D.ener (D.mulS x z) x - D.ener z (D.mulS x x)| ≤ 2 * M * D.ener x x := by
  obtain ⟨zp, hzp, zm, hzm, hp0, hpM, hm0, hmM, hdec⟩ := D.bhS_decomp hz hM hzM
  have hp := D.bhS_self_nonneg_le hx hzp hM hp0 hpM
  have hm := D.bhS_self_nonneg_le hx hzm hM hm0 hmM
  rw [← D.bhS_self, hdec x hx x hx]
  exact abs_le.2 ⟨by linarith [hp.1, hp.2, hm.1, hm.2], by linarith [hp.1, hp.2, hm.1, hm.2]⟩

/--
BH 1991, ch. I § 4.1, definition 4.1.2 (p. 17): property (R), "the form ℰ admits a carre du champ".

(R): there exists a subspace H of 𝔻 ∩ L^∞, dense in 𝔻, such that for every f ∈ H there exists f̃ ∈
L¹ with 2ℰ(fh, f) − ℰ(h, f²) = ∫ h f̃ dm for every h ∈ 𝔻 ∩ L^∞.
-/
def AdmitsCarreDuChamp : Prop :=
  ∃ H : Submodule ℝ D.Space, H ≤ D.bddSpace ∧ Dense (H : Set D.Space) ∧
    ∀ x ∈ H, ∃ ft : Lp ℝ 1 μ, ∀ z ∈ D.bddSpace,
      2 * D.ener (D.mulS x z) x - D.ener z (D.mulS x x) = ∫ ω, D.toLp z ω * ft ω ∂μ

/--
BH 1991, ch. I § 4.1, proposition 4.1.3 (p. 17): the characteristic property of the carre du champ
operator.

A continuous bilinear map Γ : 𝔻 × 𝔻 → L¹ such that, for f, g, h ∈ 𝔻 ∩ L^∞, ℰ(fh, g) + ℰ(gh, f) −
ℰ(h, fg) = ∫ h Γ(f, g) dm.
-/
def IsCarreDuChamp (Γ : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ) : Prop :=
  ∀ x ∈ D.bddSpace, ∀ y ∈ D.bddSpace, ∀ z ∈ D.bddSpace,
    D.ener (D.mulS x z) y + D.ener (D.mulS y z) x - D.ener z (D.mulS x y) =
      ∫ ω, D.toLp z ω * Γ x y ω ∂μ

/-- The characterization at (f, g) of a class G ∈ L¹. -/
def IsGammaRep (x y : D.Space) (G : Lp ℝ 1 μ) : Prop :=
  ∀ z ∈ D.bddSpace, D.bhS z x y = D.pair z G

/-- When the form domain is dense in L², an L¹ representative of the carré du champ is unique. -/
theorem isGammaRep_unique (hd : DenseRange D.toLp) {x y : D.Space} {G G' : Lp ℝ 1 μ}
    (h : D.IsGammaRep x y G) (h' : D.IsGammaRep x y G') : G = G' :=
  D.eq_of_pair_eq hd fun z hz => (h z hz).symm.trans (h' z hz)

/--
For bounded form elements, addition in the first argument adds their carré-du-champ representatives.
-/
theorem isGammaRep_add {x x' y : D.Space} (hx : x ∈ D.bddSpace) (hx' : x' ∈ D.bddSpace)
    (hy : y ∈ D.bddSpace) {G G' : Lp ℝ 1 μ} (h : D.IsGammaRep x y G) (h' : D.IsGammaRep x' y G') :
    D.IsGammaRep (x + x') y (G + G') := by
  intro z hz
  have e : D.bhS z (x + x') y = D.bhS z x y + D.bhS z x' y := by
    change D.bhForm ⟨z, hz⟩ (⟨x, hx⟩ + ⟨x', hx'⟩) ⟨y, hy⟩ =
      D.bhForm ⟨z, hz⟩ ⟨x, hx⟩ ⟨y, hy⟩ + D.bhForm ⟨z, hz⟩ ⟨x', hx'⟩ ⟨y, hy⟩
    rw [map_add, LinearMap.add_apply]
  rw [e, h z hz, h' z hz, ← D.pairCLM_apply hz, ← D.pairCLM_apply hz, ← D.pairCLM_apply hz,
    map_add]

/-- For bounded form elements, real scaling in the first argument scales its Γ representative. -/
theorem isGammaRep_smul (c : ℝ) {x y : D.Space} (hx : x ∈ D.bddSpace) (hy : y ∈ D.bddSpace)
    {G : Lp ℝ 1 μ} (h : D.IsGammaRep x y G) : D.IsGammaRep (c • x) y (c • G) := by
  intro z hz
  have e : D.bhS z (c • x) y = c * D.bhS z x y := by
    change D.bhForm ⟨z, hz⟩ (c • ⟨x, hx⟩) ⟨y, hy⟩ = c * D.bhForm ⟨z, hz⟩ ⟨x, hx⟩ ⟨y, hy⟩
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [e, h z hz, ← D.pairCLM_apply hz, ← D.pairCLM_apply hz, map_smul, smul_eq_mul]

/-- For bounded form elements, swapping the arguments preserves a Γ representative. -/
theorem isGammaRep_symm {x y : D.Space} (hx : x ∈ D.bddSpace) (hy : y ∈ D.bddSpace)
    {G : Lp ℝ 1 μ} (h : D.IsGammaRep x y G) : D.IsGammaRep y x G := fun z hz => by
  rw [D.bhS_symm hz hy hx]; exact h z hz

/--
Positivity and an L¹ bound on the diagonal (BH, proof of 4.1.3: "Γ(f, f) ≥ 0 and ‖Γ(f, f)‖_{L¹} ≤
2ℰ(f)").
-/
theorem isGammaRep_self_bound (hd : DenseRange D.toLp) {x : D.Space} (hx : x ∈ D.bddSpace)
    {G : Lp ℝ 1 μ} (h : D.IsGammaRep x x G) : 0 ≤ G ∧ ‖G‖ ≤ 2 * D.ener x x := by
  have hnn : 0 ≤ᵐ[μ] ⇑G := D.ae_nonneg_of_integral_mul_nonneg hd (L1.integrable_coeFn G)
    fun z hz hz01 => by
      have h1 := (D.bhS_self_nonneg_le hx hz zero_le_one (hz01.mono fun _ h => h.1)
        (hz01.mono fun _ h => h.2)).1
      rw [h z hz] at h1
      exact h1
  refine ⟨(Lp.coeFn_nonneg _).1 hnn, ?_⟩
  rw [L1.norm_eq_integral_norm, integral_congr_ae (hnn.mono fun ω h => Real.norm_of_nonneg h)]
  refine D.integral_le_of_integral_mul_le hd G hnn
    (mul_nonneg zero_le_two (D.ener_self_nonneg x)) fun z hz hz01 => ?_
  have h1 := (D.bhS_self_nonneg_le hx hz zero_le_one (hz01.mono fun _ h => h.1)
    (hz01.mono fun _ h => h.2)).2
  rw [h z hz] at h1
  change D.pair z G ≤ _
  linarith

/-- Polarization: the class ¼(f̃₊ − f̃₋) characterizes (f, g). -/
theorem isGammaRep_polar {x y : D.Space} (hx : x ∈ D.bddSpace) (hy : y ∈ D.bddSpace)
    {Gp Gm : Lp ℝ 1 μ} (hp : ∀ z ∈ D.bddSpace,
      2 * D.ener (D.mulS (x + y) z) (x + y) - D.ener z (D.mulS (x + y) (x + y)) = D.pair z Gp)
    (hm : ∀ z ∈ D.bddSpace,
      2 * D.ener (D.mulS (x - y) z) (x - y) - D.ener z (D.mulS (x - y) (x - y)) = D.pair z Gm) :
    D.IsGammaRep x y ((4⁻¹ : ℝ) • (Gp - Gm)) := by
  intro z hz
  have e : D.bhS z x y = 4⁻¹ * (D.bhS z (x + y) (x + y) - D.bhS z (x - y) (x - y)) := by
    change D.bhForm ⟨z, hz⟩ ⟨x, hx⟩ ⟨y, hy⟩ = 4⁻¹ *
      (D.bhForm ⟨z, hz⟩ (⟨x, hx⟩ + ⟨y, hy⟩) (⟨x, hx⟩ + ⟨y, hy⟩) -
        D.bhForm ⟨z, hz⟩ (⟨x, hx⟩ - ⟨y, hy⟩) (⟨x, hx⟩ - ⟨y, hy⟩))
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    rw [D.bhForm_symm ⟨z, hz⟩ ⟨y, hy⟩ ⟨x, hx⟩]
    ring
  rw [e, D.bhS_self, D.bhS_self, hp z hz, hm z hz, ← D.pairCLM_apply hz, ← D.pairCLM_apply hz,
    ← D.pairCLM_apply hz, map_smul, map_sub, smul_eq_mul]

end CarreDuChamp

end DirichletForm
end ErrorCalculus.Capacity

namespace ErrorCalculus.Capacity
namespace DirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (D : DirichletForm μ)

/-! ## G (continued). Proposition 4.1.3: existence, uniqueness, properties -/

section Existence

/--
BH 1991, ch. I § 4.1, proposition 4.1.3, existence (p. 17), under density of 𝔻 in L² (BH 1.1.1).
BH's proof: Γ(f, g) = ¼((f + g)~ − (f − g)~) on H × H, then "by the density of H in 𝔻"; here
continuous extension (two uses of `ContinuousLinearMap.extend`) and passage from H to 𝔻 ∩ L^∞ by
continuity of (f, g) ↦ ℰ(fh, g) + ℰ(gh, f) − ℰ(h, fg).

If (R) holds, there exists a continuous bilinear map Γ : 𝔻 × 𝔻 → L¹ such that, for f, g, h ∈ 𝔻 ∩
L^∞, ℰ(fh, g) + ℰ(gh, f) − ℰ(h, fg) = ∫ h Γ(f, g) dm.
-/
theorem exists_isCarreDuChamp (hd : DenseRange D.toLp) (hR : D.AdmitsCarreDuChamp) :
    ∃ Γ : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ, D.IsCarreDuChamp Γ := by
  obtain ⟨H, hHb, hHd, hft0⟩ := hR
  choose! ft hft using hft0
  have hb : ∀ x : H, (x : D.Space) ∈ D.bddSpace := fun x => hHb x.2
  set G0 : H → H → Lp ℝ 1 μ := fun x y =>
    (4⁻¹ : ℝ) • (ft ((x : D.Space) + y) - ft ((x : D.Space) - y)) with hG0
  have hc : ∀ x y : H, D.IsGammaRep x y (G0 x y) := fun x y =>
    D.isGammaRep_polar (hb x) (hb y) (hft _ (H.add_mem x.2 y.2)) (hft _ (H.sub_mem x.2 y.2))
  let Γ₁ : H →ₗ[ℝ] H →ₗ[ℝ] Lp ℝ 1 μ := LinearMap.mk₂ ℝ G0
    (fun x x' y => D.isGammaRep_unique hd (hc (x + x') y)
      (D.isGammaRep_add (hb x) (hb x') (hb y) (hc x y) (hc x' y)))
    (fun c x y => D.isGammaRep_unique hd (hc (c • x) y) (D.isGammaRep_smul c (hb x) (hb y) (hc x y)))
    (fun x y y' => D.isGammaRep_unique hd (hc x (y + y'))
      (D.isGammaRep_symm (D.bddSpace.add_mem (hb y) (hb y')) (hb x)
        (D.isGammaRep_add (hb y) (hb y') (hb x) (D.isGammaRep_symm (hb x) (hb y) (hc x y))
          (D.isGammaRep_symm (hb x) (hb y') (hc x y')))))
    (fun c x y => D.isGammaRep_unique hd (hc x (c • y))
      (D.isGammaRep_symm (D.bddSpace.smul_mem c (hb y)) (hb x)
        (D.isGammaRep_smul c (hb y) (hb x) (D.isGammaRep_symm (hb x) (hb y) (hc x y)))))
  have hΓ₁ : ∀ x y : H, Γ₁ x y = G0 x y := fun x y => rfl
  have hsymm : ∀ x y : H, Γ₁ x y = Γ₁ y x := fun x y =>
    D.isGammaRep_unique hd (hc x y) (D.isGammaRep_symm (hb y) (hb x) (hc y x))
  have hdiag : ∀ x : H, ‖Γ₁ x x‖ ≤ 2 * ‖x‖ ^ 2 := fun x => by
    have h1 := (D.isGammaRep_self_bound hd (hb x) (hc x x)).2
    have h2 := D.ener_self_le (x : D.Space)
    rw [hΓ₁]
    have h3 : ‖(x : D.Space)‖ = ‖x‖ := rfl
    rw [h3] at h2
    linarith
  have hsq : ∀ x y : H, ‖Γ₁ x y‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := fun x y => by
    have e : Γ₁ x y = (4⁻¹ : ℝ) • (Γ₁ (x + y) (x + y) - Γ₁ (x - y) (x - y)) := by
      simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
      rw [hsymm y x]
      module
    rw [e, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4⁻¹)]
    have h1 := hdiag (x + y)
    have h2 := hdiag (x - y)
    have hp := parallelogram_law_with_norm ℝ x y
    have hn := norm_sub_le (Γ₁ (x + y) (x + y)) (Γ₁ (x - y) (x - y))
    nlinarith
  let Γ₁c : H →L[ℝ] H →L[ℝ] Lp ℝ 1 μ :=
    LinearMap.mkContinuous₂ Γ₁ 2 fun x y => norm_le_of_sq_bound Γ₁ hsq x y
  set ι : H →L[ℝ] D.Space := H.subtypeL with hι
  have hιd : DenseRange ι := hHd.denseRange_val
  have hιu : IsUniformInducing ι := isUniformEmbedding_subtype_val.isUniformInducing
  let extL : (H →L[ℝ] Lp ℝ 1 μ) →ₗ[ℝ] (D.Space →L[ℝ] Lp ℝ 1 μ) :=
    { toFun := fun T => T.extend ι
      map_add' := fun T T' => ContinuousLinearMap.extend_unique (T + T') hιd hιu _
        (ContinuousLinearMap.ext fun x => by
          simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, FunLike.coe_add,
            Pi.add_apply, ContinuousLinearMap.extend_eq _ hιd hιu])
      map_smul' := fun c T => ContinuousLinearMap.extend_unique (c • T) hιd hιu _
        (ContinuousLinearMap.ext fun x => by
          simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, FunLike.coe_smul,
            Pi.smul_apply, RingHom.id_apply, ContinuousLinearMap.extend_eq _ hιd hιu]) }
  have hbd : ∀ T : H →L[ℝ] Lp ℝ 1 μ, ‖T.extend ι‖ ≤ ‖T‖ := fun T => by
    have h := ContinuousLinearMap.opNorm_extend_le T (N := 1) hιd (fun x => by
      rw [NNReal.coe_one, one_mul]
      exact le_of_eq rfl)
    simpa using h
  let Φl : H →ₗ[ℝ] (D.Space →L[ℝ] Lp ℝ 1 μ) :=
    { toFun := fun a => (Γ₁c a).extend ι
      map_add' := fun a b => by
        rw [map_add]
        exact map_add extL (Γ₁c a) (Γ₁c b)
      map_smul' := fun c a => by
        rw [map_smul]
        exact map_smul extL c (Γ₁c a) }
  have hΦ : ∀ a : H, ‖Φl a‖ ≤ 2 * ‖a‖ := fun a => by
    change ‖(Γ₁c a).extend ι‖ ≤ 2 * ‖a‖
    exact (hbd _).trans (ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      fun y => norm_le_of_sq_bound Γ₁ hsq a y)
  let Φ : H →L[ℝ] (D.Space →L[ℝ] Lp ℝ 1 μ) := Φl.mkContinuous 2 hΦ
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ, ∀ x y : H, Γ x y = G0 x y := by
    refine ⟨Φ.extend ι, fun x y => ?_⟩
    have h1 : Φ.extend ι (ι x) = Φ x := ContinuousLinearMap.extend_eq _ hιd hιu x
    have h2 : (Γ₁c x).extend ι (ι y) = Γ₁c x y := ContinuousLinearMap.extend_eq (Γ₁c x) hιd hιu y
    change Φ.extend ι (ι x) (ι y) = G0 x y
    rw [h1]
    change (Γ₁c x).extend ι (ι y) = G0 x y
    rw [h2]
    rfl
  refine ⟨Γ, fun x hx y hy z hz => ?_⟩
  obtain ⟨xs, hxsH, hxs⟩ := mem_closure_iff_seq_limit.1 (hHd x)
  obtain ⟨ys, hysH, hys⟩ := mem_closure_iff_seq_limit.1 (hHd y)
  obtain ⟨M', hM'⟩ := hz
  have hzM : ∀ᵐ ω ∂μ, |D.toLp z ω| ≤ |M'| := hM'.mono fun ω h => h.trans (le_abs_self _)
  have hz' : z ∈ D.bddSpace := ⟨M', hM'⟩
  have hseq : ∀ n, D.bhS z (xs n) (ys n) = D.pair z (Γ (xs n) (ys n)) := by
    intro n
    have h1 := hΓ ⟨xs n, hxsH n⟩ ⟨ys n, hysH n⟩
    have h2 := hc ⟨xs n, hxsH n⟩ ⟨ys n, hysH n⟩ z hz'
    change D.bhS z (xs n) (ys n) = D.pair z (Γ ((⟨xs n, hxsH n⟩ : H) : D.Space)
      ((⟨ys n, hysH n⟩ : H) : D.Space))
    rw [h1]
    exact h2
  have hRt : Tendsto (fun n => D.pair z (Γ (xs n) (ys n))) atTop (𝓝 (D.pair z (Γ x y))) := by
    have h1 : Tendsto (fun n => Γ (xs n) (ys n)) atTop (𝓝 (Γ x y)) :=
      (Γ.continuous₂.tendsto (x, y)).comp (hxs.prodMk_nhds hys)
    exact ((D.pairCLM hz').continuous.tendsto _).comp h1
  have hLt : Tendsto (fun n => D.bhS z (xs n) (ys n)) atTop (𝓝 (D.bhS z x y)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb' : ∀ n, ‖D.bhS z (xs n) (ys n) - D.bhS z x y‖ ≤
        4 * |M'| * (‖xs n - x‖ * ‖ys n‖) + 4 * |M'| * (‖x‖ * ‖ys n - y‖) := by
      intro n
      have hxn := hHb (hxsH n)
      have hyn := hHb (hysH n)
      have e : D.bhS z (xs n) (ys n) - D.bhS z x y =
          D.bhS z (xs n - x) (ys n) + D.bhS z x (ys n - y) := by
        change D.bhForm ⟨z, hz'⟩ ⟨xs n, hxn⟩ ⟨ys n, hyn⟩ - D.bhForm ⟨z, hz'⟩ ⟨x, hx⟩ ⟨y, hy⟩ =
          D.bhForm ⟨z, hz'⟩ (⟨xs n, hxn⟩ - ⟨x, hx⟩) ⟨ys n, hyn⟩ +
            D.bhForm ⟨z, hz'⟩ ⟨x, hx⟩ (⟨ys n, hyn⟩ - ⟨y, hy⟩)
        simp only [map_sub, LinearMap.sub_apply]
        ring
      rw [e, Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · have h := D.abs_bhS_le hz' (abs_nonneg M') hzM (D.bddSpace.sub_mem hxn hx) hyn
        linarith
      · have h := D.abs_bhS_le hz' (abs_nonneg M') hzM hx (D.bddSpace.sub_mem hyn hy)
        linarith
    have hlim : Tendsto (fun n => 4 * |M'| * (‖xs n - x‖ * ‖ys n‖) +
        4 * |M'| * (‖x‖ * ‖ys n - y‖)) atTop (𝓝 0) := by
      have a1 : Tendsto (fun n => ‖xs n - x‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.1 hxs
      have a2 : Tendsto (fun n => ‖ys n - y‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.1 hys
      have a3 : Tendsto (fun n => ‖ys n‖) atTop (𝓝 ‖y‖) := hys.norm
      have h := ((a1.mul a3).const_mul (4 * |M'|)).add ((a2.const_mul ‖x‖).const_mul (4 * |M'|))
      simpa using h
    exact squeeze_zero (fun n => norm_nonneg _) hb' hlim
  exact tendsto_nhds_unique (hLt.congr hseq) hRt

/--
BH 1991, ch. I § 4.1, proposition 4.1.3, uniqueness (p. 17: "the uniqueness property follows
easily"); using test functions (density of 𝔻 in L²) and density of 𝔻 ∩ L^∞ in 𝔻.

Two carre du champ operators of ℰ are equal.
-/
theorem isCarreDuChamp_unique (hd : DenseRange D.toLp)
    {Γ Γ' : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ} (h : D.IsCarreDuChamp Γ)
    (h' : D.IsCarreDuChamp Γ') : Γ = Γ' :=
  clm₂_ext_of_dense D.dense_bddSpace fun x hx y hy =>
    D.eq_of_pair_eq hd fun z hz => (h x hx y hy z hz).symm.trans (h' x hx y hy z hz)

/--
BH 1991, ch. I § 4.1, proposition 4.1.3 (p. 17), existence and uniqueness, under density of 𝔻 in L²
(BH 1.1.1).

If ℰ admits a carre du champ (R), there exists a unique continuous bilinear map Γ : 𝔻 × 𝔻 → L¹ such
that ℰ(fh, g) + ℰ(gh, f) − ℰ(h, fg) = ∫ h Γ(f, g) dm for f, g, h ∈ 𝔻 ∩ L^∞.
-/
theorem bh_4_1_3 (hd : DenseRange D.toLp) (hR : D.AdmitsCarreDuChamp) :
    ∃! Γ : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ, D.IsCarreDuChamp Γ := by
  obtain ⟨Γ, hΓ⟩ := D.exists_isCarreDuChamp hd hR
  exact ⟨Γ, hΓ, fun Γ' h' => D.isCarreDuChamp_unique hd h' hΓ⟩

end Existence

section Properties

variable {Γ : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ}

/--
BH 1991, ch. I § 4.1, proposition 4.1.3 (p. 17): Γ is nonnegative on the diagonal; BH: "Γ(f, f) ≥
0".

Γ(f, f) ≥ 0 a.e. for every f ∈ 𝔻.
-/
theorem isCarreDuChamp_nonneg (hd : DenseRange D.toLp) (h : D.IsCarreDuChamp Γ) (x : D.Space) :
    0 ≤ Γ x x := by
  have hb : ∀ x ∈ D.bddSpace, 0 ≤ Γ x x := fun x hx =>
    (D.isGammaRep_self_bound hd hx fun z hz => h x hx x hx z hz).1
  have hc : IsClosed ((fun x => Γ x x) ⁻¹' Set.Ici 0) :=
    isClosed_Ici.preimage (Γ.continuous.clm_apply continuous_id)
  exact hc.closure_subset_iff.2 hb (D.dense_bddSpace x)

/--
BH 1991, ch. I § 4.1, proposition 4.1.3 (p. 17): Γ is symmetric.

Γ(f, g) = Γ(g, f) for f, g ∈ 𝔻.
-/
theorem isCarreDuChamp_symm (hd : DenseRange D.toLp) (h : D.IsCarreDuChamp Γ) (x y : D.Space) :
    Γ x y = Γ y x := by
  have e : Γ = Γ.flip := clm₂_ext_of_dense D.dense_bddSpace fun x hx y hy => by
    rw [ContinuousLinearMap.flip_apply]
    exact D.isGammaRep_unique hd (fun z hz => h x hx y hy z hz)
      (D.isGammaRep_symm hy hx fun z hz => h y hy x hx z hz)
  have h2 := congrArg (fun T : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ => T x y) e
  simpa using h2

/--
BH 1991, ch. I § 4.1, proof of proposition 4.1.3 (p. 17): ‖Γ(f, f)‖_{L¹} ≤ 2ℰ(f), stated by BH on H
and extended here to all of 𝔻.

‖Γ(f, f)‖_{L¹} ≤ 2ℰ(f) for every f ∈ 𝔻.
-/
theorem isCarreDuChamp_norm_le (hd : DenseRange D.toLp) (h : D.IsCarreDuChamp Γ) (x : D.Space) :
    ‖Γ x x‖ ≤ 2 * D.ener x x := by
  have hb : ∀ x ∈ D.bddSpace, ‖Γ x x‖ ≤ 2 * D.ener x x := fun x hx =>
    (D.isGammaRep_self_bound hd hx fun z hz => h x hx x hx z hz).2
  have hc : IsClosed {x : D.Space | ‖Γ x x‖ ≤ 2 * D.ener x x} :=
    isClosed_le (Γ.continuous.clm_apply continuous_id).norm
      (continuous_const.mul (D.ener.continuous.clm_apply continuous_id))
  exact hc.closure_subset_iff.2 hb (D.dense_bddSpace x)

/--
A consequence of the BH carré-du-champ properties: pointwise Cauchy–Schwarz inequality for Γ, a
consequence of positivity and symmetry.

Γ(f, g)² ≤ Γ(f, f) Γ(g, g) a.e.
-/
theorem isCarreDuChamp_sq_le (hd : DenseRange D.toLp) (h : D.IsCarreDuChamp Γ) (x y : D.Space) :
    ∀ᵐ ω ∂μ, (Γ x y ω) ^ 2 ≤ Γ x x ω * Γ y y ω := by
  have hsym := D.isCarreDuChamp_symm hd h
  have hpos := D.isCarreDuChamp_nonneg hd h
  have hpoly : ∀ t : ℚ, ∀ᵐ ω ∂μ, 0 ≤ Γ x x ω + 2 * (t : ℝ) * Γ x y ω + (t : ℝ) ^ 2 * Γ y y ω := by
    intro t
    have hp := (Lp.coeFn_nonneg _).2 (hpos (x + (t : ℝ) • y))
    have e : Γ (x + (t : ℝ) • y) (x + (t : ℝ) • y) =
        Γ x x + (2 * (t : ℝ)) • Γ x y + ((t : ℝ) ^ 2) • Γ y y := by
      simp only [map_add, map_smul, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
        Pi.smul_apply]
      rw [hsym y x]
      module
    rw [e] at hp
    filter_upwards [hp, Lp.coeFn_add (Γ x x + (2 * (t : ℝ)) • Γ x y) ((t : ℝ) ^ 2 • Γ y y),
      Lp.coeFn_add (Γ x x) ((2 * (t : ℝ)) • Γ x y), Lp.coeFn_smul (2 * (t : ℝ)) (Γ x y),
      Lp.coeFn_smul ((t : ℝ) ^ 2) (Γ y y)] with ω h1 h2 h3 h4 h5
    rw [h2, Pi.add_apply, h3, Pi.add_apply, h4, h5, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, Pi.zero_apply] at h1
    linarith
  filter_upwards [ae_all_iff.2 hpoly] with ω hω
  have hr : ∀ t : ℝ, 0 ≤ Γ x x ω + 2 * t * Γ x y ω + t ^ 2 * Γ y y ω := fun t =>
    Rat.denseRange_cast.induction_on t (isClosed_le continuous_const (by fun_prop)) hω
  have hd' := discrim_le_zero (a := Γ y y ω) (b := 2 * Γ x y ω) (c := Γ x x ω)
    (fun t => by nlinarith [hr t])
  simp only [discrim] at hd'
  nlinarith

/--
The energy integral identity: ℰ(f) = ½ ∫ Γ(f, f) dm, which is NOT in BH § 4.1 (BH only gives ‖Γ(f,
f)‖_{L¹} ≤ 2ℰ(f) there); it holds under the "no killing term" hypothesis: 1 ∈ 𝔻 and ℰ(1) = 0 (see
the control `kill_integral_eq` for a counterexample without this hypothesis).

If 1 ∈ 𝔻 ∩ L^∞ (a class e = 1 a.e.) and ℰ(1) = 0, then ∫ Γ(f, f) dm = 2ℰ(f) for every f ∈ 𝔻.
-/
theorem isCarreDuChamp_integral_eq (h : D.IsCarreDuChamp Γ) {e : D.Space}
    (he : e ∈ D.bddSpace) (he1 : ∀ᵐ ω ∂μ, D.toLp e ω = 1) (he0 : D.ener e e = 0) (x : D.Space) :
    ∫ ω, Γ x x ω ∂μ = 2 * D.ener x x := by
  have hE : ∀ w, D.ener e w = 0 := by
    intro w
    have h1 := D.form.cauchy_schwarz (D.form.formToDomain e) (D.form.formToDomain w)
    have h2 : D.form.E (D.form.formToDomain e) (D.form.formToDomain e) = 0 := by
      rw [← D.ener_apply]; exact he0
    rw [QuadForm.seminorm, h2, Real.sqrt_zero, zero_mul] at h1
    rw [D.ener_apply]
    exact abs_nonpos_iff.1 h1
  have hb : ∀ x ∈ D.bddSpace, ∫ ω, Γ x x ω ∂μ = 2 * D.ener x x := by
    intro x hx
    have hxe : D.mulS x e = x := D.eq_of_ae (by
      filter_upwards [D.coeFn_toLp_mulS hx he, he1] with ω h1 h2
      rw [h1, h2, mul_one])
    have hi := h x hx x hx e he
    rw [hxe, hE] at hi
    have h3 : ∫ ω, D.toLp e ω * Γ x x ω ∂μ = ∫ ω, Γ x x ω ∂μ :=
      integral_congr_ae (by filter_upwards [he1] with ω h; rw [h, one_mul])
    linarith
  have hc : IsClosed {x : D.Space | ∫ ω, Γ x x ω ∂μ = 2 * D.ener x x} :=
    isClosed_eq (continuous_integral.comp (Γ.continuous.clm_apply continuous_id))
      (continuous_const.mul (D.ener.continuous.clm_apply continuous_id))
  exact hc.closure_subset_iff.2 hb (D.dense_bddSpace x)

/--
converse of BH proposition 4.1.3 (p. 17; BH: "Γ is called the carré du champ operator"): such an
operator gives (R) with H = 𝔻 ∩ L^∞ and f̃ = Γ(f, f).

If a characteristic Γ exists, then ℰ satisfies (R).
-/
theorem admitsCarreDuChamp_of_isCarreDuChamp (h : D.IsCarreDuChamp Γ) :
    D.AdmitsCarreDuChamp :=
  ⟨D.bddSpace, le_rfl, D.dense_bddSpace, fun x hx => ⟨Γ x x, fun z hz => by
    rw [← h x hx x hx z hz]
    ring⟩⟩

/--
characterization (BH definition 4.1.2 and proposition 4.1.3, p. 17): (R) is equivalent to existence
of a carre du champ operator, under density of 𝔻 in L².

The form ℰ satisfies (R) if and only if a characteristic Γ exists.
-/
theorem admitsCarreDuChamp_iff (hd : DenseRange D.toLp) :
    D.AdmitsCarreDuChamp ↔ ∃ Γ : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ, D.IsCarreDuChamp Γ :=
  ⟨D.exists_isCarreDuChamp hd, fun ⟨_, h⟩ => D.admitsCarreDuChamp_of_isCarreDuChamp h⟩

end Properties

end DirichletForm
end ErrorCalculus.Capacity

/-!
## The named carré du champ and its characterizations: the named carre du champ operator, literal BH
statements
-/

namespace ErrorCalculus.Capacity.DirichletForm

section Named
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (D : DirichletForm μ)

/--
The carre du champ operator of ℰ as a named object: a characteristic Γ (BH 4.1.3) chosen if
one exists, 0 otherwise (a conventional value, never used under (R) and density of 𝔻 in L², where it
is
the unique characteristic Γ).
-/
def carreDuChamp : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ := by
  classical
  exact if h : ∃ Γ : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ, D.IsCarreDuChamp Γ then h.choose else 0

/-- If a characteristic Γ exists, the named object is characteristic. -/
theorem isCarreDuChamp_carreDuChamp_of_exists
    (h : ∃ Γ : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ, D.IsCarreDuChamp Γ) :
    D.IsCarreDuChamp D.carreDuChamp := by
  classical
  have he : D.carreDuChamp = h.choose := by
    simp only [carreDuChamp, dif_pos h]
  rw [he]
  exact h.choose_spec

/--
Under (R) and density of 𝔻 in L², the named object is a carre du champ operator (BH 4.1.3,
existence).
-/
theorem isCarreDuChamp_carreDuChamp (hd : DenseRange D.toLp)
    (hR : D.AdmitsCarreDuChamp) : D.IsCarreDuChamp D.carreDuChamp :=
  D.isCarreDuChamp_carreDuChamp_of_exists (D.exists_isCarreDuChamp hd hR)

/--
Every carre du champ operator equals the named object (BH 4.1.3, uniqueness, under density of 𝔻 in
L²).
-/
theorem eq_carreDuChamp (hd : DenseRange D.toLp)
    {Γ : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ} (h : D.IsCarreDuChamp Γ) :
    Γ = D.carreDuChamp :=
  D.isCarreDuChamp_unique hd h (D.isCarreDuChamp_carreDuChamp_of_exists ⟨Γ, h⟩)

/--
Characterization: under (R) and density of 𝔻 in L², Γ is characteristic if and only if it equals the
named object.
-/
theorem isCarreDuChamp_iff_eq (hd : DenseRange D.toLp) (hR : D.AdmitsCarreDuChamp)
    {Γ : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ} :
    D.IsCarreDuChamp Γ ↔ Γ = D.carreDuChamp :=
  ⟨D.eq_carreDuChamp hd, fun h => h ▸ D.isCarreDuChamp_carreDuChamp hd hR⟩

/--
Literal statement of BH 1991, ch. I, prop. 4.1.3 (p. 17): if (R) holds, there exists a unique
continuous bilinear form 𝔻 × 𝔻 → L¹, positive and symmetric, satisfying the characteristic identity
(uniqueness among positive symmetric forms, as in BH).
-/
theorem existsUnique_carreDuChamp (hd : DenseRange D.toLp) (hR : D.AdmitsCarreDuChamp) :
    ∃! Γ : D.Space →L[ℝ] D.Space →L[ℝ] Lp ℝ 1 μ,
      D.IsCarreDuChamp Γ ∧ (∀ x, 0 ≤ Γ x x) ∧ ∀ x y, Γ x y = Γ y x := by
  obtain ⟨Γ, hΓ⟩ := D.exists_isCarreDuChamp hd hR
  exact ⟨Γ, ⟨hΓ, D.isCarreDuChamp_nonneg hd hΓ, D.isCarreDuChamp_symm hd hΓ⟩,
    fun Γ' h' => D.isCarreDuChamp_unique hd h'.1 hΓ⟩

/--
BH 1991, ch. I, prop. 4.1.1 (p. 17) with ‖h‖_{L^∞} (essential bound `eLpNormEssSup`) in place of a
bound M: the "bound M" form of `bh_4_1_1` contains BH's statement.
-/
theorem energy_contraction_essSup_bounds {x y z : D.Space} (hx : x ∈ D.bddSpace)
    (hz : z ∈ D.bddSpace) (hz0 : ∀ᵐ ω ∂μ, 0 ≤ D.toLp z ω) {F : ℝ → ℝ} (hF : LipschitzWith 1 F)
    (h0 : F 0 = 0) (hyx : ∀ᵐ ω ∂μ, D.toLp y ω = F (D.toLp x ω)) :
    0 ≤ D.ener (D.mulS y z) y - 2⁻¹ * D.ener z (D.mulS y y) ∧
    D.ener (D.mulS y z) y - 2⁻¹ * D.ener z (D.mulS y y) ≤
      D.ener (D.mulS x z) x - 2⁻¹ * D.ener z (D.mulS x x) ∧
    D.ener (D.mulS x z) x - 2⁻¹ * D.ener z (D.mulS x x) ≤
      (eLpNormEssSup (D.toLp z) μ).toReal * D.ener x x := by
  obtain ⟨C, hC⟩ := hz
  have hfin : eLpNormEssSup (D.toLp z) μ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (eLpNormEssSup_le_of_ae_bound (hC.mono fun ω h => by rwa [Real.norm_eq_abs]))
  have hzM : ∀ᵐ ω ∂μ, D.toLp z ω ≤ (eLpNormEssSup (D.toLp z) μ).toReal := by
    filter_upwards [ae_le_eLpNormEssSup (μ := μ) (f := ⇑(D.toLp z))] with ω h
    have h1 := ENNReal.toReal_mono hfin h
    rw [toReal_enorm, Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans h1
  exact D.bh_4_1_1 hx ⟨C, hC⟩ ENNReal.toReal_nonneg hz0 hzM hF h0 hyx

end Named

end ErrorCalculus.Capacity.DirichletForm

namespace ErrorCalculus.Capacity
namespace DirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The BH energy estimate with arbitrary product representatives -/

section OfRep

/--
BH 1991, ch. I § 4.1: the form of 4.1.1 with products given by arbitrary representatives — the
convention mulS = 0 outside 𝔻 ∩ L^∞ plays no role here.

For f, h ∈ 𝔻 ∩ L^∞, every element w of 𝔻 representing the pointwise product fh equals `mulS f h`.
-/
theorem mulS_eq_of_rep (D : DirichletForm μ) {x z w : D.Space} (hx : x ∈ D.bddSpace)
    (hz : z ∈ D.bddSpace) (hw : ⇑(D.toLp w) =ᵐ[μ] fun ω => D.toLp x ω * D.toLp z ω) :
    D.mulS x z = w :=
  D.eq_of_ae ((D.coeFn_toLp_mulS hx hz).trans hw.symm)

/--
BH 1991, ch. I § 4.1, proposition 4.1.1 (p. 17): the form of 4.1.1 with products given by arbitrary
representatives — the convention mulS = 0 outside 𝔻 ∩ L^∞ plays no role here.

Let h ∈ 𝔻 ∩ L^∞ with 0 ≤ h ≤ M a.e., f ∈ 𝔻 ∩ L^∞, F a normal contraction, g = F ∘ f, and fh, f², gh,
g² arbitrary elements of 𝔻 representing the pointwise products. Then 0 ≤ ℰ(gh, g) − ½ ℰ(h, g²) ≤
ℰ(fh, f) − ½ ℰ(h, f²) ≤ M ℰ(f).
-/
theorem bh_4_1_1_of_rep (D : DirichletForm μ) {x y z fh ff gh gg : D.Space}
    (hx : x ∈ D.bddSpace) (hz : z ∈ D.bddSpace) {M : ℝ} (hM : 0 ≤ M)
    (hz0 : ∀ᵐ ω ∂μ, 0 ≤ D.toLp z ω) (hzM : ∀ᵐ ω ∂μ, D.toLp z ω ≤ M)
    {F : ℝ → ℝ} (hF : LipschitzWith 1 F) (h0 : F 0 = 0)
    (hyx : ∀ᵐ ω ∂μ, D.toLp y ω = F (D.toLp x ω))
    (hfh : ⇑(D.toLp fh) =ᵐ[μ] fun ω => D.toLp x ω * D.toLp z ω)
    (hff : ⇑(D.toLp ff) =ᵐ[μ] fun ω => D.toLp x ω * D.toLp x ω)
    (hgh : ⇑(D.toLp gh) =ᵐ[μ] fun ω => D.toLp y ω * D.toLp z ω)
    (hgg : ⇑(D.toLp gg) =ᵐ[μ] fun ω => D.toLp y ω * D.toLp y ω) :
    0 ≤ D.ener gh y - 2⁻¹ * D.ener z gg ∧
    D.ener gh y - 2⁻¹ * D.ener z gg ≤ D.ener fh x - 2⁻¹ * D.ener z ff ∧
    D.ener fh x - 2⁻¹ * D.ener z ff ≤ M * D.ener x x := by
  have hy : y ∈ D.bddSpace := by
    obtain ⟨C, hC⟩ := hx
    refine ⟨C, ?_⟩
    filter_upwards [hyx, hC] with ω h1 h2
    rw [h1]
    have h := hF.dist_le_mul (D.toLp x ω) 0
    simp only [h0, Real.dist_eq, sub_zero, NNReal.coe_one, one_mul] at h
    exact h.trans h2
  rw [← mulS_eq_of_rep D hx hz hfh, ← mulS_eq_of_rep D hx hx hff, ← mulS_eq_of_rep D hy hz hgh,
    ← mulS_eq_of_rep D hy hy hgg]
  exact D.bh_4_1_1 hx hz hM hz0 hzM hF h0 hyx

/--
BH 1991, ch. I § 4.1: the form of 4.1.1 with products given by arbitrary representatives — the
convention mulS = 0 outside 𝔻 ∩ L^∞ plays no role here.

For f, g, h ∈ 𝔻 ∩ L^∞ and fh, gh, fg arbitrary elements of 𝔻 representing the pointwise products,
the BH form equals ℰ(fh, g) + ℰ(gh, f) − ℰ(h, fg), where ℰ is the form of D.
-/
theorem bhForm_eq_of_rep (D : DirichletForm μ) (z x y : D.bddSpace) {fh gh fg : D.Space}
    (hfh : ⇑(D.toLp fh) =ᵐ[μ] fun ω => D.toLp x ω * D.toLp z ω)
    (hgh : ⇑(D.toLp gh) =ᵐ[μ] fun ω => D.toLp y ω * D.toLp z ω)
    (hfg : ⇑(D.toLp fg) =ᵐ[μ] fun ω => D.toLp x ω * D.toLp y ω) :
    D.bhForm z x y = D.form.E (D.form.formToDomain fh) (D.form.formToDomain y)
      + D.form.E (D.form.formToDomain gh) (D.form.formToDomain x)
      - D.form.E (D.form.formToDomain z) (D.form.formToDomain fg) := by
  rw [D.bhForm_apply, mulS_eq_of_rep D x.2 z.2 hfh, mulS_eq_of_rep D y.2 z.2 hgh,
    mulS_eq_of_rep D x.2 y.2 hfg, D.ener_apply, D.ener_apply, D.ener_apply]

end OfRep

end DirichletForm
end ErrorCalculus.Capacity
