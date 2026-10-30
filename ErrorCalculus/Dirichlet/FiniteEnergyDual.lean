import ErrorCalculus.Dirichlet.CapacityForm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic

/-!
# the space 𝔻' of finite-energy distributions (BH 1991, ch. I § 9.1)

## Main results
Framework: `DirichletForm μ`, a closed form on L²(μ), for arbitrary μ, with normal contractions; 𝔻 =
`D.Space`, with norm ‖u‖²_𝔻 = ‖u‖²_{L²} + ℰ(u). The dual 𝔻' (definition 9.1.1, p. 61) is `StrongDual
ℝ D.Space`; the canonical maps 𝔻 → L² → 𝔻' (proposition 9.1.2, pp. 61–62: L² → 𝔻' has dense range
unconditionally, and its injectivity is equivalent to density of 𝔻 in L², a BH framework hypothesis
not assumed by `DirichletForm`); the operator (I − A) in the form sense (`IsResolvent`, without a
generator or domain density) and the isometry 𝔻 → 𝔻' (proposition 9.1.3 a), p. 62); the cones 𝔻⁺,
𝔻'⁺ and 𝔻 = 𝔻⁺ − 𝔻⁺ (notation 9.1.4, p. 62); density of f ≥ 0 in L² in 𝔻'⁺ (proposition 9.1.5, p.
62, "bipolar theorem": Hahn–Banach separation after Riesz transport). Further topics in BH pp.
61–62, not treated here: 9.1.3 b), remark 9.1.3.1, "𝔻' ≠ 𝔻'⁺ − 𝔻'⁺".
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity
namespace DirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (D : DirichletForm μ)

/-! ## A. The space 𝔻' of finite-energy distributions (BH 9.1) -/

section DualSpace

/--
BH 1991, ch. I § 9.1, definition 9.1.1 (p. 61).

The Hilbert dual 𝔻' of 𝔻: the space of finite-energy distributions.
-/
abbrev Dual : Type _ := StrongDual ℝ D.Space

/-- The canonical inclusion of the form space into L² is injective. -/
theorem toLp_injective : Function.Injective D.toLp := by
  intro a b h
  apply D.form.formToDomain.injective
  exact Subtype.ext ((D.toLp_apply a).symm.trans (h.trans (D.toLp_apply b)))

/-- Restricting the L² inner-product functional to the form space has norm at most ‖f‖₂. -/
theorem norm_toDualMap_comp_toLp_le (f : Lp ℝ 2 μ) :
    ‖(InnerProductSpace.toDualMap ℝ (Lp ℝ 2 μ) f).comp D.toLp‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun x => ?_
  rw [ContinuousLinearMap.comp_apply, InnerProductSpace.toDualMap_apply_apply, Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (D.norm_toLp_le x) (norm_nonneg f))

/--
BH 1991, ch. I § 9.1, proposition 9.1.2 and its proof (pp. 61–62).

The continuous linear map L² → 𝔻', f ↦ (g ↦ (g, f)_{L²}), with norm ≤ 1.
-/
def ofLp : Lp ℝ 2 μ →L[ℝ] D.Dual :=
  LinearMap.mkContinuous
    { toFun := fun f => (InnerProductSpace.toDualMap ℝ (Lp ℝ 2 μ) f).comp D.toLp
      map_add' := fun f g => by
        ext x
        simp
      map_smul' := fun c f => by
        ext x
        simp }
    1 (fun f => by rw [one_mul]; exact D.norm_toDualMap_comp_toLp_le f)

/--
The functional associated with f ∈ L² evaluates to the L² inner product with the domain image.
-/
theorem ofLp_apply (f : Lp ℝ 2 μ) (x : D.Space) : D.ofLp f x = ⟪f, D.toLp x⟫_ℝ := rfl

/-- The canonical functional associated with f ∈ L² has dual norm at most ‖f‖₂. -/
theorem norm_ofLp_le (f : Lp ℝ 2 μ) : ‖D.ofLp f‖ ≤ ‖f‖ := D.norm_toDualMap_comp_toLp_le f

/-- The map L² → 𝔻' is the adjoint of 𝔻 → L² followed by Riesz. -/
theorem ofLp_eq_toDual_adjoint (f : Lp ℝ 2 μ) :
    D.ofLp f = InnerProductSpace.toDual ℝ D.Space (ContinuousLinearMap.adjoint D.toLp f) := by
  ext x
  rw [ofLp_apply, InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]

/--
BH 1991, ch. I § 9.1, proof of propositions 9.1.2 and 9.1.3 a) ("by density", p. 62): the range of
the adjoint of 𝔻 → L² (the domain of A) is dense in 𝔻, without assuming density of 𝔻 in L².

The adjoint of the embedding 𝔻 → L² has dense range in 𝔻 (since the embedding is injective).
-/
theorem denseRange_adjoint_toLp : DenseRange (ContinuousLinearMap.adjoint D.toLp) := by
  have hker : (D.toLp : D.Space →ₗ[ℝ] Lp ℝ 2 μ).ker = ⊥ :=
    LinearMap.ker_eq_bot.2 D.toLp_injective
  have h := ContinuousLinearMap.orthogonal_ker D.toLp
  rw [hker, Submodule.bot_orthogonal_eq_top] at h
  have hd : Dense ((ContinuousLinearMap.adjoint D.toLp : Lp ℝ 2 μ →ₗ[ℝ] D.Space).range :
      Set D.Space) := Submodule.dense_iff_topologicalClosure_eq_top.2 h.symm
  rw [LinearMap.coe_range] at hd
  exact hd

/--
BH 1991, ch. I § 9.1, proposition 9.1.2 (pp. 61–62): L² → 𝔻' has dense range without assuming
density of 𝔻 in L².

The map L² → 𝔻' has dense range.
-/
theorem denseRange_ofLp : DenseRange D.ofLp := by
  have h : ⇑D.ofLp = ⇑(InnerProductSpace.toDual ℝ D.Space) ∘
      ⇑(ContinuousLinearMap.adjoint D.toLp) := by
    funext f
    exact D.ofLp_eq_toDual_adjoint f
  rw [h]
  exact (InnerProductSpace.toDual ℝ D.Space).surjective.denseRange.comp D.denseRange_adjoint_toLp
    (InnerProductSpace.toDual ℝ D.Space).continuous

/--
BH 1991, ch. I § 9.1, proposition 9.1.2 (pp. 61–62): injectivity of L² → 𝔻' is equivalent to density
of 𝔻 in L², a BH framework hypothesis ("by definition, 𝔻 is a dense subspace of L²") not assumed by
the `DirichletForm` framework.

The map L² → 𝔻' is injective if and only if 𝔻 is dense in L².
-/
theorem ofLp_injective_iff : Function.Injective D.ofLp ↔ DenseRange D.toLp := by
  have hmem : ∀ f, D.ofLp f = 0 ↔ f ∈ (D.toLp : D.Space →ₗ[ℝ] Lp ℝ 2 μ).rangeᗮ := by
    intro f
    rw [Submodule.mem_orthogonal]
    constructor
    · intro h u hu
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hu
      have hx : D.ofLp f x = 0 := by rw [h]; rfl
      rw [ofLp_apply] at hx
      rw [real_inner_comm]
      exact hx
    · intro h
      ext x
      show D.ofLp f x = 0
      rw [ofLp_apply, real_inner_comm]
      exact h _ (LinearMap.mem_range_self _ x)
  have hr : Set.range ⇑D.toLp = ((D.toLp : D.Space →ₗ[ℝ] Lp ℝ 2 μ).range : Set (Lp ℝ 2 μ)) :=
    (LinearMap.coe_range _).symm
  rw [DenseRange, hr, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff, injective_iff_map_eq_zero]
  constructor
  · intro h f hf
    exact h f ((hmem f).2 hf)
  · intro h f hf
    exact h f ((hmem f).1 hf)

/--
BH 1991, ch. I § 9.1, proposition 9.1.2 (pp. 61–62), in the BH framework (𝔻 dense in L²).

BH proposition 9.1.2: 𝔻 ↪ L² ↪ 𝔻', two injective continuous linear maps with dense ranges; the
second has norm ≤ 1.
-/
theorem bh_9_1_2 (hdense : DenseRange D.toLp) :
    Function.Injective D.toLp ∧ DenseRange D.toLp ∧ Function.Injective D.ofLp ∧
      DenseRange D.ofLp ∧ ∀ f, ‖D.ofLp f‖ ≤ ‖f‖ :=
  ⟨D.toLp_injective, hdense, D.ofLp_injective_iff.2 hdense, D.denseRange_ofLp, D.norm_ofLp_le⟩

/--
BH 1991, ch. I § 9.1, proposition 9.1.3 a) (p. 62): "f ∈ D(A) and (I − A)f = h", in the form sense.

The condition x ∈ D(A) and (I − A)x = h means (x, g)_𝔻 = (h, g)_{L²} for every g ∈ 𝔻.
-/
def IsResolvent (x : D.Space) (h : Lp ℝ 2 μ) : Prop :=
  ∀ g : D.Space, ⟪x, g⟫_ℝ = ⟪h, D.toLp g⟫_ℝ

/-- The weak resolvent relation holds exactly when x is the adjoint inclusion applied to h. -/
theorem isResolvent_iff {x : D.Space} {h : Lp ℝ 2 μ} :
    D.IsResolvent x h ↔ x = ContinuousLinearMap.adjoint D.toLp h := by
  constructor
  · intro hx
    apply ext_inner_right ℝ
    intro g
    rw [hx g, ContinuousLinearMap.adjoint_inner_left]
  · rintro rfl g
    rw [ContinuousLinearMap.adjoint_inner_left]

/--
BH 1991, ch. I § 9.1, proposition 9.1.3 a) (p. 62): (I − A) maps D(A) ONTO L².

For every h ∈ L², there exists x ∈ D(A) with (I − A)x = h.
-/
theorem bh_9_1_3_a_surj (h : Lp ℝ 2 μ) : ∃ x, D.IsResolvent x h :=
  ⟨_, D.isResolvent_iff.2 rfl⟩

/--
BH 1991, ch. I § 9.1, proposition 9.1.3 a) and its proof,) (p. 62).

BH proposition 9.1.3 a): on D(A), (I − A) followed by L² → 𝔻' equals the Riesz isometry 𝔻 → 𝔻'; in
particular ‖(I − A)x‖_{𝔻'} = ‖x‖_𝔻.
-/
theorem bh_9_1_3_a {x : D.Space} {h : Lp ℝ 2 μ} (hx : D.IsResolvent x h) :
    D.ofLp h = InnerProductSpace.toDual ℝ D.Space x ∧ ‖D.ofLp h‖ = ‖x‖ := by
  have e : D.ofLp h = InnerProductSpace.toDual ℝ D.Space x := by
    ext g
    rw [ofLp_apply, InnerProductSpace.toDual_apply_apply, hx g]
  exact ⟨e, by rw [e, LinearIsometryEquiv.norm_map]⟩

/--
BH 1991, ch. I § 9.1, proposition 9.1.3 a) (p. 62): (I − A)x is well-defined when 𝔻 is dense in L²
(the BH framework).

If 𝔻 is dense in L², then (I − A)x is determined by x.
-/
theorem bh_9_1_3_a_unique (hdense : DenseRange D.toLp) {x : D.Space} {h h' : Lp ℝ 2 μ}
    (h1 : D.IsResolvent x h) (h2 : D.IsResolvent x h') : h = h' :=
  (D.ofLp_injective_iff.2 hdense) ((D.bh_9_1_3_a h1).1.trans (D.bh_9_1_3_a h2).1.symm)

/-- The domain D(A) is dense in 𝔻. -/
theorem dense_resolventDom : Dense {x : D.Space | ∃ h, D.IsResolvent x h} := by
  refine Dense.mono ?_ D.denseRange_adjoint_toLp
  rintro _ ⟨h, rfl⟩
  exact ⟨h, D.isResolvent_iff.2 rfl⟩

/--
BH 1991, ch. I § 9.1, proposition 9.1.3 a) (p. 62): "can be extended into an isometry from 𝔻 onto
𝔻'" — the continuous extension is unique and equals the Riesz isometry.

Every continuous linear map 𝔻 → 𝔻' extending (I − A) is the Riesz isometry.
-/
theorem bh_9_1_3_a_ext (Φ : D.Space →L[ℝ] D.Dual)
    (hΦ : ∀ x h, D.IsResolvent x h → Φ x = D.ofLp h) (x : D.Space) :
    Φ x = InnerProductSpace.toDual ℝ D.Space x := by
  have he := Continuous.ext_on D.dense_resolventDom Φ.continuous
    (InnerProductSpace.toDual ℝ D.Space).continuous
    (fun y hy => by
      obtain ⟨h, hyh⟩ := hy
      exact (hΦ y h hyh).trans (D.bh_9_1_3_a hyh).1)
  exact congrFun he x

/--
BH 1991, ch. I § 9.1, notation 9.1.4 (p. 62): 𝔻⁺.

The cone 𝔻⁺ = {f ∈ 𝔻; f ≥ 0}.
-/
def posCone : Set D.Space := {x | 0 ≤ D.toLp x}

/-- The positive cone consists exactly of form elements with nonnegative a.e. representatives. -/
theorem mem_posCone_iff {x : D.Space} : x ∈ D.posCone ↔ 0 ≤ᵐ[μ] ⇑(D.toLp x) :=
  (Lp.coeFn_nonneg _).symm

/--
BH 1991, ch. I § 9.1, notation 9.1.4 (p. 62): 𝔻'⁺.

The cone 𝔻'⁺ = {T ∈ 𝔻'; ∀ f ∈ 𝔻⁺, ⟨f, T⟩ ≥ 0}.
-/
def dualPos : Set D.Dual := {T | ∀ x ∈ D.posCone, 0 ≤ T x}

/-- The cone of positive finite-energy functionals is closed. -/
theorem isClosed_dualPos : IsClosed D.dualPos := by
  have h : D.dualPos = ⋂ x ∈ D.posCone, {T : D.Dual | 0 ≤ T x} := by
    ext T
    simp [dualPos]
  rw [h]
  exact isClosed_biInter fun x _ =>
    isClosed_le continuous_const (ContinuousLinearMap.apply ℝ ℝ x).continuous

/--
BH 1991, ch. I § 9.1, notation 9.1.4 (p. 62): "𝔻 = 𝔻⁺ − 𝔻⁺".

Every element of 𝔻 is the difference of two elements of 𝔻⁺.
-/
theorem bh_9_1_4 (x : D.Space) : ∃ a ∈ D.posCone, ∃ b ∈ D.posCone, x = a - b := by
  refine ⟨D.supS x 0, ?_, D.supS x 0 - x, ?_, by abel⟩
  · show 0 ≤ D.toLp (D.supS x 0)
    rw [D.toLp_supS, map_zero]
    exact le_sup_right
  · show 0 ≤ D.toLp (D.supS x 0 - x)
    rw [map_sub, D.toLp_supS, map_zero, sub_nonneg]
    exact le_sup_left

/-- Inner product of two nonnegative elements of L². -/
theorem lp_inner_nonneg {f g : Lp ℝ 2 μ} (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_nonneg_of_ae ?_
  filter_upwards [(Lp.coeFn_nonneg f).2 hf, (Lp.coeFn_nonneg g).2 hg] with ω h1 h2
  simp only [Pi.zero_apply] at h1 h2 ⊢
  simpa [RCLike.inner_apply] using mul_nonneg h2 h1

/-- (g, g ∨ 0)_{L²} = ‖g ∨ 0‖². -/
theorem lp_inner_sup_zero (g : Lp ℝ 2 μ) : ⟪g, g ⊔ 0⟫_ℝ = ‖g ⊔ 0‖ ^ 2 := by
  have h0 : ⟪g - g ⊔ 0, g ⊔ 0⟫_ℝ = 0 := by
    rw [MeasureTheory.L2.inner_def]
    refine (integral_congr_ae ?_).trans (integral_zero Ω ℝ)
    filter_upwards [Lp.coeFn_sub g (g ⊔ 0), Lp.coeFn_sup g 0, Lp.coeFn_zero ℝ 2 μ] with ω h1 h2 h3
    rw [h1, Pi.sub_apply, h2, Pi.sup_apply, h3]
    simp only [Pi.zero_apply, RCLike.inner_apply, conj_trivial]
    rcases le_total (g ω) 0 with h | h
    · rw [max_eq_right h]; simp
    · rw [max_eq_left h]; simp
  have e : ⟪g, g ⊔ 0⟫_ℝ = ⟪g - g ⊔ 0, g ⊔ 0⟫_ℝ + ⟪g ⊔ 0, g ⊔ 0⟫_ℝ := by
    rw [← inner_add_left, sub_add_cancel]
  rw [e, h0, zero_add, real_inner_self_eq_norm_sq]

/-- If (g, f)_{L²} ≤ 0 for every f ≥ 0, then g ≤ 0. -/
theorem lp_le_zero_of_inner_nonpos {g : Lp ℝ 2 μ} (h : ∀ f : Lp ℝ 2 μ, 0 ≤ f → ⟪g, f⟫_ℝ ≤ 0) :
    g ≤ 0 := by
  have h1 := h (g ⊔ 0) le_sup_right
  rw [lp_inner_sup_zero] at h1
  have h2 : ‖g ⊔ 0‖ = 0 := by nlinarith [norm_nonneg (g ⊔ 0)]
  have h3 : g ⊔ 0 = 0 := norm_eq_zero.1 h2
  exact sup_eq_right.1 h3

/-- A nonnegative real multiple of a nonnegative L² class is nonnegative. -/
theorem lp_smul_nonneg {c : ℝ} (hc : 0 ≤ c) {f : Lp ℝ 2 μ} (hf : 0 ≤ f) : 0 ≤ c • f := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [Lp.coeFn_smul c f, (Lp.coeFn_nonneg f).2 hf] with ω h1 h2
  rw [h1]
  simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at h2 ⊢
  exact mul_nonneg hc h2

/-- Bipolar version in 𝔻 (identified with 𝔻' by Riesz). -/
theorem closure_adjoint_nonneg :
    closure (ContinuousLinearMap.adjoint D.toLp '' {f : Lp ℝ 2 μ | 0 ≤ f}) =
      {t : D.Space | ∀ x ∈ D.posCone, 0 ≤ ⟪t, x⟫_ℝ} := by
  set A := ContinuousLinearMap.adjoint D.toLp
  set K := A '' {f : Lp ℝ 2 μ | 0 ≤ f} with hK
  have hcl : IsClosed {t : D.Space | ∀ x ∈ D.posCone, 0 ≤ ⟪t, x⟫_ℝ} := by
    have e : {t : D.Space | ∀ x ∈ D.posCone, 0 ≤ ⟪t, x⟫_ℝ} =
        ⋂ x ∈ D.posCone, {t : D.Space | 0 ≤ ⟪t, x⟫_ℝ} := by
      ext t
      simp
    rw [e]
    exact isClosed_biInter fun x _ =>
      isClosed_le continuous_const (continuous_id.inner continuous_const)
  apply le_antisymm
  · refine closure_minimal ?_ hcl
    rintro _ ⟨f, hf, rfl⟩ x hx
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact lp_inner_nonneg hf hx
  · intro t ht
    by_contra hnot
    have hconv : Convex ℝ K := by
      refine Convex.linear_image ?_ (A : Lp ℝ 2 μ →ₗ[ℝ] D.Space)
      intro f hf g hg a b ha hb _
      exact add_nonneg (lp_smul_nonneg ha hf) (lp_smul_nonneg hb hg)
    obtain ⟨ℓ, u, hℓ, hu⟩ :=
      geometric_hahn_banach_closed_point hconv.closure isClosed_closure hnot
    set z := (InnerProductSpace.toDual ℝ D.Space).symm ℓ
    have hz : ∀ a, ℓ a = ⟪z, a⟫_ℝ := fun a => InnerProductSpace.toDual_symm_apply.symm
    have h0 : (0 : ℝ) < u := by
      have hmem : (0 : D.Space) ∈ closure K :=
        subset_closure ⟨0, by simp, map_zero A⟩
      simpa using hℓ 0 hmem
    have hneg : ∀ f : Lp ℝ 2 μ, 0 ≤ f → ⟪D.toLp z, f⟫_ℝ ≤ 0 := by
      intro f hf
      by_contra hpos
      replace hpos := not_le.1 hpos
      set v := ⟪D.toLp z, f⟫_ℝ
      have hmem : A ((u / v) • f) ∈ closure K :=
        subset_closure ⟨(u / v) • f, lp_smul_nonneg (div_pos h0 hpos).le hf, rfl⟩
      have h1 := hℓ _ hmem
      rw [hz, ContinuousLinearMap.adjoint_inner_right, inner_smul_right] at h1
      have h2 : u / v * v = u := div_mul_cancel₀ u hpos.ne'
      linarith
    have hle : D.toLp z ≤ 0 := lp_le_zero_of_inner_nonpos hneg
    have hmz : -z ∈ D.posCone := by
      show 0 ≤ D.toLp (-z)
      rw [map_neg]
      exact neg_nonneg.2 hle
    have h3 := ht (-z) hmz
    rw [inner_neg_right, real_inner_comm] at h3
    rw [hz] at hu
    linarith

/--
BH 1991, ch. I § 9.1, proposition 9.1.5 and its proof ("bipolar theorem", p. 62).

BH proposition 9.1.5: the set {f ∈ L²; f ≥ 0} (mapped into 𝔻') is dense in 𝔻'⁺.
-/
theorem bh_9_1_5 : closure (D.ofLp '' {f : Lp ℝ 2 μ | 0 ≤ f}) = D.dualPos := by
  set R := InnerProductSpace.toDual ℝ D.Space
  have himg : D.ofLp '' {f : Lp ℝ 2 μ | 0 ≤ f} =
      R '' (ContinuousLinearMap.adjoint D.toLp '' {f : Lp ℝ 2 μ | 0 ≤ f}) := by
    rw [Set.image_image]
    exact Set.image_congr fun f _ => D.ofLp_eq_toDual_adjoint f
  rw [himg]
  have hc : closure (R '' (ContinuousLinearMap.adjoint D.toLp '' {f : Lp ℝ 2 μ | 0 ≤ f})) =
      R '' closure (ContinuousLinearMap.adjoint D.toLp '' {f : Lp ℝ 2 μ | 0 ≤ f}) :=
    (R.toHomeomorph.image_closure _).symm
  rw [hc, D.closure_adjoint_nonneg]
  ext T
  constructor
  · rintro ⟨t, ht, rfl⟩ x hx
    rw [InnerProductSpace.toDual_apply_apply]
    exact ht x hx
  · intro hT
    refine ⟨R.symm T, fun x hx => ?_, R.apply_symm_apply T⟩
    rw [InnerProductSpace.toDual_symm_apply]
    exact hT x hx

end DualSpace

end DirichletForm
end ErrorCalculus.Capacity
