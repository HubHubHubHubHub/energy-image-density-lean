import ErrorCalculus.Dirichlet.FiniteEnergyPotential
import ErrorCalculus.Dirichlet.QuasiContinuousRepresentative
import ErrorCalculus.Dirichlet.HilbertWeakStrong
import ErrorCalculus.Dirichlet.LowerSemicontinuous
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic

/-!
# positive finite-energy measures (BH 1991, ch. I § 9.2; Fukushima 1980, § 3.2)

## Main results
Framework: `DirichletForm μ`, topological Ω, `[OpensMeasurableSpace Ω]`. Weak convergence of bounded
sequences in 𝔻 converging in L² (a tool for 9.2.4); bounded continuous representatives; positive
finite-energy measures (definition 9.2.2, p. 63) and Fukushima's form (3.2.1) (p. 69); bounded (E₂)
(`BddContDense`, equivalent to `DensityHyp`, see `FiniteEnergyControls`); the distribution T_τ ∈ 𝔻'
of a finite-energy measure (Hahn–Banach on 𝒞_b(Ω) ∩ 𝔻; the measure-to-distribution direction of
proposition 9.2.1, pp. 63–64), uniqueness and positivity under (E₂); hypothesis (O); proposition
9.2.3 (p. 64: a positive finite-energy measure does not charge polar sets, with τ(G) ≤ ‖T_τ‖
c(G)^{1/2}, Fukushima (3.2.6)); corollary 9.2.4 (pp. 65–66) for every quasi-continuous
representative and Fukushima (3.2.8); injectivity of τ ↦ T_τ. Further topics in BH pp. 63–66, not
treated here: existence of the measure in 9.2.1 (Daniell's theorem under (E₁)–(E₃)), exercises
9.1–9.5.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity
namespace DirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (D : DirichletForm μ)

/-! ## C. Positive finite-energy measures (BH 9.2; Fukushima § 3.2) -/

section WeakLimits

/--
BH 1991, ch. I § 9.2, proof of corollary 9.2.4 (p. 65): "|φₙ| converges to |f| in 𝔻" — strong
convergence is not proved by BH; this weak convergence lemma suffices for the argument. Reuse of
`weak_tendsto_of_bounded_of_clusterPt_unique` and `QuadForm.formInclusion_eq_of_weak_cluster`; an
analogue for every `DirichletForm` of
`ErrorStructure.weak_tendsto_formSpace_of_tendsto_L2_of_energy_le`.

If (xₙ) is bounded in 𝔻 and converges in L² to y, then ⟨xₙ, T⟩ → ⟨y, T⟩ for every T ∈ 𝔻'.
-/
theorem tendsto_apply_of_bounded {x : ℕ → D.Space} {y : D.Space} {R : ℝ}
    (hR : ∀ n, ‖x n‖ ≤ R) (hL : Tendsto (fun n => D.toLp (x n)) atTop (𝓝 (D.toLp y)))
    (T : D.Dual) : Tendsto (fun n => T (x n)) atTop (𝓝 (T y)) := by
  have hw := weak_tendsto_of_bounded_of_clusterPt_unique (V := D.Space) (g := x) (x := y)
    (Eventually.of_forall hR) fun A _ v hv => by
      have hh := QuadForm.formInclusion_eq_of_weak_cluster hv inf_le_left hL
      exact D.toLp_injective hh
  have h := hw (D.potential T)
  simp only [real_inner_comm (D.potential T), inner_potential] at h
  exact h

end WeakLimits

section Measures
variable [TopologicalSpace Ω]

/--
BH 1991, ch. I § 9.2, definition 9.2.2 (p. 63): "f ∈ 𝒞_b(Ω) ∩ 𝔻" — x ∈ 𝔻 admits the bounded
continuous representative φ.

The function φ is a bounded continuous representative of x ∈ 𝔻.
-/
def BddContRep (x : D.Space) (φ : Ω → ℝ) : Prop :=
  Continuous φ ∧ (∃ M, ∀ ω, |φ ω| ≤ M) ∧ ⇑(D.toLp x) =ᵐ[μ] φ

/-- The zero function is a bounded continuous representative of the zero form element. -/
theorem bddContRep_zero : D.BddContRep 0 0 := by
  refine ⟨continuous_const, ⟨0, fun ω => by simp⟩, ?_⟩
  rw [map_zero]
  exact Lp.coeFn_zero ℝ 2 μ

/-- The sum of bounded continuous representatives represents the sum of their form elements. -/
theorem bddContRep_add {x y : D.Space} {φ ψ : Ω → ℝ} (hx : D.BddContRep x φ)
    (hy : D.BddContRep y ψ) : D.BddContRep (x + y) (φ + ψ) := by
  obtain ⟨c1, ⟨M, hM⟩, e1⟩ := hx
  obtain ⟨c2, ⟨N, hN⟩, e2⟩ := hy
  refine ⟨c1.add c2, ⟨M + N, fun ω => ?_⟩, ?_⟩
  · simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hM ω) (hN ω))
  · rw [map_add]
    filter_upwards [Lp.coeFn_add (D.toLp x) (D.toLp y), e1, e2] with ω h1 h2 h3
    rw [h1, Pi.add_apply, Pi.add_apply, h2, h3]

/-- Real scalar multiplication preserves bounded continuous representatives. -/
theorem bddContRep_smul (c : ℝ) {x : D.Space} {φ : Ω → ℝ} (hx : D.BddContRep x φ) :
    D.BddContRep (c • x) (c • φ) := by
  obtain ⟨c1, ⟨M, hM⟩, e1⟩ := hx
  refine ⟨c1.const_smul c, ⟨|c| * M, fun ω => ?_⟩, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM ω) (abs_nonneg c)
  · rw [map_smul]
    filter_upwards [Lp.coeFn_smul c (D.toLp x), e1] with ω h1 h2
    rw [h1, Pi.smul_apply, Pi.smul_apply, h2]

/--
The difference of bounded continuous representatives represents the difference of the elements.
-/
theorem bddContRep_sub {x y : D.Space} {φ ψ : Ω → ℝ} (hx : D.BddContRep x φ)
    (hy : D.BddContRep y ψ) : D.BddContRep (x - y) (φ - ψ) := by
  have h := D.bddContRep_add hx (D.bddContRep_smul (-1) hy)
  rw [neg_one_smul, ← sub_eq_add_neg] at h
  have e : φ + (-1 : ℝ) • ψ = φ - ψ := by
    funext ω
    simp [sub_eq_add_neg]
  rwa [e] at h

/-- The absolute value of a bounded continuous representative represents the form absolute value. -/
theorem bddContRep_absS {x : D.Space} {φ : Ω → ℝ} (hx : D.BddContRep x φ) :
    D.BddContRep (D.absS x) (fun ω => |φ ω|) := by
  obtain ⟨c1, ⟨M, hM⟩, e1⟩ := hx
  refine ⟨c1.abs, ⟨M, fun ω => by rw [abs_abs]; exact hM ω⟩, ?_⟩
  rw [D.toLp_absS]
  filter_upwards [Lp.coeFn_abs (D.toLp x), e1] with ω h1 h2
  rw [h1, h2]

/-- A bounded continuous representative is integrable for a finite measure. -/
theorem integrable_of_bddContRep [OpensMeasurableSpace Ω] (τ : Measure Ω) [IsFiniteMeasure τ]
    {x : D.Space} {φ : Ω → ℝ} (h : D.BddContRep x φ) : Integrable φ τ :=
  Integrable.of_bound h.1.aestronglyMeasurable h.2.1.choose
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact h.2.1.choose_spec ω)

/--
BH 1991, ch. I § 9.2, definition 9.2.2 (p. 63).

BH definition 9.2.2: τ is a positive finite-energy measure if it has finite mass and there exists
C with |∫ φ dτ| ≤ C ‖x‖_𝔻 for every x ∈ 𝒞_b(Ω) ∩ 𝔻 with representative φ.
-/
def IsFiniteEnergy (τ : Measure Ω) : Prop :=
  IsFiniteMeasure τ ∧
    ∃ C : ℝ, ∀ (x : D.Space) (φ : Ω → ℝ), D.BddContRep x φ → |∫ ω, φ ω ∂τ| ≤ C * ‖x‖

/--
Fukushima 1980, § 3.2, (3.2.1) (p. 69): the form "∫ |v| dμ ≤ C ℰ₁(v, v)^{1/2}" is equivalent to BH
definition 9.2.2 (p. 63), on 𝒞_b(Ω) ∩ 𝔻.

The measure τ has finite energy (BH 9.2.2) if and only if ∫ |φ| dτ ≤ C ‖x‖ (Fukushima's form).
-/
theorem isFiniteEnergy_iff_abs {τ : Measure Ω} :
    D.IsFiniteEnergy τ ↔ IsFiniteMeasure τ ∧
      ∃ C : ℝ, ∀ (x : D.Space) (φ : Ω → ℝ), D.BddContRep x φ → ∫ ω, |φ ω| ∂τ ≤ C * ‖x‖ := by
  constructor
  · rintro ⟨hfin, C, hC⟩
    refine ⟨hfin, max C 0, fun x φ h => ?_⟩
    have h1 := hC _ _ (D.bddContRep_absS h)
    rw [abs_of_nonneg (integral_nonneg fun ω => abs_nonneg _)] at h1
    calc ∫ ω, |φ ω| ∂τ ≤ C * ‖D.absS x‖ := h1
      _ ≤ max C 0 * ‖D.absS x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max C 0 * ‖x‖ := mul_le_mul_of_nonneg_left (D.norm_absS_le x) (le_max_right _ _)
  · rintro ⟨hfin, C, hC⟩
    exact ⟨hfin, C, fun x φ h => abs_integral_le_integral_abs.trans (hC x φ h)⟩

/--
BH 1991, ch. I § 9.2, hypothesis (E₂), p. 63, in its bounded form: elements of the form space with a
bounded continuous representative are dense in the form norm. BH states density using continuous
representatives.
-/
def BddContDense : Prop := Dense {x : D.Space | ∃ φ, D.BddContRep x φ}

/-- The subspace 𝒞_b(Ω) ∩ 𝔻. -/
def bddContSub : Submodule ℝ D.Space where
  carrier := {x | ∃ φ, D.BddContRep x φ}
  add_mem' := fun ⟨φ, h1⟩ ⟨ψ, h2⟩ => ⟨φ + ψ, D.bddContRep_add h1 h2⟩
  zero_mem' := ⟨0, D.bddContRep_zero⟩
  smul_mem' := fun c _ ⟨φ, h⟩ => ⟨c • φ, D.bddContRep_smul c h⟩

/--
The continuous-representative subspace consists of elements admitting a bounded continuous
representative.
-/
theorem mem_bddContSub {x : D.Space} : x ∈ D.bddContSub ↔ ∃ φ, D.BddContRep x φ := Iff.rfl

/-- A chosen bounded continuous representative. -/
def repOf (x : D.bddContSub) : Ω → ℝ := Classical.choose (D.mem_bddContSub.1 x.2)

/--
The chosen representative of a continuous-subspace element is bounded, continuous and correct a.e.
-/
theorem repOf_spec (x : D.bddContSub) : D.BddContRep (x : D.Space) (D.repOf x) :=
  Classical.choose_spec (D.mem_bddContSub.1 x.2)

variable [OpensMeasurableSpace Ω]

/-- ∫ φ dτ is independent of the chosen bounded continuous representative. -/
theorem integral_eq_of_bddContRep {τ : Measure Ω} (hτ : D.IsFiniteEnergy τ) {x : D.Space}
    {φ ψ : Ω → ℝ} (h1 : D.BddContRep x φ) (h2 : D.BddContRep x ψ) :
    ∫ ω, φ ω ∂τ = ∫ ω, ψ ω ∂τ := by
  haveI := hτ.1
  obtain ⟨C, hC⟩ := hτ.2
  have h4 := hC _ _ (D.bddContRep_sub h1 h2)
  rw [sub_self, norm_zero, mul_zero] at h4
  have h5 : ∫ ω, (φ - ψ) ω ∂τ = 0 := abs_nonpos_iff.1 h4
  simp only [Pi.sub_apply] at h5
  rw [integral_sub (D.integrable_of_bddContRep τ h1) (D.integrable_of_bddContRep τ h2)] at h5
  linarith

/-- The linear form x ↦ ∫ φ dτ on 𝒞_b(Ω) ∩ 𝔻. -/
def distLin (τ : Measure Ω) (hτ : D.IsFiniteEnergy τ) : D.bddContSub →ₗ[ℝ] ℝ where
  toFun x := ∫ ω, D.repOf x ω ∂τ
  map_add' x y := by
    haveI := hτ.1
    have hs : D.BddContRep ((x + y : D.bddContSub) : D.Space) (D.repOf x + D.repOf y) :=
      D.bddContRep_add (D.repOf_spec x) (D.repOf_spec y)
    rw [D.integral_eq_of_bddContRep hτ (D.repOf_spec (x + y)) hs]
    exact integral_add (D.integrable_of_bddContRep τ (D.repOf_spec x))
      (D.integrable_of_bddContRep τ (D.repOf_spec y))
  map_smul' c x := by
    have hs : D.BddContRep ((c • x : D.bddContSub) : D.Space) (c • D.repOf x) :=
      D.bddContRep_smul c (D.repOf_spec x)
    rw [D.integral_eq_of_bddContRep hτ (D.repOf_spec (c • x)) hs]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

/-- The continuous form on 𝒞_b(Ω) ∩ 𝔻 (bound from definition 9.2.2). -/
def distCLM (τ : Measure Ω) (hτ : D.IsFiniteEnergy τ) : StrongDual ℝ D.bddContSub :=
  (D.distLin τ hτ).mkContinuous (Classical.choose hτ.2) fun x => by
    rw [Real.norm_eq_abs]
    exact Classical.choose_spec hτ.2 _ _ (D.repOf_spec x)

open Classical in
/--
BH 1991, ch. I § 9.2, proposition 9.2.1 and definition 9.2.2 (pp. 63–64): the
measure-to-distribution direction of the correspondence M⁺ ↔ 𝔻'⁺ (Hahn–Banach extension; unique
under (E₂), `toDist_unique`).

The distribution T_τ ∈ 𝔻' of a finite-energy measure τ (0 if τ does not have finite energy).
-/
def toDist (τ : Measure Ω) : D.Dual :=
  if hτ : D.IsFiniteEnergy τ then
    Classical.choose (exists_extension_norm_eq D.bddContSub (D.distCLM τ hτ))
  else 0

/--
BH 1991, ch. I § 9.2, proposition 9.2.1 (p. 63), the equality ⟨f, T⟩ = ∫ f dτ on 𝒞_b(Ω) ∩ 𝔻.

⟨x, T_τ⟩ = ∫ φ dτ for every bounded continuous representative φ of x.
-/
theorem toDist_apply {τ : Measure Ω} (hτ : D.IsFiniteEnergy τ) {x : D.Space} {φ : Ω → ℝ}
    (h : D.BddContRep x φ) : D.toDist τ x = ∫ ω, φ ω ∂τ := by
  have hx : x ∈ D.bddContSub := ⟨φ, h⟩
  have hspec := (Classical.choose_spec
    (exists_extension_norm_eq D.bddContSub (D.distCLM τ hτ))).1 ⟨x, hx⟩
  rw [toDist, dif_pos hτ]
  refine hspec.trans ?_
  exact D.integral_eq_of_bddContRep hτ (D.repOf_spec ⟨x, hx⟩) h

/--
BH 1991, ch. I § 9.2, proposition 9.2.1, uniqueness (pp. 63–64) under the density part of (E₂): T_τ
is the only distribution equal to ∫ φ dτ on 𝒞_b(Ω) ∩ 𝔻.

Under bounded (E₂), every T ∈ 𝔻' with ⟨x, T⟩ = ∫ φ dτ on 𝒞_b(Ω) ∩ 𝔻 equals T_τ.
-/
theorem toDist_unique (hd : D.BddContDense) {τ : Measure Ω} (hτ : D.IsFiniteEnergy τ)
    {T : D.Dual} (hT : ∀ x φ, D.BddContRep x φ → T x = ∫ ω, φ ω ∂τ) : T = D.toDist τ := by
  have he := Continuous.ext_on hd T.continuous (D.toDist τ).continuous fun y hy => by
    obtain ⟨φ, h⟩ := hy
    exact (hT y φ h).trans (D.toDist_apply hτ h).symm
  exact ContinuousLinearMap.ext fun x => congrFun he x

/--
BH 1991, ch. I § 9.2, proposition 9.2.1 and definition 9.2.2 (pp. 63–64): T_τ ∈ 𝔻'⁺, under the
density part of (E₂) (weak convergence in place of "|φₙ| → |f| in 𝔻").

Under bounded (E₂), the distribution of a positive finite-energy measure is positive.
-/
theorem toDist_mem_dualPos {τ : Measure Ω} (hτ : D.IsFiniteEnergy τ) (hd : D.BddContDense) :
    D.toDist τ ∈ D.dualPos := by
  intro x hx
  have hz : ∀ n : ℕ, ∃ z ∈ {w : D.Space | ∃ φ, D.BddContRep w φ}, dist x z < 1 / ((n : ℝ) + 1) :=
    fun n => hd.exists_dist_lt x (by positivity)
  choose z hz hzd using hz
  have hz' : ∀ n, ∃ φ, D.BddContRep (z n) φ := hz
  choose φ hφ using hz'
  have hw : ∀ n, D.BddContRep (D.absS (z n)) (fun ω => |φ n ω|) :=
    fun n => D.bddContRep_absS (hφ n)
  have hnonneg : ∀ n, 0 ≤ D.toDist τ (D.absS (z n)) := fun n => by
    rw [D.toDist_apply hτ (hw n)]
    exact integral_nonneg fun ω => abs_nonneg _
  have hdist : ∀ n, ‖z n - x‖ ≤ 1 / ((n : ℝ) + 1) := fun n => by
    rw [← dist_eq_norm, dist_comm]
    exact (hzd n).le
  have hbound : ∀ n, ‖D.absS (z n)‖ ≤ ‖x‖ + 1 := fun n => by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc ‖D.absS (z n)‖ ≤ ‖z n‖ := D.norm_absS_le _
      _ = ‖x + (z n - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖z n - x‖ := norm_add_le _ _
      _ ≤ ‖x‖ + 1 := by linarith [hdist n]
  have hL : Tendsto (fun n => D.toLp (D.absS (z n))) atTop (𝓝 (D.toLp x)) := by
    have hxabs : D.toLp x = |D.toLp x| := (abs_of_nonneg hx).symm
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [D.toLp_absS, hxabs]
    calc ‖|D.toLp (z n)| - |D.toLp x|‖ ≤ ‖D.toLp (z n) - D.toLp x‖ := norm_abs_sub_abs _ _
      _ = ‖D.toLp (z n - x)‖ := by rw [map_sub]
      _ ≤ ‖z n - x‖ := D.norm_toLp_le _
      _ ≤ 1 / ((n : ℝ) + 1) := hdist n
  exact ge_of_tendsto' (D.tendsto_apply_of_bounded hbound hL (D.toDist τ)) hnonneg

/--
BH 1991, ch. I § 9.2, proof of proposition 9.2.3,) (p. 64): the increasing sequence kₚ ∈ 𝒞(Ω)
tending to 1_G, taken here in 𝒞_b(Ω) ∩ 𝔻 without requiring monotonicity (hypothesis (O); it replaces
BH's Stone–Weierstrass approximation on the compact sets Kₙ of (E₃) and is not comparable to
(E₁)–(E₃)).

The pair (x, k) approximates the open set G: kₚ is a bounded continuous representative of xₚ, 0 ≤ kₚ
≤ 1, kₚ = 0 outside G, and kₚ → 1 on G.
-/
def IsOpenApprox (G : Set Ω) (x : ℕ → D.Space) (k : ℕ → Ω → ℝ) : Prop :=
  (∀ p, D.BddContRep (x p) (k p)) ∧ (∀ p ω, 0 ≤ k p ω) ∧ (∀ p ω, k p ω ≤ 1) ∧
    (∀ p ω, ω ∉ G → k p ω = 0) ∧ ∀ ω ∈ G, Tendsto (fun p => k p ω) atTop (𝓝 1)

/--
hypothesis (O) (a variant of BH's (E₁)–(E₃), p. 63): every open set is approximated in the sense of
`IsOpenApprox`.

Hypothesis (O): every open set G admits an approximation (x, k) in the sense of `IsOpenApprox`.
-/
def OpenApprox : Prop :=
  ∀ G : Set Ω, IsOpen G → ∃ (x : ℕ → D.Space) (k : ℕ → Ω → ℝ), D.IsOpenApprox G x k

/-- ∫ kₚ dτ → τ(G) (dominated convergence). -/
theorem tendsto_integral_approx {τ : Measure Ω} [IsFiniteMeasure τ] {G : Set Ω} (hG : IsOpen G)
    {x : ℕ → D.Space} {k : ℕ → Ω → ℝ} (hk : D.IsOpenApprox G x k) :
    Tendsto (fun p => ∫ ω, k p ω ∂τ) atTop (𝓝 (τ.real G)) := by
  have hlim : ∀ ω, Tendsto (fun p => k p ω) atTop (𝓝 (G.indicator 1 ω)) := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem hω, Pi.one_apply]
      exact hk.2.2.2.2 ω hω
    · rw [Set.indicator_of_notMem hω]
      have h0 : ∀ p, k p ω = 0 := fun p => hk.2.2.2.1 p ω hω
      simp only [h0]
      exact tendsto_const_nhds
  have h := tendsto_integral_of_dominated_convergence (μ := τ) (fun _ => (1 : ℝ))
    (fun p => (hk.1 p).1.aestronglyMeasurable) (integrable_const 1)
    (fun p => ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hk.2.1 p ω)]
      exact hk.2.2.1 p ω)
    (ae_of_all _ hlim)
  rwa [integral_indicator_one hG.measurableSet] at h

/--
BH 1991, ch. I § 9.2, end of the proof of proposition 9.2.3 (p. 65): τ(G) ≤ ‖T‖_{𝔻'} c(G)^{1/2};
Fukushima 1980, Lemma 3.2.2, (3.2.6) (pp. 70–71), under bounded (E₂) and (O).

τ(G) ≤ ‖T_τ‖ ‖e_G‖ = ‖T_τ‖ c(G)^{1/2} for open G of finite capacity.
-/
theorem measure_le_of_isOpen {τ : Measure Ω} (hτ : D.IsFiniteEnergy τ) (hd : D.BddContDense)
    (ho : D.OpenApprox) {G : Set Ω} (hG : IsOpen G) (hne : (D.adm G).Nonempty) :
    τ.real G ≤ ‖D.toDist τ‖ * ‖D.equilibrium G‖ := by
  haveI := hτ.1
  obtain ⟨x, k, hk⟩ := ho G hG
  set T := D.toDist τ
  set e := D.equilibrium G
  have hpos := D.toDist_mem_dualPos hτ hd
  have hle : ∀ p, ∫ ω, k p ω ∂τ ≤ T e := by
    intro p
    rw [← D.toDist_apply hτ (hk.1 p)]
    have hmem : e - x p ∈ D.posCone := by
      rw [D.mem_posCone_iff, map_sub]
      have hm := (D.equilibrium_spec hne).1
      have hb := (D.bh_8_1_2_a (D.capAE_ne_top_iff.2 hne)).2
      filter_upwards [hm, hb, (hk.1 p).2.2, Lp.coeFn_sub (D.toLp e) (D.toLp (x p))]
        with ω h1 h2 h3 h4
      rw [Pi.zero_apply, h4, Pi.sub_apply, h3]
      by_cases hω : ω ∈ G
      · linarith [h1 hω, hk.2.2.1 p ω]
      · rw [hk.2.2.2.1 p ω hω]
        linarith [h2.1]
    have h := hpos _ hmem
    rw [map_sub] at h
    linarith
  have hTe : T e ≤ ‖T‖ * ‖e‖ :=
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact T.le_opNorm e)
  exact le_of_tendsto' (D.tendsto_integral_approx hG hk) fun p => (hle p).trans hTe

/--
BH 1991, ch. I § 9.2, proposition 9.2.3 (p. 64); Fukushima 1980, Lemma 3.2.2 (p. 70); under bounded
(E₂) and (O), for every set A (not only A ∈ 𝓕).

BH proposition 9.2.3: a positive finite-energy measure does not charge polar sets.
-/
theorem bh_9_2_3 {τ : Measure Ω} (hτ : D.IsFiniteEnergy τ) (hd : D.BddContDense)
    (ho : D.OpenApprox) {A : Set Ω} (hA : D.IsPolar A) : τ A = 0 := by
  haveI := hτ.1
  set T := D.toDist τ
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  set δ : ℝ := (ε : ℝ) / (‖T‖ + 1) with hδdef
  have hδ : 0 < δ := div_pos hε' (by positivity)
  have hcap : D.cap A < ENNReal.ofReal (δ ^ 2) := by
    rw [show D.cap A = 0 from hA]
    exact ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨G, hGo, hAG, hGc⟩ := D.exists_isOpen_capAE_lt hcap
  have hne : (D.adm G).Nonempty := D.capAE_ne_top_iff.1 (ne_top_of_lt hGc)
  have he : ‖D.equilibrium G‖ < δ := by
    rw [D.capAE_eq_equilibrium hne, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hGc
    exact lt_of_pow_lt_pow_left₀ 2 hδ.le hGc
  have h2 : τ.real G ≤ ε := by
    calc τ.real G ≤ ‖T‖ * ‖D.equilibrium G‖ := D.measure_le_of_isOpen hτ hd ho hGo hne
      _ ≤ ‖T‖ * δ := mul_le_mul_of_nonneg_left he.le (norm_nonneg _)
      _ ≤ ε := by
          rw [hδdef, ← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg T]
  calc τ A ≤ τ G := measure_mono hAG
    _ = ENNReal.ofReal (τ.real G) := (ENNReal.ofReal_toReal (measure_ne_top τ G)).symm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal h2
    _ = ε := ENNReal.ofReal_coe_nnreal

/-- Quasi-everywhere ⇒ τ-almost everywhere. -/
theorem ae_of_qe_of_isFiniteEnergy {τ : Measure Ω} (hτ : D.IsFiniteEnergy τ)
    (hd : D.BddContDense) (ho : D.OpenApprox) {p : Ω → Prop}
    (h : ∀ᵐ ω ∂D.capOuter, p ω) : ∀ᵐ ω ∂τ, p ω := by
  rw [ae_iff] at h ⊢
  exact D.bh_9_2_3 hτ hd ho h

/--
BH 1991, ch. I § 9.2, corollary 9.2.4 and its proof (pp. 65–66); Fukushima 1980, Theorem 3.2.2,
(3.2.7)–(3.2.8) (p. 71); under bounded (E₂) and (O); BH quasi-continuity (8.1.5).

BH corollary 9.2.4: for every x ∈ 𝔻 with quasi-continuous representative f̃, f̃ ∈ L¹(τ) and ⟨x, T_τ⟩
= ∫ f̃ dτ.
-/
theorem bh_9_2_4 {τ : Measure Ω} (hτ : D.IsFiniteEnergy τ) (hd : D.BddContDense)
    (ho : D.OpenApprox) {x : D.Space} {f : Ω → ℝ} (hf : D.QuasiContinuous f)
    (hfx : ⇑(D.toLp x) =ᵐ[μ] f) : Integrable f τ ∧ D.toDist τ x = ∫ ω, f ω ∂τ := by
  haveI := hτ.1
  set T := D.toDist τ with hTdef
  have hz : ∀ n : ℕ, ∃ z ∈ {w : D.Space | ∃ φ, D.BddContRep w φ}, dist x z < (1 / 4 : ℝ) ^ n :=
    fun n => hd.exists_dist_lt x (pow_pos (by norm_num) n)
  choose z hz hzd using hz
  have hz' : ∀ n, ∃ φ, D.BddContRep (z n) φ := hz
  choose φ hφ using hz'
  have hxy : ∀ n, ‖z n - x‖ ≤ (1 / 4 : ℝ) ^ n := fun n => by
    rw [← dist_eq_norm, dist_comm]
    exact (hzd n).le
  have hq : ∀ n, D.QuasiContinuous (φ n) := fun n => D.quasiContinuous_of_continuous (hφ n).1
  have hrep : ∀ n, ⇑(D.toLp (z n)) =ᵐ[μ] φ n := fun n => (hφ n).2.2
  have hint : ∀ n, Integrable (φ n) τ := fun n => D.integrable_of_bddContRep τ (hφ n)
  -- The exceptional set ⋂ₚ Ωₚ is polar, hence τ-null (9.2.3).
  have hpolar : D.IsPolar (⋂ p, tailBad φ p) := by
    refine le_antisymm (ge_of_tendsto tendsto_bound (Eventually.of_forall fun p => ?_)) zero_le
    exact (D.cap_mono (Set.iInter_subset _ p)).trans (D.cap_tailBad_le hxy hq hrep p)
  have hnull : ∀ᵐ ω ∂τ, ω ∉ ⋂ p, tailBad φ p :=
    measure_eq_zero_iff_ae_notMem.1 (D.bh_9_2_3 hτ hd ho hpolar)
  -- The constructed limit equals f̃ quasi-everywhere (8.2.1), hence τ-a.e.
  have hqf : qlim φ =ᵐ[D.capOuter] f :=
    D.bh_8_2_1_unique (D.quasiContinuous_qlim hxy hq hrep) hf
      ((D.ae_eq_qlim hxy hq hrep).symm.trans hfx)
  have hqfτ : ∀ᵐ ω ∂τ, qlim φ ω = f ω := D.ae_of_qe_of_isFiniteEnergy hτ hd ho hqf
  have hlim : ∀ᵐ ω ∂τ, Tendsto (fun n => φ n ω) atTop (𝓝 (f ω)) := by
    filter_upwards [hnull, hqfτ] with ω h1 h2
    obtain ⟨p, hp⟩ : ∃ p, ω ∉ tailBad φ p := by
      by_contra hcon
      exact h1 (Set.mem_iInter.2 fun p => by_contra fun h' => hcon ⟨p, h'⟩)
    rw [← h2]
    exact (tendsto_qlim_of_notMem hp).1
  have hmeas : AEStronglyMeasurable f τ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hφ n).1.aestronglyMeasurable) hlim
  -- L¹(τ) bound between approximants: ∫ |φₘ − φₙ| dτ = ⟨|zₘ − zₙ|, T⟩ ≤ ‖T‖ ‖zₘ − zₙ‖.
  have hpair : ∀ m n, ∫ ω, |φ m ω - φ n ω| ∂τ ≤ ‖T‖ * ‖z m - z n‖ := by
    intro m n
    have hr : D.BddContRep (D.absS (z m - z n)) (fun ω => |φ m ω - φ n ω|) :=
      D.bddContRep_absS (D.bddContRep_sub (hφ m) (hφ n))
    rw [← D.toDist_apply hτ hr]
    calc T (D.absS (z m - z n)) ≤ |T (D.absS (z m - z n))| := le_abs_self _
      _ ≤ ‖T‖ * ‖D.absS (z m - z n)‖ := by rw [← Real.norm_eq_abs]; exact T.le_opNorm _
      _ ≤ ‖T‖ * ‖z m - z n‖ := mul_le_mul_of_nonneg_left (D.norm_absS_le _) (norm_nonneg _)
  have hzz : ∀ m n, n ≤ m → ‖z m - z n‖ ≤ 2 * (1 / 4 : ℝ) ^ n := by
    intro m n hnm
    have e : z m - z n = (z m - x) - (z n - x) := by abel
    rw [e]
    have hmn : (1 / 4 : ℝ) ^ m ≤ (1 / 4 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hnm
    calc ‖(z m - x) - (z n - x)‖ ≤ ‖z m - x‖ + ‖z n - x‖ := norm_sub_le _ _
      _ ≤ (1 / 4 : ℝ) ^ m + (1 / 4 : ℝ) ^ n := add_le_add (hxy m) (hxy n)
      _ ≤ 2 * (1 / 4 : ℝ) ^ n := by linarith
  -- Fatou
  have hfatou : ∀ n, ∫⁻ ω, ENNReal.ofReal |f ω - φ n ω| ∂τ ≤
      ENNReal.ofReal (‖T‖ * (2 * (1 / 4 : ℝ) ^ n)) := by
    intro n
    have hae : (fun ω => ENNReal.ofReal |f ω - φ n ω|) =ᵐ[τ]
        fun ω => liminf (fun m => ENNReal.ofReal |φ m ω - φ n ω|) atTop := by
      filter_upwards [hlim] with ω hω
      have ht : Tendsto (fun m => ENNReal.ofReal |φ m ω - φ n ω|) atTop
          (𝓝 (ENNReal.ofReal |f ω - φ n ω|)) :=
        (ENNReal.continuous_ofReal.tendsto _).comp ((hω.sub_const (φ n ω)).abs)
      exact ht.liminf_eq.symm
    rw [lintegral_congr_ae hae]
    refine (lintegral_liminf_le' fun m => ?_).trans ?_
    · exact (((hφ m).1.sub (hφ n).1).abs.measurable.ennreal_ofReal).aemeasurable
    · refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
      refine eventually_atTop.2 ⟨n, fun m hm => ?_⟩
      have hI : Integrable (fun ω => |φ m ω - φ n ω|) τ := ((hint m).sub (hint n)).abs
      rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun ω => abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal
        ((hpair m n).trans (mul_le_mul_of_nonneg_left (hzz m n hm) (norm_nonneg _)))
  -- Integrability of f̃.
  have hI0 : Integrable (fun ω => f ω - φ 0 ω) τ := by
    refine ⟨hmeas.sub (hint 0).1, ?_⟩
    rw [HasFiniteIntegral]
    simp only [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt (hfatou 0) ENNReal.ofReal_lt_top
  have hfint : Integrable f τ := by
    have h := hI0.add (hint 0)
    have e : ((fun ω => f ω - φ 0 ω) + φ 0) = f := by
      funext ω
      simp
    rwa [e] at h
  refine ⟨hfint, ?_⟩
  -- Passage to the limit.
  have h0 : Tendsto (fun n : ℕ => ‖T‖ * (2 * (1 / 4 : ℝ) ^ n)) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).const_mul 2).const_mul ‖T‖
    simpa using h
  have hconv1 : Tendsto (fun n => ∫ ω, φ n ω ∂τ) atTop (𝓝 (∫ ω, f ω ∂τ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h0
    rw [Real.dist_eq, ← integral_sub (hint n) hfint]
    have hIn : Integrable (fun ω => |f ω - φ n ω|) τ := (hfint.sub (hint n)).abs
    have hb := hfatou n
    rw [← ofReal_integral_eq_lintegral_ofReal hIn (ae_of_all _ fun ω => abs_nonneg _)] at hb
    have hb' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hb
    calc |∫ ω, (φ n ω - f ω) ∂τ| ≤ ∫ ω, |φ n ω - f ω| ∂τ := abs_integral_le_integral_abs
      _ = ∫ ω, |f ω - φ n ω| ∂τ := by
          congr 1
          funext ω
          exact abs_sub_comm _ _
      _ ≤ ‖T‖ * (2 * (1 / 4 : ℝ) ^ n) := hb'
  have hconv2 : Tendsto (fun n => ∫ ω, φ n ω ∂τ) atTop (𝓝 (T x)) := by
    have hzx : Tendsto z atTop (𝓝 x) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun n => norm_nonneg _) hxy
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have h := (T.continuous.tendsto x).comp hzx
    refine h.congr fun n => ?_
    exact D.toDist_apply hτ (hφ n)
  exact tendsto_nhds_unique hconv2 hconv1

/--
Fukushima 1980, Theorem 3.2.2, (3.2.8) (p. 71), α = 1, under bounded (E₂) and (O): ℰ₁(U₁τ, v) = ∫ ṽ
dτ.

(U₁τ, x)_𝔻 = ∫ f̃ dτ for every quasi-continuous representative f̃ of x.
-/
theorem inner_potential_toDist {τ : Measure Ω} (hτ : D.IsFiniteEnergy τ) (hd : D.BddContDense)
    (ho : D.OpenApprox) {x : D.Space} {f : Ω → ℝ} (hf : D.QuasiContinuous f)
    (hfx : ⇑(D.toLp x) =ᵐ[μ] f) : ⟪D.potential (D.toDist τ), x⟫_ℝ = ∫ ω, f ω ∂τ := by
  rw [inner_potential]
  exact (D.bh_9_2_4 hτ hd ho hf hfx).2

/--
BH 1991, ch. I § 9.2 (p. 64): "there is clearly a one to one map between 𝔻'⁺ and … M⁺", the
injective direction, under (O) and Borel Ω.

Two finite-energy measures with the same distribution are equal.
-/
theorem toDist_injective [BorelSpace Ω] (ho : D.OpenApprox)
    {τ σ : Measure Ω} (hτ : D.IsFiniteEnergy τ) (hσ : D.IsFiniteEnergy σ)
    (h : D.toDist τ = D.toDist σ) : τ = σ := by
  haveI := hτ.1
  haveI := hσ.1
  have hopen : ∀ G : Set Ω, IsOpen G → τ G = σ G := by
    intro G hG
    obtain ⟨x, k, hk⟩ := ho G hG
    have h1 := D.tendsto_integral_approx (τ := τ) hG hk
    have h2 := D.tendsto_integral_approx (τ := σ) hG hk
    have e : ∀ p, ∫ ω, k p ω ∂τ = ∫ ω, k p ω ∂σ := fun p => by
      rw [← D.toDist_apply hτ (hk.1 p), ← D.toDist_apply hσ (hk.1 p), h]
    simp only [e] at h1
    have hr : τ.real G = σ.real G := tendsto_nhds_unique h1 h2
    rw [measureReal_def, measureReal_def] at hr
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top τ G) (measure_ne_top σ G)).1 hr
  refine ext_of_generate_finite {s : Set Ω | IsOpen s} ?_ isPiSystem_isOpen
    (fun s hs => hopen s hs) (hopen Set.univ isOpen_univ)
  rw [BorelSpace.measurable_eq (α := Ω)]
  rfl

end Measures

end DirichletForm
end ErrorCalculus.Capacity
