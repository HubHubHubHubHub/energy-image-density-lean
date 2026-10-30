import ErrorCalculus.Dirichlet.CapacityHilbert
import ErrorCalculus.Dirichlet.CapacityForm
import ErrorCalculus.Dirichlet.WhiteNoiseHilbert
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Order.SetAccumulate
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-!
# capacity of a Dirichlet form (BH 1991, ch. I § 8.1, pp. 52–54)

## Main results
The a.e. capacity of an arbitrary set (BH definition 8.1.1, p. 52, extended), equilibrium potential
and proposition 8.1.2 (pp. 52–53), strong subadditivity, continuity from below, outer capacity `cap`
(definition 8.1.1), proposition 8.1.3 a)–d) (p. 53), capacity outer measure, polar sets and
"quasi-everywhere" (definition 8.1.4 and remark 8.1.4.1, pp. 53–54); continuity from above on
compact sets (Fukushima 1980, § 3.1, Theorem 3.1.1 (iii), p. 63). Capacity takes values in [0,
∞], with the empty infimum equal to ∞ as in BH.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity

variable {Ω : Type*} [MeasurableSpace Ω]

namespace DirichletForm
variable {μ : Measure Ω} (D : DirichletForm μ)

/-! ## C. Capacity (BH I.8.1) -/

/--
BH 1991, ch. I § 8.1, definition 8.1.1 (p. 52): the admissible set 𝓛_G.

Elements of 𝔻 that are at least 1 almost everywhere on G (inequality between classes).
-/
def adm (G : Set Ω) : Set D.Space := {x | ∀ᵐ ω ∂μ, ω ∈ G → 1 ≤ D.toLp x ω}

/-- The L² functions that are at least one almost everywhere on G form a closed set. -/
theorem isClosed_setOf_ae_one_le (G : Set Ω) :
    IsClosed {f : Lp ℝ 2 μ | ∀ᵐ ω ∂μ, ω ∈ G → 1 ≤ f ω} := by
  refine IsSeqClosed.isClosed ?_
  intro f g hf hlim
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hall : ∀ᵐ ω ∂μ, ∀ n, ω ∈ G → 1 ≤ f n ω := ae_all_iff.2 hf
  filter_upwards [hns, hall] with ω h1 h2 hω
  exact ge_of_tendsto' h1 fun i => h2 (ns i) hω

/-- The admissible subset of the form space for G is closed. -/
theorem isClosed_adm (G : Set Ω) : IsClosed (D.adm G) :=
  (isClosed_setOf_ae_one_le G).preimage D.toLp.continuous

/-- The admissible subset of the form space for G is convex. -/
theorem convex_adm (G : Set Ω) : Convex ℝ (D.adm G) := by
  intro x hx y hy a b ha hb hab
  have hc : ⇑(D.toLp (a • x + b • y)) =ᵐ[μ] fun ω => a * D.toLp x ω + b * D.toLp y ω := by
    rw [map_add, map_smul, map_smul]
    filter_upwards [Lp.coeFn_add (a • D.toLp x) (b • D.toLp y), Lp.coeFn_smul a (D.toLp x),
      Lp.coeFn_smul b (D.toLp y)] with ω h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  show ∀ᵐ ω ∂μ, ω ∈ G → 1 ≤ D.toLp (a • x + b • y) ω
  filter_upwards [hx, hy, hc] with ω h1 h2 h3 hω
  rw [h3]
  nlinarith [h1 hω, h2 hω]

/-- Almost-everywhere inclusion of sets reverses inclusion of their admissible classes. -/
theorem adm_anti_ae {G₁ G₂ : Set Ω} (h : ∀ᵐ ω ∂μ, ω ∈ G₁ → ω ∈ G₂) : D.adm G₂ ⊆ D.adm G₁ := by
  intro x hx
  show ∀ᵐ ω ∂μ, ω ∈ G₁ → 1 ≤ D.toLp x ω
  filter_upwards [hx, h] with ω h1 h2 hω using h1 (h2 hω)

/-- Inclusion of sets reverses inclusion of their admissible classes. -/
theorem adm_anti {G₁ G₂ : Set Ω} (h : G₁ ⊆ G₂) : D.adm G₂ ⊆ D.adm G₁ :=
  D.adm_anti_ae (Eventually.of_forall fun _ hω => h hω)

/-- The maximum of two admissible elements is admissible on the union. -/
theorem supS_mem_adm_union {G₁ G₂ : Set Ω} {x y : D.Space} (hx : x ∈ D.adm G₁)
    (hy : y ∈ D.adm G₂) : D.supS x y ∈ D.adm (G₁ ∪ G₂) := by
  show ∀ᵐ ω ∂μ, ω ∈ G₁ ∪ G₂ → 1 ≤ D.toLp (D.supS x y) ω
  rw [D.toLp_supS]
  filter_upwards [hx, hy, Lp.coeFn_sup (D.toLp x) (D.toLp y)] with ω h1 h2 h3 hω
  rw [h3, Pi.sup_apply]
  rcases hω with hω | hω
  · exact le_sup_of_le_left (h1 hω)
  · exact le_sup_of_le_right (h2 hω)

/-- The minimum of two admissible elements is admissible on the intersection. -/
theorem infS_mem_adm_inter {G₁ G₂ : Set Ω} {x y : D.Space} (hx : x ∈ D.adm G₁)
    (hy : y ∈ D.adm G₂) : D.infS x y ∈ D.adm (G₁ ∩ G₂) := by
  show ∀ᵐ ω ∂μ, ω ∈ G₁ ∩ G₂ → 1 ≤ D.toLp (D.infS x y) ω
  rw [D.toLp_infS]
  filter_upwards [hx, hy, Lp.coeFn_inf (D.toLp x) (D.toLp y)] with ω h1 h2 h3 hω
  rw [h3, Pi.inf_apply]
  exact le_inf (h1 hω.1) (h2 hω.2)

/--
BH 1991, ch. I § 8.1, definition 8.1.1 (p. 52), extended to every set.

The almost-everywhere capacity of an arbitrary set: inf {‖u‖²_𝔻; u ∈ 𝔻, u ≥ 1 μ-a.e. on G} (= +∞ if
the set is empty). For open G, this is BH's c(G), definition 8.1.1 (see `cap_eq_capAE`).
-/
def capAE (G : Set Ω) : ℝ≥0∞ := ⨅ x ∈ D.adm G, ENNReal.ofReal (‖x‖ ^ 2)

/-- The squared norm of any admissible element bounds the a.e. capacity from above. -/
theorem capAE_le {G : Set Ω} {x : D.Space} (hx : x ∈ D.adm G) :
    D.capAE G ≤ ENNReal.ofReal (‖x‖ ^ 2) := iInf₂_le x hx

/-- The a.e. capacity is monotone under almost-everywhere inclusion. -/
theorem capAE_mono_ae {G₁ G₂ : Set Ω} (h : ∀ᵐ ω ∂μ, ω ∈ G₁ → ω ∈ G₂) :
    D.capAE G₁ ≤ D.capAE G₂ :=
  biInf_mono fun _ hx => D.adm_anti_ae h hx

/-- The a.e. capacity is monotone under set inclusion. -/
theorem capAE_mono {G₁ G₂ : Set Ω} (h : G₁ ⊆ G₂) : D.capAE G₁ ≤ D.capAE G₂ :=
  D.capAE_mono_ae (Eventually.of_forall fun _ hω => h hω)

/-- The a.e. capacity is finite exactly when the admissible class is nonempty. -/
theorem capAE_ne_top_iff {G : Set Ω} : D.capAE G ≠ ⊤ ↔ (D.adm G).Nonempty := by
  constructor
  · intro h
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exact h (by simp [capAE, hne])
  · rintro ⟨x, hx⟩
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (D.capAE_le hx)

open Classical in
/--
BH 1991, ch. I § 8.1, proposition 8.1.2 a) (p. 52): equilibrium potential.

The equilibrium potential e_G: projection of 0 onto the closed convex set `adm G` (0 if it is
empty).
-/
def equilibrium (G : Set Ω) : D.Space :=
  if h : (D.adm G).Nonempty then
    (exists_min_norm h (D.isClosed_adm G) (D.convex_adm G)).choose
  else 0

/--
For a nonempty admissible class, the equilibrium potential is admissible and has minimum norm.
-/
theorem equilibrium_spec {G : Set Ω} (h : (D.adm G).Nonempty) :
    D.equilibrium G ∈ D.adm G ∧ ∀ v ∈ D.adm G, ‖D.equilibrium G‖ ≤ ‖v‖ := by
  rw [equilibrium, dif_pos h]
  exact (exists_min_norm h (D.isClosed_adm G) (D.convex_adm G)).choose_spec

/-- For a nonempty admissible class, the a.e. capacity equals the squared equilibrium norm. -/
theorem capAE_eq_equilibrium {G : Set Ω} (h : (D.adm G).Nonempty) :
    D.capAE G = ENNReal.ofReal (‖D.equilibrium G‖ ^ 2) := by
  obtain ⟨hm, hmin⟩ := D.equilibrium_spec h
  exact le_antisymm (D.capAE_le hm) (le_iInf₂ fun x hx =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hmin x hx) 2))

/-- An admissible element with norm at most the equilibrium norm is the equilibrium potential. -/
theorem eq_equilibrium {G : Set Ω} (h : (D.adm G).Nonempty) {v : D.Space} (hv : v ∈ D.adm G)
    (hle : ‖v‖ ≤ ‖D.equilibrium G‖) : v = D.equilibrium G :=
  eq_of_norm_le_min (D.convex_adm G) (D.equilibrium_spec h).1 hv (D.equilibrium_spec h).2 hle

/--
BH 1991, ch. I § 8.1, proposition 8.1.2 a) (pp. 52–53).

BH proposition 8.1.2 a) (for every set G, not only open sets): if the capacity is finite,
there exists a unique e_G ∈ 𝔻 with e_G ≥ 1 a.e. on G and ‖e_G‖² = c(G); moreover, 0 ≤ e_G ≤ 1 a.e.
-/
theorem bh_8_1_2_a {G : Set Ω} (hG : D.capAE G ≠ ⊤) :
    (∃! e : D.Space, e ∈ D.adm G ∧ ENNReal.ofReal (‖e‖ ^ 2) = D.capAE G) ∧
    ∀ᵐ ω ∂μ, 0 ≤ D.toLp (D.equilibrium G) ω ∧ D.toLp (D.equilibrium G) ω ≤ 1 := by
  have hne := D.capAE_ne_top_iff.1 hG
  obtain ⟨hm, hmin⟩ := D.equilibrium_spec hne
  refine ⟨⟨D.equilibrium G, ⟨hm, (D.capAE_eq_equilibrium hne).symm⟩, ?_⟩, ?_⟩
  · rintro v ⟨hv, hcap⟩
    rw [D.capAE_eq_equilibrium hne, ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)]
      at hcap
    refine D.eq_equilibrium hne hv ?_
    nlinarith [norm_nonneg v, norm_nonneg (D.equilibrium G)]
  · set e := D.equilibrium G with he
    have hmem : D.contract lipschitzWith_unitF unitF_zero e ∈ D.adm G := by
      show ∀ᵐ ω ∂μ, ω ∈ G → 1 ≤ D.toLp (D.contract lipschitzWith_unitF unitF_zero e) ω
      rw [toLp_contract]
      filter_upwards [hm, D.coe_contractLp lipschitzWith_unitF unitF_zero e] with ω h1 h2 hω
      rw [h2, unitF_eq_one (h1 hω)]
    have heq : D.contract lipschitzWith_unitF unitF_zero e = e :=
      D.eq_equilibrium hne hmem (D.norm_contract_le _ _ e)
    have hcoe : D.toLp e = D.contractLp lipschitzWith_unitF unitF_zero e := by
      calc D.toLp e = D.toLp (D.contract lipschitzWith_unitF unitF_zero e) := by rw [heq]
        _ = _ := rfl
    filter_upwards [D.coe_contractLp lipschitzWith_unitF unitF_zero e] with ω h
    rw [hcoe, h]
    exact unitF_mem _

/--
BH 1991, ch. I § 8.1, proposition 8.1.2 b) (statement p. 52, proof p. 53).

BH proposition 8.1.2 b): G₁ ⊆ G₂ with finite capacities ⇒ e_{G₁} ≤ e_{G₂}.
-/
theorem bh_8_1_2_b {G₁ G₂ : Set Ω} (h12 : G₁ ⊆ G₂) (h1 : D.capAE G₁ ≠ ⊤)
    (h2 : D.capAE G₂ ≠ ⊤) : D.toLp (D.equilibrium G₁) ≤ D.toLp (D.equilibrium G₂) := by
  have n1 := D.capAE_ne_top_iff.1 h1
  have n2 := D.capAE_ne_top_iff.1 h2
  obtain ⟨m1, min1⟩ := D.equilibrium_spec n1
  obtain ⟨m2, min2⟩ := D.equilibrium_spec n2
  have hI : D.infS (D.equilibrium G₁) (D.equilibrium G₂) ∈ D.adm G₁ := by
    have h := D.infS_mem_adm_inter m1 m2
    rwa [Set.inter_eq_left.2 h12] at h
  have hS : D.supS (D.equilibrium G₁) (D.equilibrium G₂) ∈ D.adm G₂ := by
    have h := D.supS_mem_adm_union m1 m2
    rwa [Set.union_eq_right.2 h12] at h
  have hl := D.bh_8_1_2_1 (D.equilibrium G₁) (D.equilibrium G₂)
  have hI' : ‖D.equilibrium G₁‖ ^ 2 ≤ ‖D.infS (D.equilibrium G₁) (D.equilibrium G₂)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (min1 _ hI) 2
  have hS' : ‖D.supS (D.equilibrium G₁) (D.equilibrium G₂)‖ ≤ ‖D.equilibrium G₂‖ := by
    nlinarith [norm_nonneg (D.supS (D.equilibrium G₁) (D.equilibrium G₂)),
      norm_nonneg (D.equilibrium G₂)]
  have heq := D.eq_equilibrium n2 hS hS'
  have h := congrArg D.toLp heq
  rw [D.toLp_supS] at h
  exact sup_eq_right.1 h

/--
BH 1991, ch. I § 8.1, proof of proposition 8.1.3 b) (p. 53), for the a.e. capacity.

Strong subadditivity of the a.e. capacity (Lemma 8.1.2.1 applied to the potentials).
-/
theorem capAE_union_add_inter_le (G₁ G₂ : Set Ω) :
    D.capAE (G₁ ∪ G₂) + D.capAE (G₁ ∩ G₂) ≤ D.capAE G₁ + D.capAE G₂ := by
  by_cases h1 : D.capAE G₁ = ⊤
  · rw [h1, top_add]; exact le_top
  by_cases h2 : D.capAE G₂ = ⊤
  · rw [h2, add_top]; exact le_top
  have n1 := D.capAE_ne_top_iff.1 h1
  have n2 := D.capAE_ne_top_iff.1 h2
  have m1 := (D.equilibrium_spec n1).1
  have m2 := (D.equilibrium_spec n2).1
  calc D.capAE (G₁ ∪ G₂) + D.capAE (G₁ ∩ G₂)
      ≤ ENNReal.ofReal (‖D.supS (D.equilibrium G₁) (D.equilibrium G₂)‖ ^ 2) +
        ENNReal.ofReal (‖D.infS (D.equilibrium G₁) (D.equilibrium G₂)‖ ^ 2) :=
        add_le_add (D.capAE_le (D.supS_mem_adm_union m1 m2))
          (D.capAE_le (D.infS_mem_adm_inter m1 m2))
    _ = ENNReal.ofReal (‖D.supS (D.equilibrium G₁) (D.equilibrium G₂)‖ ^ 2 +
        ‖D.infS (D.equilibrium G₁) (D.equilibrium G₂)‖ ^ 2) :=
        (ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)).symm
    _ ≤ ENNReal.ofReal (‖D.equilibrium G₁‖ ^ 2 + ‖D.equilibrium G₂‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (D.bh_8_1_2_1 _ _)
    _ = D.capAE G₁ + D.capAE G₂ := by
        rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), D.capAE_eq_equilibrium n1,
          D.capAE_eq_equilibrium n2]

/--
BH 1991, ch. I § 8.1, proposition 8.1.3 c) on open sets (p. 53); the case c(⋃ Gₙ) = +∞, asserted
without argument by BH, is handled by `exists_tendsto_min_norm`.

Continuity from below of the a.e. capacity along every increasing sequence of sets (projections onto
decreasing convex sets).
-/
theorem capAE_iUnion_of_monotone {G : ℕ → Set Ω} (hG : Monotone G) :
    D.capAE (⋃ n, G n) = ⨆ n, D.capAE (G n) := by
  refine le_antisymm ?_ (iSup_le fun n => D.capAE_mono (Set.subset_iUnion G n))
  by_cases htop : ⨆ n, D.capAE (G n) = ⊤
  · rw [htop]; exact le_top
  have hfin : ∀ n, D.capAE (G n) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top htop (le_iSup (fun n => D.capAE (G n)) n)
  have hne : ∀ n, (D.adm (G n)).Nonempty := fun n => D.capAE_ne_top_iff.1 (hfin n)
  have hbound : ∀ n, ‖D.equilibrium (G n)‖ ^ 2 ≤ (⨆ n, D.capAE (G n)).toReal := fun n => by
    have h := le_iSup (fun n => D.capAE (G n)) n
    rw [D.capAE_eq_equilibrium (hne n)] at h
    exact (ENNReal.ofReal_le_iff_le_toReal htop).1 h
  obtain ⟨e', he', hlim⟩ := exists_tendsto_min_norm (fun n => D.convex_adm (G n))
    (fun n => D.isClosed_adm (G n)) (fun n m hnm => D.adm_anti (hG hnm))
    (fun n => (D.equilibrium_spec (hne n)).1) (fun n => (D.equilibrium_spec (hne n)).2) hbound
  have hmem : e' ∈ D.adm (⋃ n, G n) := by
    have h : ∀ n, e' ∈ D.adm (G n) := Set.mem_iInter.1 he'
    have hall : ∀ᵐ ω ∂μ, ∀ n, ω ∈ G n → 1 ≤ D.toLp e' ω := ae_all_iff.2 h
    show ∀ᵐ ω ∂μ, ω ∈ ⋃ n, G n → 1 ≤ D.toLp e' ω
    filter_upwards [hall] with ω hω hU
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hU
    exact hω n hn
  have htend : Tendsto (fun n => ENNReal.ofReal (‖D.equilibrium (G n)‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (‖e'‖ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (((continuous_norm.tendsto e').comp hlim).pow 2)
  calc D.capAE (⋃ n, G n) ≤ ENNReal.ofReal (‖e'‖ ^ 2) := D.capAE_le hmem
    _ ≤ ⨆ n, D.capAE (G n) := le_of_tendsto' htend fun n => by
        rw [← D.capAE_eq_equilibrium (hne n)]; exact le_iSup (fun n => D.capAE (G n)) n

/--
BH 1991, ch. I § 8.1, proposition 8.1.3 a) (p. 53), a.e. version.

BH proposition 8.1.3 a), a.e. version: μ(G) ≤ c(G) for measurable G.
-/
theorem measure_le_capAE {G : Set Ω} (hG : MeasurableSet G) : μ G ≤ D.capAE G := by
  refine le_iInf₂ fun x hx => ?_
  have hint : Integrable (fun ω => D.toLp x ω ^ 2) μ := (Lp.memLp (D.toLp x)).integrable_sq
  calc μ G = ∫⁻ ω, G.indicator 1 ω ∂μ := (lintegral_indicator_one hG).symm
    _ ≤ ∫⁻ ω, ENNReal.ofReal (D.toLp x ω ^ 2) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hx] with ω hω
        by_cases h : ω ∈ G
        · rw [Set.indicator_of_mem h, Pi.one_apply]
          exact ENNReal.one_le_ofReal.2 (by nlinarith [hω h])
        · rw [Set.indicator_of_notMem h]; exact zero_le
    _ = ENNReal.ofReal (∫ ω, D.toLp x ω ^ 2 ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun ω => sq_nonneg (D.toLp x ω))).symm
    _ = ENNReal.ofReal (‖D.toLp x‖ ^ 2) := by
        simpa only [Real.norm_eq_abs, sq_abs] using
          congrArg ENNReal.ofReal (ErrorCalculus.l2_integral_norm_sq (D.toLp x))
    _ ≤ ENNReal.ofReal (‖x‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (D.norm_toLp_le x) 2)

/-! ### Outer capacity (BH definition 8.1.1) -/
variable [TopologicalSpace Ω]

/--
BH 1991, ch. I § 8.1, definition 8.1.1 (p. 52).

BH definition 8.1.1: c(A) = inf {c(G); G open, G ⊇ A}.
-/
def cap (A : Set Ω) : ℝ≥0∞ := ⨅ G : {G : Set Ω // IsOpen G ∧ A ⊆ G}, D.capAE G.1

/-- The capacity of A is bounded by the a.e. capacity of any open set containing A. -/
theorem cap_le_capAE {A G : Set Ω} (hG : IsOpen G) (hA : A ⊆ G) : D.cap A ≤ D.capAE G :=
  iInf_le (fun G : {G : Set Ω // IsOpen G ∧ A ⊆ G} => D.capAE G.1) ⟨G, hG, hA⟩

/--
BH 1991, ch. I § 8.1, definition 8.1.1 (p. 52): agreement of the two definitions on open sets.

On open sets, outer capacity equals the direct definition.
-/
theorem cap_eq_capAE {G : Set Ω} (hG : IsOpen G) : D.cap G = D.capAE G :=
  le_antisymm (D.cap_le_capAE hG subset_rfl) (le_iInf fun G' => D.capAE_mono G'.2.2)

/-- Outer capacity is monotone under set inclusion. -/
theorem cap_mono {A B : Set Ω} (h : A ⊆ B) : D.cap A ≤ D.cap B :=
  le_iInf fun G => D.cap_le_capAE G.2.1 (h.trans G.2.2)

/-- Every strict upper bound for capacity is attained as a strict bound on an open enlargement. -/
theorem exists_isOpen_capAE_lt {A : Set Ω} {c : ℝ≥0∞} (h : D.cap A < c) :
    ∃ G, IsOpen G ∧ A ⊆ G ∧ D.capAE G < c := by
  obtain ⟨G, hG⟩ := iInf_lt_iff.1 h
  exact ⟨G.1, G.2.1, G.2.2, hG⟩

/-- The empty set has zero capacity. -/
theorem cap_empty : D.cap ∅ = 0 := by
  refine le_antisymm ?_ zero_le
  have h0 : (0 : D.Space) ∈ D.adm ∅ := by
    show ∀ᵐ ω ∂μ, ω ∈ (∅ : Set Ω) → 1 ≤ D.toLp 0 ω
    exact Eventually.of_forall fun ω hω => absurd hω (Set.notMem_empty ω)
  calc D.cap ∅ ≤ D.capAE ∅ := D.cap_le_capAE isOpen_empty subset_rfl
    _ ≤ ENNReal.ofReal (‖(0 : D.Space)‖ ^ 2) := D.capAE_le h0
    _ = 0 := by simp

/--
BH 1991, ch. I § 8.1, proposition 8.1.3 a) (p. 53).

BH proposition 8.1.3 a) (for every A ⊆ Ω): μ(A) ≤ c(A).
-/
theorem bh_8_1_3_a [OpensMeasurableSpace Ω] (A : Set Ω) : μ A ≤ D.cap A :=
  le_iInf fun G => (measure_mono G.2.2).trans (D.measure_le_capAE G.2.1.measurableSet)

/--
BH 1991, ch. I § 8.1, proposition 8.1.3 b) (p. 53).

BH proposition 8.1.3 b): c(A₁ ∪ A₂) + c(A₁ ∩ A₂) ≤ c(A₁) + c(A₂).
-/
theorem bh_8_1_3_b (A₁ A₂ : Set Ω) :
    D.cap (A₁ ∪ A₂) + D.cap (A₁ ∩ A₂) ≤ D.cap A₁ + D.cap A₂ := by
  have hrw : D.cap A₁ + D.cap A₂ = ⨅ G₁ : {G : Set Ω // IsOpen G ∧ A₁ ⊆ G},
      ⨅ G₂ : {G : Set Ω // IsOpen G ∧ A₂ ⊆ G}, (D.capAE G₁.1 + D.capAE G₂.1) := by
    simp only [cap, ENNReal.iInf_add, ENNReal.add_iInf]
    exact iInf_comm
  rw [hrw]
  refine le_iInf₂ fun G₁ G₂ => ?_
  calc D.cap (A₁ ∪ A₂) + D.cap (A₁ ∩ A₂)
      ≤ D.capAE (G₁.1 ∪ G₂.1) + D.capAE (G₁.1 ∩ G₂.1) :=
        add_le_add (D.cap_le_capAE (G₁.2.1.union G₂.2.1) (Set.union_subset_union G₁.2.2 G₂.2.2))
          (D.cap_le_capAE (G₁.2.1.inter G₂.2.1) (Set.inter_subset_inter G₁.2.2 G₂.2.2))
    _ ≤ D.capAE G₁.1 + D.capAE G₂.1 := D.capAE_union_add_inter_le _ _

/-- The capacity of a union is at most the sum of the two capacities. -/
theorem cap_union_le (A₁ A₂ : Set Ω) : D.cap (A₁ ∪ A₂) ≤ D.cap A₁ + D.cap A₂ :=
  le_self_add.trans (D.bh_8_1_3_b A₁ A₂)

/--
BH 1991, ch. I § 8.1, proposition 8.1.3 c) (p. 53).

BH proposition 8.1.3 c): continuity from below, for every increasing sequence of sets.
-/
theorem bh_8_1_3_c {A : ℕ → Set Ω} (hA : Monotone A) :
    D.cap (⋃ n, A n) = ⨆ n, D.cap (A n) := by
  refine le_antisymm ?_ (iSup_le fun n => D.cap_mono (Set.subset_iUnion A n))
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
  have hfin : ∀ n, D.cap (A n) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top hlt.ne (le_iSup (fun n => D.cap (A n)) n)
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.coe_ne_zero.2 hε.ne') ℕ
  have hH : ∀ n, ∃ H, IsOpen H ∧ A n ⊆ H ∧ D.capAE H < D.cap (A n) + δ n := fun n =>
    D.exists_isOpen_capAE_lt (ENNReal.lt_add_right (hfin n)
      (ENNReal.coe_ne_zero.2 (hδpos n).ne'))
  choose H hHo hAH hHcap using hH
  have hGo : ∀ n, IsOpen (Set.accumulate H n) := fun n => by
    unfold Set.accumulate
    exact isOpen_iUnion fun k => isOpen_iUnion fun _ => hHo k
  have hAG : ∀ n, A n ⊆ Set.accumulate H n := fun n =>
    (hAH n).trans (Set.subset_accumulate)
  have hind : ∀ n, D.capAE (Set.accumulate H n) ≤
      D.cap (A n) + ∑ k ∈ Finset.range (n + 1), (δ k : ℝ≥0∞) := by
    intro n
    induction n with
    | zero =>
      rw [Set.accumulate_zero_nat, Finset.sum_range_one]
      exact (hHcap 0).le
    | succ n ih =>
      have hsub := D.capAE_union_add_inter_le (Set.accumulate H n) (H (n + 1))
      have hlow : D.cap (A n) ≤ D.capAE (Set.accumulate H n ∩ H (n + 1)) :=
        D.cap_le_capAE ((hGo n).inter (hHo _))
          (Set.subset_inter (hAG n) ((hA n.le_succ).trans (hAH (n + 1))))
      rw [Set.accumulate_succ, Finset.sum_range_succ]
      refine ENNReal.le_of_add_le_add_left (hfin n) ?_
      calc D.cap (A n) + D.capAE (Set.accumulate H n ∪ H (n + 1))
          ≤ D.capAE (Set.accumulate H n ∪ H (n + 1)) +
            D.capAE (Set.accumulate H n ∩ H (n + 1)) := by
            rw [add_comm]; exact add_le_add le_rfl hlow
        _ ≤ D.capAE (Set.accumulate H n) + D.capAE (H (n + 1)) := hsub
        _ ≤ (D.cap (A n) + ∑ k ∈ Finset.range (n + 1), (δ k : ℝ≥0∞)) +
            (D.cap (A (n + 1)) + δ (n + 1)) := add_le_add ih (hHcap (n + 1)).le
        _ = D.cap (A n) + (D.cap (A (n + 1)) +
            (∑ k ∈ Finset.range (n + 1), (δ k : ℝ≥0∞) + δ (n + 1))) := by ring
  have hU : ⋃ n, A n ⊆ ⋃ n, Set.accumulate H n :=
    Set.iUnion_mono fun n => hAG n
  calc D.cap (⋃ n, A n) ≤ D.capAE (⋃ n, Set.accumulate H n) :=
        D.cap_le_capAE (isOpen_iUnion hGo) hU
    _ = ⨆ n, D.capAE (Set.accumulate H n) :=
        D.capAE_iUnion_of_monotone Set.monotone_accumulate
    _ ≤ ⨆ n, (D.cap (A n) + ε) := iSup_mono fun n =>
        (hind n).trans (add_le_add le_rfl ((ENNReal.sum_le_tsum _).trans hδsum.le))
    _ ≤ (⨆ n, D.cap (A n)) + ε := iSup_le fun n =>
        add_le_add (le_iSup (fun n => D.cap (A n)) n) le_rfl

/--
BH 1991, ch. I § 8.1, proposition 8.1.3 d) (p. 53).

BH proposition 8.1.3 d): countable subadditivity.
-/
theorem bh_8_1_3_d (A : ℕ → Set Ω) : D.cap (⋃ n, A n) ≤ ∑' n, D.cap (A n) := by
  have hU : ⋃ n, A n = ⋃ n, Set.accumulate A n := Set.iUnion_accumulate.symm
  rw [hU, D.bh_8_1_3_c Set.monotone_accumulate]
  refine iSup_le fun n => ?_
  have h : ∀ n, D.cap (Set.accumulate A n) ≤ ∑ k ∈ Finset.range (n + 1), D.cap (A k) := by
    intro n
    induction n with
    | zero => rw [Set.accumulate_zero_nat, Finset.sum_range_one]
    | succ n ih =>
      rw [Set.accumulate_succ, Finset.sum_range_succ]
      exact (D.cap_union_le _ _).trans (add_le_add ih le_rfl)
  exact (h n).trans (ENNReal.sum_le_tsum _)

/--
BH 1991, ch. I § 8.1, definition 8.1.4 (p. 53): "quasi-everywhere".

Capacity as an outer measure: "quasi-everywhere" is the `ae` filter of this outer measure (BH
definition 8.1.4).
-/
def capOuter : OuterMeasure Ω where
  measureOf := D.cap
  empty := D.cap_empty
  mono := fun h => D.cap_mono h
  iUnion_nat := fun A _ => D.bh_8_1_3_d A

/-- The capacity outer measure evaluates to the outer capacity of each set. -/
theorem capOuter_apply (A : Set Ω) : D.capOuter A = D.cap A := rfl

/--
BH 1991, ch. I § 8.1, definition 8.1.4 (p. 53).

BH definition 8.1.4: a polar set.
-/
def IsPolar (A : Set Ω) : Prop := D.cap A = 0

/--
BH 1991, ch. I § 8.1, remark 8.1.4.1 (p. 54); reuse of `measure_iUnion_null` for the outer measure
`capOuter` (an adaptation, not a new result).

BH remark 8.1.4.1: a countable union of polar sets is polar.
-/
theorem isPolar_iUnion {A : ℕ → Set Ω} (h : ∀ n, D.IsPolar (A n)) : D.IsPolar (⋃ n, A n) :=
  measure_iUnion_null (μ := D.capOuter) h

/--
consequence of BH 1991, ch. I § 8.1, proposition 8.1.3 a) (p. 53).

A polar set is μ-null (BH 8.1.3 a)).
-/
theorem measure_eq_zero_of_isPolar [OpensMeasurableSpace Ω] {A : Set Ω} (h : D.IsPolar A) :
    μ A = 0 :=
  le_antisymm ((D.bh_8_1_3_a A).trans (le_of_eq h)) zero_le

/--
consequence of BH 1991, ch. I § 8.1, proposition 8.1.3 a) (p. 53).

Quasi-everywhere ⇒ μ-almost everywhere.
-/
theorem ae_of_qe [OpensMeasurableSpace Ω] {p : Ω → Prop} (h : ∀ᵐ ω ∂D.capOuter, p ω) :
    ∀ᵐ ω ∂μ, p ω := by
  rw [ae_iff] at h ⊢
  exact D.measure_eq_zero_of_isPolar h

/--
Fukushima 1980, § 3.1, Theorem 3.1.1 (iii) (p. 63): continuity from above on compact sets, for
Hausdorff Ω, without finiteness of capacities or regularity of the form; capacitability is not
established.

Fukushima 1980, Theorem 3.1.1 (iii): continuity from above on compact sets; together with `cap_mono`
and `bh_8_1_3_c`, this makes c a Choquet capacity (for Hausdorff Ω).
-/
theorem cap_iInter_of_isCompact [T2Space Ω] {K : ℕ → Set Ω} (hK : ∀ n, IsCompact (K n))
    (hanti : Antitone K) : D.cap (⋂ n, K n) = ⨅ n, D.cap (K n) := by
  refine le_antisymm (le_iInf fun n => D.cap_mono (Set.iInter_subset _ n)) ?_
  refine le_iInf fun G => ?_
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact' hanti.directed_ge hK
    (fun n => (hK n).isClosed) (fun x hx => G.2.1.mem_nhds (G.2.2 hx))
  exact (iInf_le _ n).trans (D.cap_le_capAE G.2.1 hn)

end DirichletForm
end ErrorCalculus.Capacity
