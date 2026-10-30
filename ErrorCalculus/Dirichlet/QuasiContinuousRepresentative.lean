import ErrorCalculus.Dirichlet.QuasiContinuity
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# quasi-continuous representatives, quasi-uniform convergence (BH 1991, ch. I § 8.2–8.3, pp. 54–56;
Fukushima 1980, th. 3.1.3–3.1.4, pp. 65–67)

## Main results
Common core: if ‖xₙ − y‖_𝔻 ≤ 4⁻ⁿ and fₙ is a quasi-continuous representative of xₙ, the pointwise
limit `qlim f` is attained quasi-uniformly, is quasi-continuous and represents y. Consequences:
existence of a quasi-continuous representative under the density part of (D) (prop. 8.2.1),
quasi-uniform convergence (def. 8.2.3), prop. 8.2.5, cor. 8.2.6, Cauchy sequences (Fukushima th.
3.1.4 (i)) and c-indistinguishability (prop. 8.3.3). Scope: `fukushima_3_1_4` is proved for ORDINARY
quasi-continuity and without regularity; Fukushima's restricted sense (Alexandrov compactification)
is not treated here. The predicate `RegularCore` is only the density-in-𝔻 component of Fukushima
regularity. The objects `badSet`, `tailBad`, `qlim` and the geometric bounds are tools.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity
namespace DirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] {μ : Measure Ω}
variable (D : DirichletForm μ)

/-! ## E. Quasi-continuous representatives, quasi-uniform convergence (BH 8.2) -/

/-- The bad set at index n: |f_{n+1} - f_n| > 2^{-n}. -/
def badSet (f : ℕ → Ω → ℝ) (n : ℕ) : Set Ω := {ω | (1 / 2 : ℝ) ^ n < |f (n + 1) ω - f n ω|}

/-- Union of the bad sets from index p onward (the set Ω_p of BH 8.2.1). -/
def tailBad (f : ℕ → Ω → ℝ) (p : ℕ) : Set Ω := ⋃ k, badSet f (k + p)

/-- Pointwise limit (an arbitrary value where it does not exist). -/
def qlim (f : ℕ → Ω → ℝ) : Ω → ℝ := fun ω => limUnder atTop fun n => f n ω

omit [MeasurableSpace Ω] [TopologicalSpace Ω] in
/--
Outside `tailBad f p`, the sequence converges to `qlim f` with error at k + p at most 2·2⁻⁽ᵏ⁺ᵖ⁾.
-/
theorem tendsto_qlim_of_notMem {f : ℕ → Ω → ℝ} {p : ℕ} {ω : Ω} (hω : ω ∉ tailBad f p) :
    Tendsto (fun n => f n ω) atTop (𝓝 (qlim f ω)) ∧
      ∀ k, dist (f (k + p) ω) (qlim f ω) ≤ 2 * (1 / 2 : ℝ) ^ (k + p) := by
  have hb : ∀ k, |f (k + p + 1) ω - f (k + p) ω| ≤ (1 / 2 : ℝ) ^ (k + p) := by
    intro k
    have h : ω ∉ badSet f (k + p) := fun h => hω (Set.mem_iUnion.2 ⟨k, h⟩)
    simpa [badSet] using h
  have hv : ∀ k, dist (f (k + p) ω) (f (k + 1 + p) ω) ≤ 2 * (1 / 2 : ℝ) ^ p / 2 / 2 ^ k := by
    intro k
    have e1 : k + 1 + p = k + p + 1 := by omega
    have h2 : (1 / 2 : ℝ) ^ (k + p) = 2 * (1 / 2 : ℝ) ^ p / 2 / 2 ^ k := by
      rw [pow_add, one_div_pow (2 : ℝ) k]; field_simp
    rw [e1, Real.dist_eq, abs_sub_comm, ← h2]
    exact hb k
  have hcauchy : CauchySeq fun k => f (k + p) ω := cauchySeq_of_le_geometric_two hv
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hf : Tendsto (fun n => f n ω) atTop (𝓝 a) :=
    (tendsto_add_atTop_iff_nat (f := fun n => f n ω) p).1 ha
  have hq : qlim f ω = a := tendsto_nhds_unique (tendsto_nhds_limUnder ⟨a, hf⟩) hf
  refine ⟨by rw [hq]; exact hf, fun k => ?_⟩
  have h := dist_le_of_le_geometric_two_of_tendsto hv ha k
  rw [hq]
  calc dist (f (k + p) ω) a ≤ 2 * (1 / 2 : ℝ) ^ p / 2 ^ k := h
    _ = 2 * (1 / 2 : ℝ) ^ (k + p) := by rw [pow_add, one_div_pow (2 : ℝ) k]; field_simp

omit [MeasurableSpace Ω] [TopologicalSpace Ω] in
/-- The sequence converges uniformly to `qlim f` on the complement of `tailBad f p`. -/
theorem tendstoUniformlyOn_qlim (f : ℕ → Ω → ℝ) (p : ℕ) :
    TendstoUniformlyOn f (qlim f) atTop (tailBad f p)ᶜ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h0 : Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 2
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h0.eventually (gt_mem_nhds hε))
  refine eventually_atTop.2 ⟨N + p, fun n hn ω hω => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + p := ⟨n - p, by omega⟩
  rw [dist_comm]
  exact lt_of_le_of_lt ((tendsto_qlim_of_notMem hω).2 k) (hN (k + p) (by omega))

/-- The geometric tail with terms 4·(1/4)^(k + p) is summable. -/
theorem summable_geom_tail (p : ℕ) : Summable fun k : ℕ => 4 * (1 / 4 : ℝ) ^ (k + p) :=
  ((summable_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (4 * (1 / 4 : ℝ) ^ p)).congr fun k => by rw [pow_add]; ring

/-- The sum of 4·(1/4)^(k + p) over k is (16/3)·(1/4)^p. -/
theorem tsum_geom_tail (p : ℕ) :
    ∑' k : ℕ, 4 * (1 / 4 : ℝ) ^ (k + p) = 16 / 3 * (1 / 4 : ℝ) ^ p := by
  have h : ∀ k : ℕ, 4 * (1 / 4 : ℝ) ^ (k + p) = (4 * (1 / 4 : ℝ) ^ p) * (1 / 4 : ℝ) ^ k :=
    fun k => by rw [pow_add]; ring
  rw [tsum_congr h, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  ring

/-- The nonnegative extended-real bounds (16/3)·(1/4)^p tend to zero. -/
theorem tendsto_bound :
    Tendsto (fun p : ℕ => ENNReal.ofReal (16 / 3 * (1 / 4 : ℝ) ^ p)) atTop (𝓝 0) := by
  have h : Tendsto (fun p : ℕ => 16 / 3 * (1 / 4 : ℝ) ^ p) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).const_mul (16 / 3)
  have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h
  rw [ENNReal.ofReal_zero] at h2
  exact h2

/--
BH 1991, ch. I § 8.2, definition 8.2.3 (p. 55).

BH definition 8.2.3: quasi-uniform convergence.
-/
def TendstoQuasiUniformly (F : ℕ → Ω → ℝ) (g : Ω → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ G, IsOpen G ∧ D.cap G < ε ∧ TendstoUniformlyOn F g atTop Gᶜ

section Core
variable {x : ℕ → D.Space} {y : D.Space} (hxy : ∀ n, ‖x n - y‖ ≤ (1 / 4 : ℝ) ^ n)
  {f : ℕ → Ω → ℝ} (hf : ∀ n, D.QuasiContinuous (f n))
  (hfx : ∀ n, ⇑(D.toLp (x n)) =ᵐ[μ] f n)
include hxy hf hfx

/--
Under the continuous representative and increment bounds, the n-th bad set has capacity ≤ 4·(1/4)^n.
-/
theorem cap_badSet_le (n : ℕ) : D.cap (badSet f n) ≤ ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ n) := by
  have hrep : ⇑(D.toLp (x (n + 1) - x n)) =ᵐ[μ] f (n + 1) - f n := by
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (D.toLp (x (n + 1))) (D.toLp (x n)), hfx (n + 1), hfx n]
      with ω h1 h2 h3
    rw [h1, Pi.sub_apply, Pi.sub_apply, h2, h3]
  have h := D.bh_8_2_2_lt (x (n + 1) - x n) (D.quasiContinuous_sub (hf (n + 1)) (hf n)) hrep
    (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hd : ‖x (n + 1) - x n‖ ≤ 2 * (1 / 4 : ℝ) ^ n := by
    have e : x (n + 1) - x n = (x (n + 1) - y) - (x n - y) := by abel
    rw [e]
    calc _ ≤ ‖x (n + 1) - y‖ + ‖x n - y‖ := norm_sub_le _ _
      _ ≤ (1 / 4 : ℝ) ^ (n + 1) + (1 / 4 : ℝ) ^ n := add_le_add (hxy _) (hxy _)
      _ ≤ 2 * (1 / 4 : ℝ) ^ n := by
          rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 4) n]
  have hq : ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 4 : ℝ) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hq, div_le_iff₀ (pow_pos (by norm_num) n)]
  have hsq : ‖x (n + 1) - x n‖ ^ 2 ≤ (2 * (1 / 4 : ℝ) ^ n) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hd 2
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 4) n]

/--
Under the continuous representative and increment bounds, the p-th tail has capacity ≤
(16/3)·(1/4)^p.
-/
theorem cap_tailBad_le (p : ℕ) :
    D.cap (tailBad f p) ≤ ENNReal.ofReal (16 / 3 * (1 / 4 : ℝ) ^ p) :=
  calc D.cap (tailBad f p) ≤ ∑' k, D.cap (badSet f (k + p)) := D.bh_8_1_3_d _
    _ ≤ ∑' k, ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ (k + p)) :=
        ENNReal.tsum_le_tsum fun k => D.cap_badSet_le hxy hf hfx _
    _ = ENNReal.ofReal (∑' k, 4 * (1 / 4 : ℝ) ^ (k + p)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (summable_geom_tail p)).symm
    _ = ENNReal.ofReal (16 / 3 * (1 / 4 : ℝ) ^ p) := by rw [tsum_geom_tail]

/--
Under the representative and increment assumptions, convergence is uniform outside an open set of
arbitrarily small positive capacity bound.
-/
theorem exists_isOpen_tendstoUniformlyOn {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ O, IsOpen O ∧ D.cap O < ε ∧ TendstoUniformlyOn f (qlim f) atTop Oᶜ := by
  obtain ⟨p, hp⟩ := (tendsto_bound.eventually (gt_mem_nhds hε)).exists
  have hlt : D.cap (tailBad f p) < ε := lt_of_le_of_lt (D.cap_tailBad_le hxy hf hfx p) hp
  obtain ⟨O, hOo, hsub, hO⟩ := D.exists_isOpen_capAE_lt hlt
  exact ⟨O, hOo, by rwa [D.cap_eq_capAE hOo],
    (tendstoUniformlyOn_qlim f p).mono (Set.compl_subset_compl.2 hsub)⟩

/--
Under the representative and increment assumptions, the sequence converges quasi-uniformly to its
chosen limit.
-/
theorem tendstoQuasiUniformly_qlim : D.TendstoQuasiUniformly f (qlim f) :=
  fun _ hε => D.exists_isOpen_tendstoUniformlyOn hxy hf hfx hε

/--
Under the continuous representative and increment assumptions, the chosen limit is quasi-continuous.
-/
theorem quasiContinuous_qlim : D.QuasiContinuous (qlim f) := by
  intro ε hε
  obtain ⟨O, hOo, hOc, hOu⟩ :=
    D.exists_isOpen_tendstoUniformlyOn hxy hf hfx (ENNReal.half_pos hε.ne')
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.half_pos hε.ne').ne' ℕ
  have hH : ∀ n, ∃ H, IsOpen H ∧ D.cap H < δ n ∧ ContinuousOn (f n) Hᶜ := fun n =>
    hf n (δ n) (ENNReal.coe_pos.2 (hδpos n))
  choose H hHo hHc hHf using hH
  refine ⟨O ∪ ⋃ n, H n, hOo.union (isOpen_iUnion hHo), ?_, ?_⟩
  · calc D.cap (O ∪ ⋃ n, H n) ≤ D.cap O + D.cap (⋃ n, H n) := D.cap_union_le _ _
      _ ≤ D.cap O + ∑' n, (δ n : ℝ≥0∞) :=
          add_le_add le_rfl ((D.bh_8_1_3_d H).trans (ENNReal.tsum_le_tsum fun n => (hHc n).le))
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hOc hδsum
      _ = ε := ENNReal.add_halves ε
  · have hsubO : (O ∪ ⋃ n, H n)ᶜ ⊆ Oᶜ := Set.compl_subset_compl.2 Set.subset_union_left
    refine (hOu.mono hsubO).continuousOn (Frequently.of_forall fun n => (hHf n).mono ?_)
    exact Set.compl_subset_compl.2 ((Set.subset_iUnion H n).trans Set.subset_union_right)

/--
BH 1991, ch. I § 8.2, proof of proposition 8.2.1 (pp. 54–55) and Fukushima 1980, § 3.1, proof of
Theorem 3.1.3 (pp. 65–66): the a.e. identification of the limit, left implicit in both sources, is
proved here.
-/
theorem ae_eq_qlim [OpensMeasurableSpace Ω] : ⇑(D.toLp y) =ᵐ[μ] qlim f := by
  have hlim : Tendsto x atTop (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hxy
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  obtain ⟨ns, hns, h1⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((D.toLp.continuous.tendsto y).comp hlim)).exists_seq_tendsto_ae
  have hall : ∀ᵐ ω ∂μ, ∀ n, D.toLp (x n) ω = f n ω := ae_all_iff.2 hfx
  have hpolar : D.IsPolar (⋂ p, tailBad f p) := by
    refine le_antisymm (ge_of_tendsto tendsto_bound (Eventually.of_forall fun p => ?_)) zero_le
    exact (D.cap_mono (Set.iInter_subset _ p)).trans (D.cap_tailBad_le hxy hf hfx p)
  have hnull : ∀ᵐ ω ∂μ, ω ∉ ⋂ p, tailBad f p :=
    measure_eq_zero_iff_ae_notMem.1 (D.measure_eq_zero_of_isPolar hpolar)
  filter_upwards [h1, hall, hnull] with ω ha hb hc
  obtain ⟨p, hp⟩ : ∃ p, ω ∉ tailBad f p := by
    by_contra hcon
    exact hc (Set.mem_iInter.2 fun p => by_contra fun h' => hcon ⟨p, h'⟩)
  have h4 := ((tendsto_qlim_of_notMem hp).1).comp hns.tendsto_atTop
  have h5 : Tendsto (fun i => f (ns i) ω) atTop (𝓝 (D.toLp y ω)) :=
    ha.congr fun i => hb (ns i)
  exact tendsto_nhds_unique h5 h4

end Core

omit [TopologicalSpace Ω] in
/--
A sequence converging in the form norm has a strictly increasing subsequence with error at k
bounded by (1/4)^k.
-/
theorem exists_extraction {x : ℕ → D.Space} {y : D.Space} (hxy : Tendsto x atTop (𝓝 y)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ k, ‖x (ns k) - y‖ ≤ (1 / 4 : ℝ) ^ k := by
  have h0 := tendsto_iff_norm_sub_tendsto_zero.1 hxy
  exact extraction_forall_of_eventually (P := fun k n => ‖x n - y‖ ≤ (1 / 4 : ℝ) ^ k)
    fun k => ((tendsto_order.1 h0).2 _ (pow_pos (by norm_num) k)).mono fun n hn => hn.le

/--
BH 1991, ch. I § 8.2, hypothesis (D) (p. 54), the density part alone; (T) is the
`OpensMeasurableSpace` instance in `bh_8_2_1`.

The density part of BH hypothesis (D); (T) is supplied separately by `OpensMeasurableSpace` in
`bh_8_2_1`.
-/
def DensityHyp : Prop :=
  Dense {x : D.Space | ∃ φ : Ω → ℝ, Continuous φ ∧ ⇑(D.toLp x) =ᵐ[μ] φ}

/--
BH 1991, ch. I § 8.2, proposition 8.2.1, existence under (D) (pp. 54–55).

BH proposition 8.2.1 (existence): under (D), every x ∈ 𝔻 has a quasi-continuous representative.
-/
theorem bh_8_2_1 [OpensMeasurableSpace Ω] (hD : D.DensityHyp) (x : D.Space) :
    ∃ f : Ω → ℝ, D.QuasiContinuous f ∧ ⇑(D.toLp x) =ᵐ[μ] f := by
  have h : ∀ n : ℕ, ∃ z ∈ {w : D.Space | ∃ φ : Ω → ℝ, Continuous φ ∧ ⇑(D.toLp w) =ᵐ[μ] φ},
      dist x z < (1 / 4 : ℝ) ^ n := fun n => hD.exists_dist_lt x (pow_pos (by norm_num) n)
  choose z hz hzd using h
  have hz' : ∀ n, ∃ φ : Ω → ℝ, Continuous φ ∧ ⇑(D.toLp (z n)) =ᵐ[μ] φ := hz
  choose φ hφc hφ using hz'
  have hxy : ∀ n, ‖z n - x‖ ≤ (1 / 4 : ℝ) ^ n := fun n => by
    rw [← dist_eq_norm, dist_comm]; exact (hzd n).le
  have hq : ∀ n, D.QuasiContinuous (φ n) := fun n => D.quasiContinuous_of_continuous (hφc n)
  exact ⟨qlim φ, D.quasiContinuous_qlim hxy hq hφ, D.ae_eq_qlim hxy hq hφ⟩

/-- Changing the limit on a capacity-null set preserves quasi-uniform convergence. -/
theorem tendstoQuasiUniformly_congr {F : ℕ → Ω → ℝ} {g₁ g₂ : Ω → ℝ}
    (hT : D.TendstoQuasiUniformly F g₁) (h : g₁ =ᵐ[D.capOuter] g₂) :
    D.TendstoQuasiUniformly F g₂ := by
  intro ε hε
  obtain ⟨G, hGo, hGc, hGu⟩ := hT (ε / 2) (ENNReal.half_pos hε.ne')
  have hN : D.cap {ω | ¬g₁ ω = g₂ ω} < ε / 2 := by
    have h0 : D.capOuter {ω | ¬g₁ ω = g₂ ω} = 0 := ae_iff.1 h
    rw [capOuter_apply] at h0
    rw [h0]; exact ENNReal.half_pos hε.ne'
  obtain ⟨O, hOo, hNO, hOc⟩ := D.exists_isOpen_capAE_lt hN
  refine ⟨G ∪ O, hGo.union hOo, ?_, ?_⟩
  · calc D.cap (G ∪ O) ≤ D.cap G + D.cap O := D.cap_union_le _ _
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hGc (by rwa [D.cap_eq_capAE hOo])
      _ = ε := ENNReal.add_halves ε
  · refine (hGu.mono (Set.compl_subset_compl.2 Set.subset_union_left)).congr_right ?_
    intro ω hω
    by_contra hne
    exact hω (Or.inr (hNO hne))

/-- Quasi-uniform convergence implies quasi-everywhere convergence. -/
theorem tendsto_qe_of_tendstoQuasiUniformly {F : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hT : D.TendstoQuasiUniformly F g) :
    ∀ᵐ ω ∂D.capOuter, Tendsto (fun n => F n ω) atTop (𝓝 (g ω)) := by
  rw [ae_iff, capOuter_apply]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  obtain ⟨G, hGo, hGc, hGu⟩ := hT ε (ENNReal.coe_pos.2 hε)
  have hsub : {ω | ¬Tendsto (fun n => F n ω) atTop (𝓝 (g ω))} ⊆ G := by
    intro ω hω
    by_contra hG
    exact hω (hGu.tendsto_at hG)
  rw [zero_add]
  exact (D.cap_mono hsub).trans hGc.le

/--
BH 1991, ch. I § 8.2, proposition 8.2.5 (pp. 55–56); geometric weights in place of BH's k⁻¹, k⁻²
(indexing understood as k ≥ 1).

BH proposition 8.2.5: if xₙ → x in 𝔻, a subsequence of the quasi-continuous representatives
converges quasi-uniformly to the quasi-continuous representative of x.
-/
theorem bh_8_2_5 [OpensMeasurableSpace Ω] {x : ℕ → D.Space} {y : D.Space}
    (hxy : Tendsto x atTop (𝓝 y)) {f : ℕ → Ω → ℝ} (hf : ∀ n, D.QuasiContinuous (f n))
    (hfx : ∀ n, ⇑(D.toLp (x n)) =ᵐ[μ] f n) {g : Ω → ℝ} (hg : D.QuasiContinuous g)
    (hgy : ⇑(D.toLp y) =ᵐ[μ] g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ D.TendstoQuasiUniformly (fun k => f (ns k)) g := by
  obtain ⟨ns, hns, hb⟩ := D.exists_extraction hxy
  have hf' : ∀ k, D.QuasiContinuous (f (ns k)) := fun k => hf (ns k)
  have hfx' : ∀ k, ⇑(D.toLp (x (ns k))) =ᵐ[μ] f (ns k) := fun k => hfx (ns k)
  refine ⟨ns, hns, D.tendstoQuasiUniformly_congr (D.tendstoQuasiUniformly_qlim hb hf' hfx') ?_⟩
  exact D.bh_8_2_1_unique (D.quasiContinuous_qlim hb hf' hfx') hg
    ((D.ae_eq_qlim hb hf' hfx').symm.trans hgy)

/--
BH 1991, ch. I § 8.2, corollary 8.2.6 (p. 56), without proof in BH.

BH corollary 8.2.6: if xₙ → x in 𝔻 and the quasi-continuous representatives converge
quasi-everywhere to h, then h is equal quasi-everywhere to the quasi-continuous representative of x.
-/
theorem bh_8_2_6 [OpensMeasurableSpace Ω] {x : ℕ → D.Space} {y : D.Space}
    (hxy : Tendsto x atTop (𝓝 y)) {f : ℕ → Ω → ℝ} (hf : ∀ n, D.QuasiContinuous (f n))
    (hfx : ∀ n, ⇑(D.toLp (x n)) =ᵐ[μ] f n) {g : Ω → ℝ} (hg : D.QuasiContinuous g)
    (hgy : ⇑(D.toLp y) =ᵐ[μ] g) {h : Ω → ℝ}
    (hh : ∀ᵐ ω ∂D.capOuter, Tendsto (fun n => f n ω) atTop (𝓝 (h ω))) :
    h =ᵐ[D.capOuter] g := by
  obtain ⟨ns, hns, hT⟩ := D.bh_8_2_5 hxy hf hfx hg hgy
  filter_upwards [hh, D.tendsto_qe_of_tendstoQuasiUniformly hT] with ω h1 h2
  exact tendsto_nhds_unique (h1.comp hns.tendsto_atTop) h2

/--
Fukushima 1980, § 3.1, Theorem 3.1.4 (i) (pp. 66–67), for ORDINARY quasi-continuity (BH 8.1.5) and
without regularity; the book's restricted sense (Alexandrov compactification) is not treated here.

Version of the mechanism of Fukushima 1980, Theorem 3.1.4 (i), for ordinary quasi-continuity,
without a regularity assumption. The book uses quasi-continuity in the restricted sense: every
Cauchy sequence in 𝔻 whose terms have quasi-continuous representatives has a limit y, and a
subsequence of the representatives converges quasi-uniformly to a quasi-continuous function
representing y.
-/
theorem fukushima_3_1_4 [OpensMeasurableSpace Ω] {x : ℕ → D.Space} (hc : CauchySeq x)
    {f : ℕ → Ω → ℝ} (hf : ∀ n, D.QuasiContinuous (f n))
    (hfx : ∀ n, ⇑(D.toLp (x n)) =ᵐ[μ] f n) :
    ∃ y : D.Space, Tendsto x atTop (𝓝 y) ∧ ∃ g : Ω → ℝ, D.QuasiContinuous g ∧
      ⇑(D.toLp y) =ᵐ[μ] g ∧ ∃ ns : ℕ → ℕ, StrictMono ns ∧
        D.TendstoQuasiUniformly (fun k => f (ns k)) g := by
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  obtain ⟨ns, hns, hb⟩ := D.exists_extraction hy
  have hf' : ∀ k, D.QuasiContinuous (f (ns k)) := fun k => hf (ns k)
  have hfx' : ∀ k, ⇑(D.toLp (x (ns k))) =ᵐ[μ] f (ns k) := fun k => hfx (ns k)
  exact ⟨y, hy, qlim fun k => f (ns k), D.quasiContinuous_qlim hb hf' hfx',
    D.ae_eq_qlim hb hf' hfx', ns, hns, D.tendstoQuasiUniformly_qlim hb hf' hfx'⟩

/--
Fukushima 1980, § 3.1 (p. 61), regularity of the form: ONLY the density-in-𝔻 component; uniform
density in C₀ is not included.

Regularity in Fukushima's sense (the density-in-𝔻 part): elements of 𝔻 admitting a continuous,
compactly supported representative are dense.
-/
def RegularCore : Prop :=
  Dense {x : D.Space | ∃ φ : Ω → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ ⇑(D.toLp x) =ᵐ[μ] φ}

/-- A regular core implies density of elements with continuous representatives in the form space. -/
theorem densityHyp_of_regularCore (h : D.RegularCore) : D.DensityHyp :=
  h.mono fun _ hx => by
    obtain ⟨φ, hc, _, he⟩ := hx
    exact ⟨φ, hc, he⟩

/--
BH 1991, ch. I § 8.3, definition 8.3.1 and proposition 8.3.3 (p. 56); BH's reference to "8.1.5" is
read as 8.1.6 (via `bh_8_2_1_unique`).

BH definition 8.3.1 and proposition 8.3.3: two families continuous in λ (separable), equal
μ-a.e. for each λ and quasi-continuous, are c-indistinguishable.
-/
theorem bh_8_3_3 {Λ : Type*} [TopologicalSpace Λ] [TopologicalSpace.SeparableSpace Λ]
    {u v : Λ → Ω → ℝ} (hu : ∀ ω, Continuous fun l => u l ω) (hv : ∀ ω, Continuous fun l => v l ω)
    (hae : ∀ l, u l =ᵐ[μ] v l) (hqu : ∀ l, D.QuasiContinuous (u l))
    (hqv : ∀ l, D.QuasiContinuous (v l)) : ∀ᵐ ω ∂D.capOuter, ∀ l, u l ω = v l ω := by
  obtain ⟨T, hTc, hTd⟩ := TopologicalSpace.exists_countable_dense Λ
  haveI := hTc.to_subtype
  have h : ∀ᵐ ω ∂D.capOuter, ∀ t : T, u t ω = v t ω :=
    ae_all_iff.2 fun t => D.bh_8_2_1_unique (hqu t) (hqv t) (hae t)
  filter_upwards [h] with ω hω l
  have he := Continuous.ext_on hTd (hu ω) (hv ω) (fun t ht => hω ⟨t, ht⟩)
  exact congrFun he l

end DirichletForm
end ErrorCalculus.Capacity
