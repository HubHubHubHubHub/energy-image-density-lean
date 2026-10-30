import ErrorCalculus.Dirichlet.Capacity
import Mathlib.Tactic

/-!
# quasi-continuity and the capacity inequality (BH 1991, ch. I § 8.1–8.2, pp. 54–55)

## Main results
Definition 8.1.5 (quasi-continuity in BH's sense: continuity of the restriction to the complement of
an open set of small capacity), proposition 8.1.6 (nonnegativity a.e. on an open set ⇒ q.e.), q.e.
uniqueness of quasi-continuous representatives (8.2.1, second half), capacity inequality 8.2.2 in
both forms (strict, from BH's proof; non-strict, from its statement) and Fukushima's (3.1.10) for a
continuous representative. The lemmas `smul_absS_mem_adm`, `norm_smul_absS_sq_le`, `capAE_lt_abs_le`
are proof tools, not new results.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity
namespace DirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] {μ : Measure Ω}
variable (D : DirichletForm μ)

/-! ## D. Quasi-continuity (BH 8.1.5, 8.1.6) and the capacity inequality (BH 8.2.2) -/

/--
BH 1991, ch. I § 8.1, definition 8.1.5 (p. 54).

BH definition 8.1.5: for every ε > 0, there exists an open set G with c(G) < ε such that the
restriction of f to Gᶜ is continuous.
-/
def QuasiContinuous (f : Ω → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ G, IsOpen G ∧ D.cap G < ε ∧ ContinuousOn f Gᶜ

/-- Every continuous real function is quasi-continuous. -/
theorem quasiContinuous_of_continuous {f : Ω → ℝ} (hf : Continuous f) : D.QuasiContinuous f :=
  fun _ hε => ⟨∅, isOpen_empty, by rw [D.cap_empty]; exact hε, hf.continuousOn⟩

/-- The difference of two quasi-continuous functions is quasi-continuous. -/
theorem quasiContinuous_sub {f g : Ω → ℝ} (hf : D.QuasiContinuous f)
    (hg : D.QuasiContinuous g) : D.QuasiContinuous (f - g) := by
  intro ε hε
  obtain ⟨G₁, h1o, h1c, h1f⟩ := hf (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨G₂, h2o, h2c, h2f⟩ := hg (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨G₁ ∪ G₂, h1o.union h2o, ?_, ?_⟩
  · calc D.cap (G₁ ∪ G₂) ≤ D.cap G₁ + D.cap G₂ := D.cap_union_le _ _
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add h1c h2c
      _ = ε := ENNReal.add_halves ε
  · exact (h1f.mono (Set.compl_subset_compl.2 Set.subset_union_left)).sub
      (h2f.mono (Set.compl_subset_compl.2 Set.subset_union_right))

/--
BH 1991, ch. I § 8.1, proposition 8.1.6 and its proof (p. 54); "N ∩ Gᶜ open in Gᶜ" is understood
relative to Gᶜ.

BH proposition 8.1.6: f quasi-continuous, V open, f ≥ 0 μ-a.e. on V ⇒ f ≥ 0 q.e. on V.
-/
theorem bh_8_1_6 {f : Ω → ℝ} (hf : D.QuasiContinuous f) {V : Set Ω} (hV : IsOpen V)
    (h : ∀ᵐ ω ∂μ, ω ∈ V → 0 ≤ f ω) : ∀ᵐ ω ∂D.capOuter, ω ∈ V → 0 ≤ f ω := by
  rw [ae_iff, capOuter_apply]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  obtain ⟨G, hGo, hGc, hGf⟩ := hf ε (ENNReal.coe_pos.2 hε)
  obtain ⟨U, hUo, hU⟩ := (continuousOn_iff'.1 hGf) (Set.Iio 0) isOpen_Iio
  have hsub : {ω | ¬(ω ∈ V → 0 ≤ f ω)} ⊆ (V ∩ U) ∪ G := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Classical.not_imp, not_le] at hω
    by_cases hG : ω ∈ G
    · exact Or.inr hG
    · have h1 : ω ∈ f ⁻¹' Set.Iio 0 ∩ Gᶜ := ⟨hω.2, hG⟩
      rw [hU] at h1
      exact Or.inl ⟨hω.1, h1.1⟩
  have hae : ∀ᵐ ω ∂μ, ω ∈ (V ∩ U) ∪ G → ω ∈ G := by
    filter_upwards [h] with ω hω hmem
    rcases hmem with ⟨hV', hU'⟩ | hG
    · by_contra hG
      have h1 : ω ∈ U ∩ Gᶜ := ⟨hU', hG⟩
      rw [← hU] at h1
      exact absurd (hω hV') (not_le.2 h1.1)
    · exact hG
  calc D.cap {ω | ¬(ω ∈ V → 0 ≤ f ω)} ≤ D.cap ((V ∩ U) ∪ G) := D.cap_mono hsub
    _ = D.capAE ((V ∩ U) ∪ G) := D.cap_eq_capAE ((hV.inter hUo).union hGo)
    _ ≤ D.capAE G := D.capAE_mono_ae hae
    _ = D.cap G := (D.cap_eq_capAE hGo).symm
    _ ≤ 0 + ε := by rw [zero_add]; exact hGc.le

/--
BH 1991, ch. I § 8.2, proposition 8.2.1, q.e. uniqueness (pp. 54–55), by proposition 8.1.6.

BH proposition 8.2.1 (uniqueness): two quasi-continuous functions equal μ-a.e. are equal
quasi-everywhere.
-/
theorem bh_8_2_1_unique {f g : Ω → ℝ} (hf : D.QuasiContinuous f) (hg : D.QuasiContinuous g)
    (h : f =ᵐ[μ] g) : f =ᵐ[D.capOuter] g := by
  have h1 := D.bh_8_1_6 (D.quasiContinuous_sub hf hg) isOpen_univ
    (h.mono fun ω hω _ => by simp [hω])
  have h2 := D.bh_8_1_6 (D.quasiContinuous_sub hg hf) isOpen_univ
    (h.mono fun ω hω _ => by simp [hω])
  filter_upwards [h1, h2] with ω a b
  have a' := a (Set.mem_univ ω)
  have b' := b (Set.mem_univ ω)
  simp only [Pi.sub_apply] at a' b'
  linarith

omit [TopologicalSpace Ω] in
/-- For α > 0, α⁻¹|x| is admissible on the set where a representative of x has magnitude above α. -/
theorem smul_absS_mem_adm (x : D.Space) {φ : Ω → ℝ} (hφ : ⇑(D.toLp x) =ᵐ[μ] φ) {α : ℝ}
    (hα : 0 < α) : α⁻¹ • D.absS x ∈ D.adm {ω | α < |φ ω|} := by
  show ∀ᵐ ω ∂μ, ω ∈ {ω | α < |φ ω|} → 1 ≤ D.toLp (α⁻¹ • D.absS x) ω
  rw [map_smul, D.toLp_absS]
  filter_upwards [Lp.coeFn_smul α⁻¹ |D.toLp x|, Lp.coeFn_abs (D.toLp x), hφ] with ω h1 h2 h3 hω
  rw [h1, Pi.smul_apply, h2]
  simp only [smul_eq_mul]
  rw [h3, inv_mul_eq_div, one_le_div hα]
  exact hω.le

omit [TopologicalSpace Ω] in
/-- For α > 0, the squared norm of α⁻¹|x| is at most ‖x‖²/α². -/
theorem norm_smul_absS_sq_le (x : D.Space) {α : ℝ} (hα : 0 < α) :
    ‖α⁻¹ • D.absS x‖ ^ 2 ≤ ‖x‖ ^ 2 / α ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hα, mul_pow, inv_pow, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (D.norm_absS_le x) 2)
    (by positivity)

omit [TopologicalSpace Ω] in
/-- The a.e. capacity inequality for every representative φ of x. -/
theorem capAE_lt_abs_le (x : D.Space) {φ : Ω → ℝ} (hφ : ⇑(D.toLp x) =ᵐ[μ] φ) {α : ℝ}
    (hα : 0 < α) : D.capAE {ω | α < |φ ω|} ≤ ENNReal.ofReal (‖x‖ ^ 2 / α ^ 2) :=
  (D.capAE_le (D.smul_absS_mem_adm x hφ hα)).trans
    (ENNReal.ofReal_le_ofReal (D.norm_smul_absS_sq_le x hα))

/--
Fukushima 1980, § 3.1, inequality (3.1.10) (p. 65), for a continuous representative.

Fukushima (3.1.10): for a continuous representative, c{|φ| > α} ≤ α⁻² ‖x‖²_𝔻.
-/
theorem cap_lt_abs_le_of_continuous (x : D.Space) {φ : Ω → ℝ} (hφc : Continuous φ)
    (hφ : ⇑(D.toLp x) =ᵐ[μ] φ) {α : ℝ} (hα : 0 < α) :
    D.cap {ω | α < |φ ω|} ≤ ENNReal.ofReal (‖x‖ ^ 2 / α ^ 2) := by
  rw [D.cap_eq_capAE (isOpen_lt continuous_const hφc.abs)]
  exact D.capAE_lt_abs_le x hφ hα

/--
BH 1991, ch. I § 8.2, proposition 8.2.2 (p. 55), in the strict form established by the proof.

BH proposition 8.2.2, strict form (given by BH's proof): for quasi-continuous f̃ representing x,
c{|f̃| > α} ≤ α⁻² ‖x‖²_𝔻.
-/
theorem bh_8_2_2_lt (x : D.Space) {f : Ω → ℝ} (hf : D.QuasiContinuous f)
    (hfx : ⇑(D.toLp x) =ᵐ[μ] f) {α : ℝ} (hα : 0 < α) :
    D.cap {ω | α < |f ω|} ≤ ENNReal.ofReal (‖x‖ ^ 2 / α ^ 2) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨G, hGo, hGc, hGf⟩ := hf ε (ENNReal.coe_pos.2 hε)
  obtain ⟨U, hUo, hU⟩ := (continuousOn_iff'.1 hGf.abs) (Set.Ioi α) isOpen_Ioi
  have hGfin : D.capAE G ≠ ⊤ := by rw [← D.cap_eq_capAE hGo]; exact ne_top_of_lt hGc
  have hne := D.capAE_ne_top_iff.1 hGfin
  have hm := (D.equilibrium_spec hne).1
  have hz := D.supS_mem_adm_union (D.smul_absS_mem_adm x hfx hα) hm
  have hsub : U ∪ G ⊆ {ω | α < |f ω|} ∪ G := by
    intro ω hω
    by_cases hG : ω ∈ G
    · exact Or.inr hG
    · rcases hω with hU' | hG'
      · have h1 : ω ∈ U ∩ Gᶜ := ⟨hU', hG⟩
        rw [← hU] at h1
        exact Or.inl h1.1
      · exact absurd hG' hG
  have hA : {ω | α < |f ω|} ⊆ U ∪ G := by
    intro ω hω
    by_cases hG : ω ∈ G
    · exact Or.inr hG
    · have h1 : ω ∈ (fun ω => |f ω|) ⁻¹' Set.Ioi α ∩ Gᶜ := ⟨hω, hG⟩
      rw [hU] at h1
      exact Or.inl h1.1
  calc D.cap {ω | α < |f ω|} ≤ D.capAE (U ∪ G) := D.cap_le_capAE (hUo.union hGo) hA
    _ ≤ ENNReal.ofReal (‖D.supS (α⁻¹ • D.absS x) (D.equilibrium G)‖ ^ 2) :=
        D.capAE_le (D.adm_anti hsub hz)
    _ ≤ ENNReal.ofReal (‖α⁻¹ • D.absS x‖ ^ 2 + ‖D.equilibrium G‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (D.norm_supS_sq_le _ _)
    _ = ENNReal.ofReal (‖α⁻¹ • D.absS x‖ ^ 2) + D.capAE G := by
        rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), D.capAE_eq_equilibrium hne]
    _ ≤ ENNReal.ofReal (‖x‖ ^ 2 / α ^ 2) + ε := by
        refine add_le_add (ENNReal.ofReal_le_ofReal (D.norm_smul_absS_sq_le x hα)) ?_
        rw [← D.cap_eq_capAE hGo]; exact hGc.le

/--
BH 1991, ch. I § 8.2, proposition 8.2.2 as stated (p. 55); the passage to a non-strict threshold,
implicit in BH, is carried out here.

BH proposition 8.2.2, as stated: c{|f̃| ≥ α} ≤ α⁻² ‖x‖²_𝔻 (passage to the limit α' ↑ α in the strict
form, a step absent from BH).
-/
theorem bh_8_2_2 (x : D.Space) {f : Ω → ℝ} (hf : D.QuasiContinuous f)
    (hfx : ⇑(D.toLp x) =ᵐ[μ] f) {α : ℝ} (hα : 0 < α) :
    D.cap {ω | α ≤ |f ω|} ≤ ENNReal.ofReal (‖x‖ ^ 2 / α ^ 2) := by
  have hlim : Tendsto (fun β : ℝ => ENNReal.ofReal (‖x‖ ^ 2 / β ^ 2)) (𝓝[<] α)
      (𝓝 (ENNReal.ofReal (‖x‖ ^ 2 / α ^ 2))) := by
    refine (ENNReal.continuous_ofReal.tendsto _).comp (Tendsto.mono_left ?_ nhdsWithin_le_nhds)
    exact (continuousAt_const.div ((continuous_pow 2).continuousAt) (by positivity)).tendsto
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hα] with β hβ
  exact (D.cap_mono fun ω hω => lt_of_lt_of_le hβ.2 hω).trans (D.bh_8_2_2_lt x hf hfx hβ.1)

end DirichletForm
end ErrorCalculus.Capacity
