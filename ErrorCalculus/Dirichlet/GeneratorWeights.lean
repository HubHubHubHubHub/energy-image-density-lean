import ErrorCalculus.Dirichlet.ProductRule
import ErrorCalculus.Dirichlet.EIDVectorCriterion
import ErrorCalculus.Dirichlet.SemigroupGenerator

noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

abbrev generatorResolvent := S.energy.formResolvent S.energy_closed S.dense
abbrev generatorDom := S.generatorResolvent.dom
abbrev generator := S.generatorResolvent.generator

/-- A measurable everywhere bounded version of an essentially bounded domain element. -/
def boundedRepresentative (F : S.dom) (hF : AEBounded (μ := μ) (F : Lp ℝ 2 μ)) : Ω → ℝ :=
  fun ω => truncation hF.choose (S.representative F ω)

theorem measurable_boundedRepresentative (F : S.dom)
    (hF : AEBounded (μ := μ) (F : Lp ℝ 2 μ)) : Measurable (S.boundedRepresentative F hF) :=
  (truncation_lipschitz _).continuous.measurable.comp (S.measurable_representative F)

theorem bounded_boundedRepresentative (F : S.dom)
    (hF : AEBounded (μ := μ) (F : Lp ℝ 2 μ)) :
    ∃ C : ℝ, ∀ ω, ‖S.boundedRepresentative F hF ω‖ ≤ C :=
  ⟨truncationBound hF.choose, fun _ => norm_truncation_le _ _⟩

theorem coeFn_boundedRepresentative (F : S.dom)
    (hF : AEBounded (μ := μ) (F : Lp ℝ 2 μ)) :
    ⇑(F : Lp ℝ 2 μ) =ᵐ[μ] S.boundedRepresentative F hF := by
  filter_upwards [S.coeFn_representative F,hF.choose_spec] with ω hω hb
  unfold boundedRepresentative
  rw [← hω, truncation_eq_self (by simpa only [Real.norm_eq_abs] using hb)]

theorem bounded_compactComp {d : ℕ} (hd : 0 < d) (u : Fin d → S.dom)
    (φ : (Fin d → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (hk : HasCompactSupport φ) :
    AEBounded (μ := μ) (S.compactComp hd u φ hφ hk : Lp ℝ 2 μ) := by
  obtain ⟨C,hC⟩ := hk.exists_bound_of_continuous hφ.continuous
  refine ⟨C,?_⟩
  filter_upwards [S.coeFn_compactComp hd u φ hφ hk] with ω hω
  rw [hω]
  exact hC _

/-- P.2(a,b): product rule followed by the generator integration by parts. -/
theorem integral_weight_gamma (u w v : S.dom) (hu : (u : Lp ℝ 2 μ) ∈ S.generatorDom)
    (hw : AEBounded (μ := μ) (w : Lp ℝ 2 μ))
    (hv : AEBounded (μ := μ) (v : Lp ℝ 2 μ)) :
    (∫ ω, (w : Lp ℝ 2 μ) ω * S.Γ v u ω ∂μ) =
      ∫ ω, (v : Lp ℝ 2 μ) ω *
        (-(2 * (w : Lp ℝ 2 μ) ω * S.generator ⟨u,hu⟩ ω + S.Γ w u ω)) ∂μ := by
  let p := S.boundedMul w v hw hv
  have hp := S.coeFn_boundedMul w v hw hv
  have h1 := (L1.integrable_coeFn (S.Γ v u)).bdd_mul
    (Lp.aestronglyMeasurable (w : Lp ℝ 2 μ)) hw.choose_spec
  have h2 := (L1.integrable_coeFn (S.Γ w u)).bdd_mul
    (Lp.aestronglyMeasurable (v : Lp ℝ 2 μ)) hv.choose_spec
  have h3 := ((Lp.memLp (w : Lp ℝ 2 μ)).integrable_mul
    (Lp.memLp (S.generator ⟨u,hu⟩))).bdd_mul
    (Lp.aestronglyMeasurable (v : Lp ℝ 2 μ)) hv.choose_spec
  change Integrable (fun ω => (v : Lp ℝ 2 μ) ω *
    ((w : Lp ℝ 2 μ) ω * S.generator ⟨u,hu⟩ ω)) μ at h3
  have he := S.energy.energy_eq_neg_inner_generator S.energy_closed S.dense ⟨u,hu⟩ p
  change S.energy.E u p = -inner ℝ (S.generator ⟨u,hu⟩) (p : Lp ℝ 2 μ) at he
  rw [S.energy.symm, ErrorData.energy_apply, L2.inner_def] at he
  simp only [RCLike.inner_apply, conj_trivial] at he
  have he' : (1/2 : ℝ) * (∫ ω, S.Γ p u ω ∂μ) =
      -(∫ ω, (v : Lp ℝ 2 μ) ω * ((w : Lp ℝ 2 μ) ω * S.generator ⟨u,hu⟩ ω) ∂μ) := by
    convert he using 2
    apply integral_congr_ae
    filter_upwards [hp] with ω hp
    rw [hp]
    ring
  have hg := integral_congr_ae (S.gamma_mul w v p u hw hv hp)
  rw [integral_add h1 h2] at hg
  have hr : (∫ ω, (v : Lp ℝ 2 μ) ω *
      (-(2 * (w : Lp ℝ 2 μ) ω * S.generator ⟨u,hu⟩ ω + S.Γ w u ω)) ∂μ) =
      -(2 * (∫ ω, (v : Lp ℝ 2 μ) ω *
        ((w : Lp ℝ 2 μ) ω * S.generator ⟨u,hu⟩ ω) ∂μ) +
        (∫ ω, (v : Lp ℝ 2 μ) ω * S.Γ w u ω ∂μ)) := by
    calc
      _ = ∫ ω, -(2 * ((v : Lp ℝ 2 μ) ω *
          ((w : Lp ℝ 2 μ) ω * S.generator ⟨u,hu⟩ ω)) +
          (v : Lp ℝ 2 μ) ω * S.Γ w u ω) ∂μ := by congr 1; ext ω; ring
      _ = _ := by rw [integral_neg, integral_add (h3.const_mul 2) h2, integral_const_mul]
  rw [hr]
  linarith

variable {d : ℕ}

/-- The proposed divergence is in L¹; Hölder suffices for its generator term. -/
theorem integrable_generatorDivergence (u : Fin d → S.dom)
    (hu : ∀ j, (u j : Lp ℝ 2 μ) ∈ S.generatorDom) (w : Fin d → Fin d → S.dom) (i : Fin d) :
    Integrable (fun ω => -∑ j, (2 * (w i j : Lp ℝ 2 μ) ω *
      S.generator ⟨u j,hu j⟩ ω + S.Γ (w i j) (u j) ω)) μ := by
  apply Integrable.neg
  apply integrable_finsetSum
  intro j _
  have h := ((Lp.memLp (w i j : Lp ℝ 2 μ)).integrable_mul
    (Lp.memLp (S.generator ⟨u j,hu j⟩))).const_mul 2
  have h' : Integrable (fun ω => 2 * (w i j : Lp ℝ 2 μ) ω *
      S.generator ⟨u j,hu j⟩ ω) μ := by simpa only [Pi.mul_apply, mul_assoc] using h
  exact h'.add (L1.integrable_coeFn _)

/-- The concrete L¹ Malliavin divergence with normalization E = 1/2 ∫ Γ. -/
def generatorDivergence (u : Fin d → S.dom)
    (hu : ∀ j, (u j : Lp ℝ 2 μ) ∈ S.generatorDom) (w : Fin d → Fin d → S.dom) :
    Fin d → Lp ℝ 1 μ := fun i => (S.integrable_generatorDivergence u hu w i).toL1 _

theorem coeFn_generatorDivergence (u : Fin d → S.dom)
    (hu : ∀ j, (u j : Lp ℝ 2 μ) ∈ S.generatorDom) (w : Fin d → Fin d → S.dom) (i : Fin d) :
    ⇑(S.generatorDivergence u hu w i) =ᵐ[μ] fun ω => -∑ j,
      (2 * (w i j : Lp ℝ 2 μ) ω * S.generator ⟨u j,hu j⟩ ω + S.Γ (w i j) (u j) ω) :=
  (S.integrable_generatorDivergence u hu w i).coeFn_toL1

/--
bounded weights in D and coordinates in D(A) give the divergence. The coordinates themselves need
not be bounded.
-/
theorem hasDivergence_of_generator (hd : 0 < d) (u : Fin d → S.dom)
    (hu : ∀ j, (u j : Lp ℝ 2 μ) ∈ S.generatorDom) (w : Fin d → Fin d → S.dom)
    (hw : ∀ i j, AEBounded (μ := μ) (w i j : Lp ℝ 2 μ)) :
    S.HasDivergence hd u (fun i j => S.boundedRepresentative (w i j) (hw i j))
      (S.generatorDivergence u hu w) := by
  intro i φ hφ hk
  let v := S.compactComp hd u φ hφ hk
  have hv := S.bounded_compactComp hd u φ hφ hk
  have hi (j : Fin d) : Integrable (fun ω => (w i j : Lp ℝ 2 μ) ω * S.Γ v (u j) ω) μ :=
    (L1.integrable_coeFn _).bdd_mul (Lp.aestronglyMeasurable _) (hw i j).choose_spec
  have hr (j : Fin d) : Integrable (fun ω => (v : Lp ℝ 2 μ) ω *
      (-(2 * (w i j : Lp ℝ 2 μ) ω * S.generator ⟨u j,hu j⟩ ω + S.Γ (w i j) (u j) ω))) μ := by
    have h := ((Lp.memLp (w i j : Lp ℝ 2 μ)).integrable_mul
      (Lp.memLp (S.generator ⟨u j,hu j⟩))).const_mul 2
    apply Integrable.bdd_mul _ (Lp.aestronglyMeasurable _) hv.choose_spec
    have h' : Integrable (fun ω => 2 * (w i j : Lp ℝ 2 μ) ω *
        S.generator ⟨u j,hu j⟩ ω) μ := by simpa only [Pi.mul_apply, mul_assoc] using h
    exact (h'.add (L1.integrable_coeFn _)).neg
  calc
    _ = ∫ ω, ∑ j, (w i j : Lp ℝ 2 μ) ω * S.Γ v (u j) ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr (fun j => S.coeFn_boundedRepresentative (w i j) (hw i j))]
        with ω hω
      simp only [hω, v]
    _ = ∑ j, ∫ ω, (w i j : Lp ℝ 2 μ) ω * S.Γ v (u j) ω ∂μ :=
      integral_finsetSum _ (fun j _ => hi j)
    _ = ∑ j, ∫ ω, (v : Lp ℝ 2 μ) ω *
        (-(2 * (w i j : Lp ℝ 2 μ) ω * S.generator ⟨u j,hu j⟩ ω + S.Γ (w i j) (u j) ω)) ∂μ := by
      apply Finset.sum_congr rfl
      intro j _
      exact S.integral_weight_gamma (u j) (w i j) v (hu j) (hw i j) hv
    _ = ∫ ω, ∑ j, (v : Lp ℝ 2 μ) ω *
        (-(2 * (w i j : Lp ℝ 2 μ) ω * S.generator ⟨u j,hu j⟩ ω + S.Γ (w i j) (u j) ω)) ∂μ :=
      (integral_finsetSum _ (fun j _ => hr j)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [S.coeFn_compactComp hd u φ hφ hk, S.coeFn_generatorDivergence u hu w i]
        with ω hv hδ
      change (∑ j, (S.compactComp hd u φ hφ hk : Lp ℝ 2 μ) ω * _) = _
      rw [hv,hδ]
      simp only [← Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- The divergence identity is independent of all choices on null sets. -/
theorem hasDivergence_of_generator_ae (hd : 0 < d) (u : Fin d → S.dom)
    (hu : ∀ j, (u j : Lp ℝ 2 μ) ∈ S.generatorDom) (w : Fin d → Fin d → S.dom)
    (hw : ∀ i j, AEBounded (μ := μ) (w i j : Lp ℝ 2 μ))
    (a : Fin d → Fin d → Ω → ℝ)
    (ha : ∀ i j, ⇑(w i j : Lp ℝ 2 μ) =ᵐ[μ] a i j) :
    S.HasDivergence hd u a (S.generatorDivergence u hu w) := by
  intro i φ hφ hk
  have h := S.hasDivergence_of_generator hd u hu w hw i φ hφ hk
  refine Eq.trans (integral_congr_ae ?_) h
  filter_upwards [ae_all_iff.mpr (fun j => ha i j),
    ae_all_iff.mpr (fun j => S.coeFn_boundedRepresentative (w i j) (hw i j))] with ω h1 h2
  apply Finset.sum_congr rfl
  intro j _
  rw [← h1 j, h2 j]

/-- In particular, the original L² representatives satisfy the exact P.2(c) identity. -/
theorem hasDivergence_of_generator_coeFn (hd : 0 < d) (u : Fin d → S.dom)
    (hu : ∀ j, (u j : Lp ℝ 2 μ) ∈ S.generatorDom) (w : Fin d → Fin d → S.dom)
    (hw : ∀ i j, AEBounded (μ := μ) (w i j : Lp ℝ 2 μ)) :
    S.HasDivergence hd u (fun i j => (w i j : Lp ℝ 2 μ)) (S.generatorDivergence u hu w) :=
  S.hasDivergence_of_generator_ae hd u hu w hw _ (fun _ _ => Filter.EventuallyEq.rfl)

/-- The concrete generator-weight criterion for absolute continuity. -/
theorem absolutelyContinuous_map_of_generator_weights (hd : 0 < d) (u : Fin d → S.dom)
    (hu : ∀ j, (u j : Lp ℝ 2 μ) ∈ S.generatorDom) (w : Fin d → Fin d → S.dom)
    (hw : ∀ i j, AEBounded (μ := μ) (w i j : Lp ℝ 2 μ))
    (hinv : ∀ i k, ∀ᵐ ω ∂μ, ∑ j, (w i j : Lp ℝ 2 μ) ω * S.Γ (u j) (u k) ω =
      if i = k then 1 else 0) : μ.map (S.toEuclidean u) ≪ volume := by
  classical
  apply S.absolutelyContinuous_map_of_weights hd u
    (w := fun i j => S.boundedRepresentative (w i j) (hw i j))
    (δ := S.generatorDivergence u hu w) ?_ (S.hasDivergence_of_generator hd u hu w hw)
  refine ⟨fun i j => S.measurable_boundedRepresentative _ _,
    fun i j => S.bounded_boundedRepresentative _ _, fun i k => ?_⟩
  filter_upwards [hinv i k,
    ae_all_iff.mpr (fun j => S.coeFn_boundedRepresentative (w i j) (hw i j))] with ω hi he
  simpa only [he] using hi

end ErrorCalculus.ErrorStructure
