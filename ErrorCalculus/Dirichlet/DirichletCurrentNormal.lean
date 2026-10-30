import ErrorCalculus.Dirichlet.DirichletCurrent
import ErrorCalculus.Dirichlet.PolarCurrentNormal
import ErrorCalculus.Dirichlet.GeneratorComposition

noncomputable section
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {n : ℕ}

/-- Boundary of a Dirichlet current. The factor two is forced by E = (1/2)∫Γ,
whereas EBM uses the energy-density convention E = ∫γ. -/
theorem dirichletRow_boundary (f : Fin n → S.dom) (i : Fin n)
    (hi : (f i : Lp ℝ 2 μ) ∈ S.generatorDom)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (hk : HasCompactSupport φ) :
    (S.dirichletRow f i).boundary φ =
      -(∫ x, φ (S.representativeVec f x) * (2 * S.generator ⟨f i, hi⟩ x) ∂μ) := by
  have hn : 0 < n := i.pos
  have hC : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hk hC (by norm_num)
  let h : Fin n → ImageTest (Fin n → ℝ) := fun j =>
    ⟨fun y => fderiv ℝ φ y (Pi.single j 1),
      ((hC.fderiv_right (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuous.clm_apply
        continuous_const).measurable,
      L, fun y => norm_partialDeriv_le hL j y⟩
  have hiq (j : Fin n) := ((h j).comp _ (S.measurable_representativeVec f)).integrable_mul
    (S.Γ (f j) (f i))
  have hg := S.gamma_comp_eq_sum hn f hC hk (S.compactComp hn f φ hC hk)
    (S.coeFn_compactComp hn f φ hC hk) (f i)
  have he := S.energy.energy_eq_neg_inner_generator S.energy_closed S.dense
    ⟨f i, hi⟩ (S.compactComp hn f φ hC hk)
  change S.energy.E (f i) (S.compactComp hn f φ hC hk) = _ at he
  rw [S.energy.symm, ErrorData.energy_apply, L2.inner_def] at he
  simp only [RCLike.inner_apply, conj_trivial] at he
  have hc : (∫ x, (S.compactComp hn f φ hC hk : Lp ℝ 2 μ) x *
      S.generator ⟨f i, hi⟩ x ∂μ) =
      ∫ x, φ (S.representativeVec f x) * S.generator ⟨f i, hi⟩ x ∂μ :=
    integral_congr_ae ((S.coeFn_compactComp hn f φ hC hk).mono (fun x hx => by dsimp; rw [hx]))
  rw [hc] at he
  change (S.dirichletRow f i).action (fun j => h j) = _
  rw [S.dirichletRow_action]
  simp_rw [S.Γ_symm (f i)]
  dsimp only [ImageTest.comp, Function.comp_def, h] at hiq ⊢
  rw [← integral_finsetSum Finset.univ (fun j _ => hiq j), ← integral_congr_ae hg]
  have hr : (∫ x, φ (S.representativeVec f x) * (2 * S.generator ⟨f i, hi⟩ x) ∂μ) =
      2 * ∫ x, φ (S.representativeVec f x) * S.generator ⟨f i, hi⟩ x ∂μ := by
    simp_rw [mul_left_comm _ (2 : ℝ)]
    exact integral_const_mul _ _
  rw [hr]
  linarith

/-- EBM Lemma 4.11 in the library's normalization. The divergence density is
+2 Af_i; the distributional boundary density is −2 Af_i. -/
theorem dirichletRow_isNormal (f : Fin n → S.dom) (i : Fin n)
    (hi : (f i : Lp ℝ 2 μ) ∈ S.generatorDom) : (S.dirichletRow f i).IsNormal := by
  apply PolarCurrent.isNormal_of_source_density _ (S.representativeVec f)
    (S.measurable_representativeVec f) (fun x => 2 * S.generator ⟨f i, hi⟩ x)
    (measurable_const.mul (Lp.stronglyMeasurable _).measurable)
    (((Lp.memLp (S.generator ⟨f i, hi⟩)).integrable (by norm_num)).const_mul 2)
  exact S.dirichletRow_boundary f i hi

end ErrorCalculus.ErrorStructure
