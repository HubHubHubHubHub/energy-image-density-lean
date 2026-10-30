import ErrorCalculus.Dirichlet.MixedConditionalMatrix
import ErrorCalculus.Dirichlet.GeneratorComposition
import ErrorCalculus.Dirichlet.PolarCurrentNormal

noncomputable section
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {n : ℕ}

theorem integrable_mixedConditionalMatrix_columnNorm (f g : Fin n → S.dom) (j : Fin n) :
    Integrable (fun y => polarNorm (fun i => S.mixedConditionalMatrix f g y i j)) (S.eidImageLaw f) :=
  ((euclideanEquiv n).toContinuousLinearMap.integrable_comp
    (integrable_pi_iff.mpr (fun i => L1.integrable_coeFn (S.condMatrixEntry f g i j)))).norm

/-- The current T_(f,g_j) is the normalized column j of the mixed matrix.
In applications g is the kth generator approximation of f. -/
def dirichletRowSeq (f g : Fin n → S.dom) (j : Fin n) : PolarCurrent n :=
  PolarCurrent.ofDensity (S.eidImageLaw f) (fun y i => S.condMatrixEntry f g i j y)
    (measurable_pi_lambda _ (fun i => (Lp.stronglyMeasurable _).measurable))
    (S.integrable_mixedConditionalMatrix_columnNorm f g j) j

theorem dirichletRowSeq_action (f g : Fin n → S.dom) (j : Fin n)
    (h : Fin n → ImageTest (Fin n → ℝ)) :
    (S.dirichletRowSeq f g j).action (fun i => h i) =
      ∑ i, ∫ x, h i (S.representativeVec f x) * S.Γ (f i) (g j) x ∂μ := by
  rw [dirichletRowSeq, PolarCurrent.ofDensity_action,
    integral_finsetSum Finset.univ (fun i _ => (h i).integrable_mul (S.condMatrixEntry f g i j))]
  exact Finset.sum_congr rfl (fun i _ => S.condMatrixEntry_characterization f g i j (h i))

/-- Boundary of a Dirichlet current. The factor two is forced by E = (1/2)∫Γ,
whereas EBM uses the energy-density convention E = ∫γ. -/
theorem dirichletRowSeq_boundary (f g : Fin n → S.dom) (i : Fin n)
    (hi : (g i : Lp ℝ 2 μ) ∈ S.generatorDom)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (hk : HasCompactSupport φ) :
    (S.dirichletRowSeq f g i).boundary φ =
      -(∫ x, φ (S.representativeVec f x) * (2 * S.generator ⟨g i, hi⟩ x) ∂μ) := by
  have hn : 0 < n := i.pos
  have hC : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hk hC (by norm_num)
  let h : Fin n → ImageTest (Fin n → ℝ) := fun j =>
    ⟨fun y => fderiv ℝ φ y (Pi.single j 1),
      ((hC.fderiv_right (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuous.clm_apply
        continuous_const).measurable,
      L, fun y => norm_partialDeriv_le hL j y⟩
  have hiq (j : Fin n) := ((h j).comp _ (S.measurable_representativeVec f)).integrable_mul
    (S.Γ (f j) (g i))
  have hg := S.gamma_comp_eq_sum hn f hC hk (S.compactComp hn f φ hC hk)
    (S.coeFn_compactComp hn f φ hC hk) (g i)
  have he := S.energy.energy_eq_neg_inner_generator S.energy_closed S.dense
    ⟨g i, hi⟩ (S.compactComp hn f φ hC hk)
  change S.energy.E (g i) (S.compactComp hn f φ hC hk) = _ at he
  rw [S.energy.symm, ErrorData.energy_apply, L2.inner_def] at he
  simp only [RCLike.inner_apply, conj_trivial] at he
  have hc : (∫ x, (S.compactComp hn f φ hC hk : Lp ℝ 2 μ) x *
      S.generator ⟨g i, hi⟩ x ∂μ) =
      ∫ x, φ (S.representativeVec f x) * S.generator ⟨g i, hi⟩ x ∂μ :=
    integral_congr_ae ((S.coeFn_compactComp hn f φ hC hk).mono (fun x hx => by dsimp; rw [hx]))
  rw [hc] at he
  change (S.dirichletRowSeq f g i).action (fun j => h j) = _
  rw [S.dirichletRowSeq_action]
  dsimp only [ImageTest.comp, Function.comp_def, h] at hiq ⊢
  rw [← integral_finsetSum Finset.univ (fun j _ => hiq j), ← integral_congr_ae hg]
  have hr : (∫ x, φ (S.representativeVec f x) * (2 * S.generator ⟨g i, hi⟩ x) ∂μ) =
      2 * ∫ x, φ (S.representativeVec f x) * S.generator ⟨g i, hi⟩ x ∂μ := by
    simp_rw [mul_left_comm _ (2 : ℝ)]
    exact integral_const_mul _ _
  rw [hr]
  linarith

/--
For g_i in the generator domain, the mixed current formed from Γ(f_j, g_i) is normal. With E =
(1/2)∫Γ, its divergence is +2 f_*(Ag_i μ) and its boundary is −2 f_*(Ag_i μ). This is the
normalization of Eriksson-Bique–Murugan, Lemma 4.11, adapted to Γ = 2γ.
-/
theorem dirichletRowSeq_isNormal (f g : Fin n → S.dom) (i : Fin n)
    (hi : (g i : Lp ℝ 2 μ) ∈ S.generatorDom) : (S.dirichletRowSeq f g i).IsNormal := by
  apply PolarCurrent.isNormal_of_source_density _ (S.representativeVec f)
    (S.measurable_representativeVec f) (fun x => 2 * S.generator ⟨g i, hi⟩ x)
    (measurable_const.mul (Lp.stronglyMeasurable _).measurable)
    (((Lp.memLp (S.generator ⟨g i, hi⟩)).integrable (by norm_num)).const_mul 2)
  exact S.dirichletRowSeq_boundary f g i hi


end ErrorCalculus.ErrorStructure
