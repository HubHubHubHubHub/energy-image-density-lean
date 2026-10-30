import ErrorCalculus.Dirichlet.ImageL1Transfer
import ErrorCalculus.Dirichlet.ConditionalMatrixLemma
import ErrorCalculus.Dirichlet.GeneratorApproximation
import ErrorCalculus.Dirichlet.FiniteL1Subsequence

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {n : ℕ}

/-- Conditional density Γ[f_i,g_j] on the fixed image space of f.
The matrix is generally not symmetric. Currents are its columns. -/
def condMatrixEntry (f g : Fin n → S.dom) (i j : Fin n) : Lp ℝ 1 (S.eidImageLaw f) :=
  imageL1 (fun k => (f k : Lp ℝ 2 μ)) (S.Γ (f i) (g j))

theorem condMatrixEntry_characterization (f g : Fin n → S.dom) (i j : Fin n)
    (h : ImageTest (Fin n → ℝ)) :
    (∫ y, h y * S.condMatrixEntry f g i j y ∂S.eidImageLaw f) =
      ∫ ω, h (S.representativeVec f ω) * S.Γ (f i) (g j) ω ∂μ := by
  have he := imageL1_characterization (fun k => (f k : Lp ℝ 2 μ)) (S.Γ (f i) (g j)) h
  exact he.trans (integral_congr_ae ((S.imageRepresentative_ae_representativeVec f).mono
    (fun ω hω => by dsimp only; rw [hω])))

theorem condMatrixEntry_self (f : Fin n → S.dom) (i j : Fin n) :
    S.condMatrixEntry f f i j = S.imageGammaMatrixGeneral f i j := by
  apply ImageTest.eq_of_integral_eq
  intro h
  exact (S.condMatrixEntry_characterization f f i j h).trans
    (S.imageGammaMatrixGeneral_characterization f i j h).symm

/-- L¹ convergence of the mixed conditional densities under form convergence. -/
theorem condMatrix_tendsto_L1 (f : Fin n → S.dom) (g : ℕ → Fin n → S.dom)
    (hg : ∀ j, Tendsto (fun k => S.energy.formToDomain.symm (g k j)) atTop
      (𝓝 (S.energy.formToDomain.symm (f j)))) (i j : Fin n) :
    Tendsto (fun k => S.condMatrixEntry f (g k) i j) atTop
      (𝓝 (S.imageGammaMatrixGeneral f i j)) := by
  have hgamma : Tendsto (fun k => S.Γ (f i) (g k j)) atTop (𝓝 (S.Γ (f i) (f j))) := by
    simpa only [Function.comp_def, LinearEquiv.apply_symm_apply] using
      (S.continuous_gamma_formSpace.tendsto
        (S.energy.formToDomain.symm (f i), S.energy.formToDomain.symm (f j))).comp
        ((tendsto_const_nhds (x := S.energy.formToDomain.symm (f i))).prodMk_nhds (hg j))
  have h := ((imageL1 (fun k => (f k : Lp ℝ 2 μ))).continuous.tendsto _).comp hgamma
  change Tendsto (fun k => S.condMatrixEntry f (g k) i j) atTop
    (𝓝 (S.condMatrixEntry f f i j)) at h
  rwa [S.condMatrixEntry_self] at h

/-- Pointwise representative of the nonsymmetric mixed conditional matrix. -/
def mixedConditionalMatrix (f g : Fin n → S.dom) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => S.condMatrixEntry f g i j y

theorem measurable_mixedConditionalMatrix (f g : Fin n → S.dom) :
    Measurable (S.mixedConditionalMatrix f g) :=
  measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => (Lp.stronglyMeasurable _).measurable))

/-- EBM (4.19): one subsequence yields determinant convergence ν-a.e. -/
theorem det_condMatrix_seq_tendsto_ae (f : Fin n → S.dom) (g : ℕ → Fin n → S.dom)
    (hg : ∀ j, Tendsto (fun k => S.energy.formToDomain.symm (g k j)) atTop
      (𝓝 (S.energy.formToDomain.symm (f j)))) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ᵐ y ∂S.eidMeasure f,
      Tendsto (fun k => (S.mixedConditionalMatrix f (g (s k)) y).det) atTop
        (𝓝 (S.conditionalMatrix f y).det) := by
  obtain ⟨s, hs, hae⟩ := exists_subseq_L1_finite_ae
    (fun k (p : Fin n × Fin n) => S.condMatrixEntry f (g k) p.1 p.2)
    (fun p => S.imageGammaMatrixGeneral f p.1 p.2)
    (fun p => S.condMatrix_tendsto_L1 f g hg p.1 p.2)
  refine ⟨s, hs, ?_⟩
  filter_upwards [(S.eidMeasure_absolutelyContinuous_imageLaw f).ae_le hae] with y hy
  apply Continuous.tendsto (continuous_id.matrix_det) _ |>.comp
  exact tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => hy (i, j)))

end ErrorCalculus.ErrorStructure
