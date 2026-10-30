import ErrorCalculus.Dirichlet.KernelProjection
import ErrorCalculus.Dirichlet.DirichletCurrent

/-!
# Conditional Matrix Lemma

## Main results
Bouleau–Hirsch V.1.1.6.2, proved with finitely many bounded measurable kernel columns. The
measurable pseudoinverse replaces measurable unit selection.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology Matrix
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {n : ℕ}

/-- Integrability of a quadratic Γ expression with bounded image-measurable coefficients. -/
theorem integrable_gamma_image_quadratic (f : Fin n → S.dom)
    (q : Fin n → ImageTest (Fin n → ℝ)) :
    Integrable (fun ω => ∑ i, ∑ j, q i (S.representativeVec f ω) *
      q j (S.representativeVec f ω) * S.Γ (f i) (f j) ω) μ := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (((q i).mul (q j)).comp _ (S.measurable_representativeVec f)).integrable_mul _

/-- Conditional expectation tested against every bounded measurable quadratic field. -/
theorem integral_gamma_image_quadratic (f : Fin n → S.dom)
    (q : Fin n → ImageTest (Fin n → ℝ)) :
    (∫ ω, ∑ i, ∑ j, q i (S.representativeVec f ω) *
      q j (S.representativeVec f ω) * S.Γ (f i) (f j) ω ∂μ) =
    ∫ y, ∑ i, ∑ j, q i y * q j y * S.conditionalMatrix f y i j ∂S.eidImageLaw f := by
  have hi (i j : Fin n) :=
    (((q i).mul (q j)).comp _ (S.measurable_representativeVec f)).integrable_mul (S.Γ (f i) (f j))
  have hj (i j : Fin n) := ((q i).mul (q j)).integrable_mul (S.imageGammaMatrixGeneral f i j)
  dsimp only [ImageTest.comp, ImageTest.mul, Function.comp_def] at hi hj
  dsimp only [conditionalMatrix]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hj i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j), integral_finsetSum _ (fun j _ => hj i j)]
  exact Finset.sum_congr rfl (fun j _ =>
    (S.imageGammaMatrixGeneral_characterization f i j ((q i).mul (q j))).symm)

/-- Each rescaled kernel column is an admissible bounded test, coordinate by coordinate. -/
def conditionalKernelTest (f : Fin n → S.dom) (k i : Fin n) : ImageTest (Fin n → ℝ) where
  toFun y := boundedKernelColumn (S.conditionalMatrix f y) k i
  measurable := (measurable_pi_apply i).comp
    ((measurable_boundedKernelColumn k).comp (S.measurable_conditionalMatrix f))
  bound := ⟨1, fun y => boundedKernelColumn_bound _ k i⟩

/-- The original Γ matrix annihilates every measurable kernel column of its conditional matrix. -/
theorem gamma_mulVec_conditionalKernel_ae (f : Fin n → S.dom) (k : Fin n) :
    ∀ᵐ ω ∂μ, (Matrix.of (fun i j => S.Γ (f i) (f j) ω)).mulVec
      (boundedKernelColumn (S.conditionalMatrix f (S.representativeVec f ω)) k) = 0 := by
  let q := S.conditionalKernelTest f k
  have hzero : (∫ ω, ∑ i, ∑ j, q i (S.representativeVec f ω) *
      q j (S.representativeVec f ω) * S.Γ (f i) (f j) ω ∂μ) = 0 := by
    rw [S.integral_gamma_image_quadratic f q]
    have hpoint (y : Fin n → ℝ) :
        (∑ i, ∑ j, q i y * q j y * S.conditionalMatrix f y i j) = 0 := by
      have h := mulVec_boundedKernelColumn (S.conditionalMatrix_isHermitian f y) k
      have hd := congrArg (fun v => (boundedKernelColumn (S.conditionalMatrix f y) k) ⬝ᵥ v) h
      simpa [q, conditionalKernelTest, dotProduct, Matrix.mulVec, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm] using hd
    simp_rw [hpoint, integral_zero]
  have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ ∑ i, ∑ j, q i (S.representativeVec f ω) *
      q j (S.representativeVec f ω) * S.Γ (f i) (f j) ω := by
    filter_upwards [S.gammaMatrix_posSemidef_ae f] with ω hω
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      using hω.dotProduct_mulVec_nonneg (fun i => q i (S.representativeVec f ω))
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg
    (S.integrable_gamma_image_quadratic f q)).mp hzero
  filter_upwards [hae, S.gammaMatrix_posSemidef_ae f] with ω hz hp
  apply (hp.dotProduct_mulVec_zero_iff _).mp
  simpa [q, conditionalKernelTest, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using hz

/-- BH V.1.1.6.2, in source-space form: positive original determinant forces
nonzero conditional determinant. No external BH lemma is assumed. -/
theorem det_condMatrix_comp_ne_zero_ae (f : Fin n → S.dom) :
    ∀ᵐ ω ∂μ, 0 < (Matrix.of (fun i j => S.Γ (f i) (f j) ω)).det →
      (S.conditionalMatrix f (S.representativeVec f ω)).det ≠ 0 := by
  filter_upwards [ae_all_iff.mpr (S.gamma_mulVec_conditionalKernel_ae f)] with ω hω hdet
  apply det_ne_zero_of_boundedKernelColumn_eq_zero (S.conditionalMatrix_isHermitian f _)
  intro k
  have hinj : Function.Injective (Matrix.of (fun i j => S.Γ (f i) (f j) ω)).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hdet.ne'))
  apply hinj
  simpa using hω k

/-- BH V.1.1.6.2, after restriction to {det Γ > 0} and pushforward. -/
theorem det_condMatrix_ne_zero_ae (f : Fin n → S.dom) :
    ∀ᵐ y ∂S.eidMeasure f, (S.conditionalMatrix f y).det ≠ 0 := by
  have hm : Measurable (fun y => (S.conditionalMatrix f y).det) :=
    (continuous_id.matrix_det.measurable).comp (S.measurable_conditionalMatrix f)
  unfold eidMeasure
  apply (ae_map_iff (S.measurable_representativeVec f).aemeasurable
    (measurableSet_eq_fun hm measurable_const).compl).mpr
  apply (ae_restrict_iff (measurableSet_eq_fun
    (hm.comp (S.measurable_representativeVec f)) measurable_const).compl).mpr
  exact S.det_condMatrix_comp_ne_zero_ae f

end ErrorCalculus.ErrorStructure
