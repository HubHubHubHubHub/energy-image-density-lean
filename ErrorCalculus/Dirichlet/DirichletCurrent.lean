import ErrorCalculus.Dirichlet.MatrixSqrtMeasurable
import ErrorCalculus.Dirichlet.ConditionalMatrix
import ErrorCalculus.Dirichlet.PolarCurrentDensity
import ErrorCalculus.Dirichlet.GeneratorWeights

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {n : ℕ}

/-- Everywhere measurable matrix representative of the image L¹ entries. -/
def conditionalMatrix (f : Fin n → S.dom) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => S.imageGammaMatrixGeneral f i j y

theorem measurable_conditionalMatrix (f : Fin n → S.dom) : Measurable (S.conditionalMatrix f) :=
  measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j =>
    S.imageGammaMatrixGeneral_measurable f i j))

theorem conditionalMatrix_isHermitian (f : Fin n → S.dom) (y : Fin n → ℝ) :
    (S.conditionalMatrix f y).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  exact congrArg (fun g : Lp ℝ 1 (S.eidImageLaw f) => g y)
    (S.imageGammaMatrixGeneral_symm f j i)

theorem integrable_conditionalMatrix_rowNorm (f : Fin n → S.dom) (i : Fin n) :
    Integrable (fun y => polarNorm (S.conditionalMatrix f y i)) (S.eidImageLaw f) :=
  ((euclideanEquiv n).toContinuousLinearMap.integrable_comp
    (integrable_pi_iff.mpr (fun j => L1.integrable_coeFn (S.imageGammaMatrixGeneral f i j)))).norm

/-- EBM Definition 4.10: the current T_(f,f_i), in polar form. -/
def dirichletRow (f : Fin n → S.dom) (i : Fin n) : PolarCurrent n :=
  PolarCurrent.ofDensity (S.eidImageLaw f) (fun y => S.conditionalMatrix f y i)
    ((measurable_pi_apply i).comp (S.measurable_conditionalMatrix f))
    (S.integrable_conditionalMatrix_rowNorm f i) i

/-- The mass uses the Euclidean length of row i, without boundedness assumptions on Γ. -/
theorem dirichletRow_mass (f : Fin n → S.dom) (i : Fin n) :
    (S.dirichletRow f i).mass = (S.eidImageLaw f).withDensity
      (fun y => ENNReal.ofReal (polarNorm (S.conditionalMatrix f y i))) := rfl

theorem dirichletRow_norm (f : Fin n → S.dom) (i : Fin n) :
    ∀ᵐ y ∂(S.dirichletRow f i).mass, polarNorm ((S.dirichletRow f i).direction y) = 1 :=
  (S.dirichletRow f i).norm_direction

/-- The defining action identity on bounded measurable one-forms. -/
theorem dirichletRow_action (f : Fin n → S.dom) (i : Fin n)
    (h : Fin n → ImageTest (Fin n → ℝ)) :
    (S.dirichletRow f i).action (fun j => h j) =
      ∑ j, ∫ ω, h j (S.representativeVec f ω) * S.Γ (f i) (f j) ω ∂μ := by
  rw [dirichletRow, PolarCurrent.ofDensity_action]
  change (∫ y, ∑ j, h j y * S.imageGammaMatrixGeneral f i j y ∂S.eidImageLaw f) = _
  rw [integral_finsetSum _ (fun j _ => (h j).integrable_mul (S.imageGammaMatrixGeneral f i j))]
  exact Finset.sum_congr rfl (fun j _ => S.imageGammaMatrixGeneral_characterization f i j (h j))

/-- The EID measure is dominated by the unrestricted image law. -/
theorem eidMeasure_le_imageLaw (f : Fin n → S.dom) : S.eidMeasure f ≤ S.eidImageLaw f := by
  rw [S.eidImageLaw_eq_map]
  exact Measure.map_mono Measure.restrict_le_self (S.measurable_representativeVec f)

theorem eidMeasure_absolutelyContinuous_imageLaw (f : Fin n → S.dom) :
    S.eidMeasure f ≪ S.eidImageLaw f := Measure.absolutelyContinuous_of_le (S.eidMeasure_le_imageLaw f)

end ErrorCalculus.ErrorStructure
