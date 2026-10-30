import ErrorCalculus.Dirichlet.DensityCalculus
import ErrorCalculus.Dirichlet.DensityClosure
import Mathlib.Probability.Distributions.Gaussian.Real

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace ErrorCalculus

/-- The standard Gaussian density, using Mathlib's normalization. -/
def ouDensity : ℝ → ℝ := gaussianPDFReal 0 1

instance ouDensity_smooth : SmoothDensity ouDensity where
  contDiff := by
    unfold ouDensity gaussianPDFReal
    fun_prop
  pos x := gaussianPDFReal_pos 0 1 x (by norm_num)

theorem ouDensity_measure : densityMeasure ouDensity = gaussianReal 0 1 := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1:ℝ≥0) ≠ 0)]
  rfl

instance ouDensity_probability : IsProbabilityMeasure (densityMeasure ouDensity) := by
  rw [ouDensity_measure]
  infer_instance

/-- The OU proto-structure on the standard Gaussian probability space. -/
def ouProto : ProtoErrorStructure ℝ (gaussianReal 0 1) :=
  (densityProto ouDensity).transport ouDensity_measure

/-- direct specialization of X.3 after identifying the measures. -/
theorem ouProto_isClosable : ouProto.energy.IsClosable :=
  ProtoErrorStructure.isClosable_transport ouDensity_measure (densityProto ouDensity)
    (protoForm_isClosable ouDensity)

end ErrorCalculus
