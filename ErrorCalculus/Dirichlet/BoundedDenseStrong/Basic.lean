import ErrorCalculus.Dirichlet.FormConvergence
import ErrorCalculus.Dirichlet.EIDVectorChain
import ErrorCalculus.Dirichlet.ExtensionLp
import ErrorCalculus.Dirichlet.GeneratorWeights.Basic
import ErrorCalculus.Dirichlet.SemigroupResolvent
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Density of bounded functions in the form space

This file contains the definitions and results of the development of
`ErrorCalculus.Dirichlet.BoundedDenseStrong` that the main statements of the library (the head
theorems listed in the README of the repository) use. `ErrorCalculus.Dirichlet.BoundedDenseStrong`
imports it and continues the development.

## Main definitions

* `ErrorStructure.gammaFormBilin`: The carré du champ as a bounded bilinear map for the form norm.

## Main statements

* `ErrorStructure.continuous_gamma_formSpace`: joint L¹ continuity of the carré du champ.
-/
noncomputable section

open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- The carré du champ as a bounded bilinear map for the form norm. -/
def gammaFormBilin : S.energy.FormSpace →L[ℝ] S.energy.FormSpace →L[ℝ] Lp ℝ 1 μ :=
  (S.Γ.compl₁₂ S.energy.formToDomain.toLinearMap S.energy.formToDomain.toLinearMap).mkContinuous₂
    2 (by
      intro x y
      apply (S.toErrorData.norm_gamma_le_energy (S.energy.formToDomain x)
        (S.energy.formToDomain y)).trans
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (S.energy.seminorm_le_formNorm _) (by norm_num)
      · exact S.energy.seminorm_le_formNorm _
      · exact Real.sqrt_nonneg _
      · positivity)

@[simp] theorem gammaFormBilin_apply (x y : S.energy.FormSpace) :
    S.gammaFormBilin x y = S.Γ (S.energy.formToDomain x) (S.energy.formToDomain y) := rfl

/-- joint L¹ continuity of the carré du champ. -/
theorem continuous_gamma_formSpace :
    Continuous (fun p : S.energy.FormSpace × S.energy.FormSpace =>
      S.Γ (S.energy.formToDomain p.1) (S.energy.formToDomain p.2)) :=
  S.gammaFormBilin.continuous₂

end ErrorCalculus.ErrorStructure
