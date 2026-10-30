import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Positivity

noncomputable section
namespace Foundations

/-- Power-series majorization in a norm-one algebra. -/
theorem norm_exp_le_real_exp_norm {E : Type*} [NormedRing E] [NormedAlgebra ℝ E]
    [CompleteSpace E] [NormOneClass E] (A : E) : ‖NormedSpace.exp A‖ ≤ Real.exp ‖A‖ := by
  rw [Real.exp_eq_exp_ℝ]
  apply (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).norm_le_of_bounded
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖A‖)
  intro n
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le A n) (by positivity)

theorem exp_real_smul_one {E : Type*} [NormedRing E] [NormedAlgebra ℝ E]
    [CompleteSpace E] (t : ℝ) :
    NormedSpace.exp (t • (1:E)) = Real.exp t • (1:E) := by
  simpa [Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ] using
    (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := E) t).symm

end Foundations
