import ErrorCalculus.Dirichlet.RangeProjectionMeasurable
import ErrorCalculus.Dirichlet.ConditionalMatrix

/-!
# Kernel Projection

## Main results
Measurable bounded kernel tests. We use all columns of I − P_range, rescaled by 1 + their sup norm.
This avoids choosing a single unit kernel vector.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
namespace ErrorCalculus
variable {n : ℕ}

/-- Orthogonal kernel projection on symmetric matrices. -/
def kernelProjection (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - rangeProjection A

theorem measurable_kernelProjection : Measurable (kernelProjection (n := n)) :=
  measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j =>
    measurable_const.sub ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_rangeProjection))))

theorem mul_kernelProjection {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    A * kernelProjection A = 0 := by
  have h : A * rangeProjection A = A := by
    rw [← matrixPseudoInverse_mul hA, ← mul_assoc, mul_matrixPseudoInverse hA,
      rangeProjection_mul hA]
  simp [kernelProjection, mul_sub, h]

/-- A bounded measurable column, nonzero exactly when the corresponding kernel
projection column is nonzero. Normalization to length one is unnecessary. -/
def boundedKernelColumn (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : Fin n → ℝ :=
  (1 + ‖fun i => kernelProjection A i j‖)⁻¹ • (fun i => kernelProjection A i j)

theorem measurable_boundedKernelColumn (j : Fin n) :
    Measurable (fun A : Matrix (Fin n) (Fin n) ℝ => boundedKernelColumn A j) := by
  have hm : Measurable (fun A : Matrix (Fin n) (Fin n) ℝ => fun i => kernelProjection A i j) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_kernelProjection))
  exact ((measurable_const.add hm.norm).inv).smul hm

theorem boundedKernelColumn_bound (A : Matrix (Fin n) (Fin n) ℝ) (j i : Fin n) :
    ‖boundedKernelColumn A j i‖ ≤ 1 := by
  have hp : 0 < 1 + ‖fun i => kernelProjection A i j‖ := by positivity
  simp only [boundedKernelColumn, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hp]
  rw [inv_mul_eq_div, div_le_one hp]
  exact (norm_le_pi_norm (fun i => kernelProjection A i j) i).trans (by linarith)

theorem mulVec_boundedKernelColumn {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (j : Fin n) : A.mulVec (boundedKernelColumn A j) = 0 := by
  have h : A.mulVec (fun i => kernelProjection A i j) = 0 := by
    ext i
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) (mul_kernelProjection hA)
  simp [boundedKernelColumn, Matrix.mulVec_smul, h]

theorem det_ne_zero_of_boundedKernelColumn_eq_zero {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (h : ∀ j, boundedKernelColumn A j = 0) : A.det ≠ 0 := by
  have hk : kernelProjection A = 0 := by
    ext i j
    have hp : (1 + ‖fun i => kernelProjection A i j‖)⁻¹ ≠ 0 := by positivity
    have hz := congrFun (h j) i
    change (1 + ‖fun i => kernelProjection A i j‖)⁻¹ * kernelProjection A i j = 0 at hz
    exact (mul_eq_zero.mp hz).resolve_left hp
  have hr : rangeProjection A = 1 := sub_eq_zero.mp hk |>.symm
  have hd := congrArg Matrix.det ((mul_matrixPseudoInverse hA).trans hr)
  rw [Matrix.det_mul, Matrix.det_one] at hd
  intro hz
  simp [hz] at hd

end ErrorCalculus
