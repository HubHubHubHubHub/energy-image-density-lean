import ErrorCalculus.Dirichlet.ExtensionLp

/-!
# Limits for the closure of the functional calculus

This file contains the results of the development of `ErrorCalculus.Dirichlet.ClosureCalculusLimits`
that the main statements of the library (the head theorems listed in the README of the repository)
use. `ErrorCalculus.Dirichlet.ClosureCalculusLimits` imports it and continues the development.

## Main statements

* `fderiv_coefficient_bound`: Uniform bound for each derivative coefficient in the finite-coordinate
  convention.
-/
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace ErrorCalculus

/-- Uniform bound for each derivative coefficient in the finite-coordinate convention. -/
theorem fderiv_coefficient_bound {k : ℕ} {F : (Fin k → ℝ) → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L F) (x : Fin k → ℝ) (i : Fin k) :
    |fderiv ℝ F x (Pi.single i 1)| ≤ L := by
  have h := (fderiv ℝ F x).le_opNorm (Pi.single i 1)
  have hn := norm_fderiv_le_of_lipschitz ℝ hL (x₀ := x)
  have hs : ‖(Pi.single i 1 : Fin k → ℝ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  simpa only [Real.norm_eq_abs, mul_one] using h.trans
    (mul_le_mul hn hs (norm_nonneg _) L.coe_nonneg)

end ErrorCalculus
