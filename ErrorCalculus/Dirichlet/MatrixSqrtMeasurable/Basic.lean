import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurable square roots of positive semidefinite matrices

This file contains the results of the development of `ErrorCalculus.Dirichlet.MatrixSqrtMeasurable`
that the main statements of the library (the head theorems listed in the README of the repository)
use. `ErrorCalculus.Dirichlet.MatrixSqrtMeasurable` imports it and continues the development.

## Main statements

* `matrix_cfc_tendsto`: Finite spectrum makes pointwise convergence sufficient for matrix functional
  calculus.
-/
noncomputable section
open Filter Topology Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder
namespace ErrorCalculus
variable {d : ℕ}

instance matrixMeasurableSpace : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

instance matrixBorelSpace : BorelSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))

/-- Finite spectrum makes pointwise convergence sufficient for matrix functional calculus. -/
theorem matrix_cfc_tendsto {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (h : ∀ i, Tendsto (fun n => f n (hA.eigenvalues i)) atTop
      (𝓝 (g (hA.eigenvalues i)))) :
    Tendsto (fun n => cfc (f n) A) atTop (𝓝 (cfc g A)) := by
  simp only [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have hv := (tendsto_pi_nhds.mpr h)
  have hc : Continuous (fun v : Fin d → ℝ =>
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) * Matrix.diagonal v *
        star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) := by fun_prop
  simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
    hc.continuousAt.tendsto.comp hv

end ErrorCalculus
