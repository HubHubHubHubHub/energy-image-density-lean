import ErrorCalculus.Dirichlet.MatrixFunctionalMeasurable

/-!
# Measurable pseudo-inverse and range projection of symmetric matrices

This file contains the definitions and results of the development of
`ErrorCalculus.Dirichlet.RangeProjectionMeasurable` that the main statements of the library (the
head theorems listed in the README of the repository) use.
`ErrorCalculus.Dirichlet.RangeProjectionMeasurable` imports it and continues the development.

## Main definitions

* `matrixPseudoInverse`: Spectral reciprocal, with reciprocal zero at zero.
* `rangeProjection`: The spectral indicator of the nonzero eigenvalues.

## Main statements

* `rangeProjection_isSymm`: The matrix `rangeProjection A` is symmetric for every real square matrix
  `A`.
* `rangeProjection_idempotent`: The matrix `rangeProjection A` is idempotent for every real square
  matrix `A`.
-/
noncomputable section
open Filter Topology Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder
namespace ErrorCalculus
variable {d : ℕ}

/-- Spectral reciprocal, with reciprocal zero at zero. It is not the nonsingular matrix inverse. -/
def matrixPseudoInverse (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  cfc (fun t : ℝ => t⁻¹) A

/-- The spectral indicator of the nonzero eigenvalues. -/
def rangeProjection (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  cfc (fun t : ℝ => t * t⁻¹) A

/-- Continuous regularizers converge to the spectral reciprocal, including on the kernel. -/
theorem matrixPseudoInverse_tendsto {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    Tendsto (fun n : ℕ => cfc (fun t : ℝ => t / (t^2 + 1 / (n + 1))) A)
      atTop (𝓝 (matrixPseudoInverse A)) := by
  apply matrix_cfc_tendsto hA
  intro i
  generalize hA.eigenvalues i = t
  by_cases ht : t = 0
  · simp only [ht, zero_div, _root_.inv_zero]
    exact tendsto_const_nhds
  · have h := (tendsto_const_nhds (x := t)).div
      ((tendsto_const_nhds (x := t^2)).add tendsto_one_div_add_atTop_nhds_zero_nat)
      (by simpa using pow_ne_zero 2 ht)
    have he : t / (t^2 + 0) = t⁻¹ := by simp [div_eq_mul_inv, pow_two, ht]
    simpa only [Pi.div_def, Pi.add_def, he] using h

theorem measurable_matrixPseudoInverse : Measurable (matrixPseudoInverse (d := d)) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n A => cfc (fun t : ℝ => t / (t^2 + 1 / (n + 1))) A)
  · intro n
    apply measurable_matrix_cfc
    apply Continuous.div continuous_id (by fun_prop)
    intro t
    positivity
  · apply tendsto_pi_nhds.mpr
    intro A
    by_cases hA : A.IsHermitian
    · exact matrixPseudoInverse_tendsto hA
    · simp only [matrixPseudoInverse, cfc_apply_of_not_predicate (R := ℝ) (p := IsSelfAdjoint) A hA]
      exact tendsto_const_nhds

theorem mul_matrixPseudoInverse {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    A * matrixPseudoInverse A = rangeProjection A := by
  rw [rangeProjection, ← matrix_cfc_mul, cfc_id' (p := IsSelfAdjoint) ℝ A hA]
  rfl

theorem matrixPseudoInverse_mul {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    matrixPseudoInverse A * A = rangeProjection A := by
  calc
    _ = cfc (fun t : ℝ => t⁻¹) A * cfc (fun t : ℝ => t) A := by rw [cfc_id' (p := IsSelfAdjoint) ℝ A hA]; rfl
    _ = cfc (fun t : ℝ => t⁻¹ * t) A := matrix_cfc_mul _ _ _
    _ = rangeProjection A := by simp only [rangeProjection, mul_comm]

theorem measurable_rangeProjection : Measurable (rangeProjection (d := d)) := by
  have he : rangeProjection (d := d) = fun A => A * matrixPseudoInverse A := by
    funext A
    by_cases hA : A.IsHermitian
    · exact (mul_matrixPseudoInverse hA).symm
    · simp [rangeProjection, matrixPseudoInverse, cfc_apply_of_not_predicate (R := ℝ) (p := IsSelfAdjoint) A hA]
  rw [he]
  exact measurable_id.mul measurable_matrixPseudoInverse

theorem rangeProjection_isSymm (A : Matrix (Fin d) (Fin d) ℝ) :
    (rangeProjection A).IsSymm :=
  Matrix.isHermitian_iff_isSymm.mp (cfc_predicate _ A)

theorem rangeProjection_idempotent (A : Matrix (Fin d) (Fin d) ℝ) :
    rangeProjection A * rangeProjection A = rangeProjection A := by
  rw [rangeProjection, matrix_cfc_mul]
  apply cfc_congr
  intro t _
  by_cases ht : t = 0 <;> simp [ht]

theorem rangeProjection_mul {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    rangeProjection A * A = A := by
  calc
    _ = cfc (fun t : ℝ => t * t⁻¹) A * cfc (fun t : ℝ => t) A := by rw [cfc_id' (p := IsSelfAdjoint) ℝ A hA]; rfl
    _ = cfc (fun t : ℝ => (t * t⁻¹) * t) A := matrix_cfc_mul _ _ _
    _ = cfc (fun t : ℝ => t) A := by
      apply cfc_congr
      intro t _
      by_cases ht : t = 0 <;> simp [ht]
    _ = A := cfc_id' (p := IsSelfAdjoint) ℝ A hA

end ErrorCalculus
