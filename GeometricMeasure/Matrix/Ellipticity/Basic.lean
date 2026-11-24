import GeometricMeasure.Matrix.WaveCone

/-!
# Ellipticity and the scalar wave cone of a fixed matrix

This file contains the definitions and results of the development of
`GeometricMeasure.Matrix.Ellipticity` that the main statements of the library (the head theorems
listed in the README of the repository) use, together with the basic API of their definitions.
`GeometricMeasure.Matrix.Ellipticity` imports it and continues the development.

## Main definitions

* `matrixEllipticityConstant`: Totalized inverse of the Euclidean operator norm of P⁻¹; equals zero
  in dimension zero.

## Main statements

* `matrixDivergence_ellipticity_of_not_mem`: Algebraic package for a fixed matrix outside the cone:
  nonzero determinant, positive constant and two lower bounds; no analytic freezing of the polar.

## References

Reference: De Philippis–Rindler, arXiv:1601.06543v2, p. 8 (iii).
-/
noncomputable section
open scoped Matrix
open WithLp
namespace GeometricMeasure
variable {n : ℕ}

/--
algebraic justification of DPR p. 8 (iii). The matrix inverse acts on the left of P when det P ≠ 0,
over ℝ or ℂ.
-/
theorem matrixEuclideanCLM_inv_apply {𝕜 : Type*} [RCLike 𝕜]
    (P : Matrix (Fin n) (Fin n) 𝕜) (hP : P.det ≠ 0)
    (ξ : EuclideanSpace 𝕜 (Fin n)) :
    matrixEuclideanCLM P⁻¹ (matrixEuclideanCLM P ξ) = ξ := by
  apply (WithLp.ofLp_injective 2)
  change P⁻¹ *ᵥ (P *ᵥ ofLp ξ) = ofLp ξ
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hP),
    Matrix.one_mulVec]

/--
justification of DPR p. 8 (iii). Frequency bound by the Euclidean operator norm of the inverse.
-/
theorem matrix_norm_le_inv_norm_mul {𝕜 : Type*} [RCLike 𝕜]
    (P : Matrix (Fin n) (Fin n) 𝕜) (hP : P.det ≠ 0)
    (ξ : EuclideanSpace 𝕜 (Fin n)) :
    ‖ξ‖ ≤ ‖matrixEuclideanCLM P⁻¹‖ * ‖matrixEuclideanCLM P ξ‖ := by
  calc
    ‖ξ‖ = ‖matrixEuclideanCLM P⁻¹ (matrixEuclideanCLM P ξ)‖ :=
      congrArg norm (matrixEuclideanCLM_inv_apply P hP ξ).symm
    _ ≤ _ := (matrixEuclideanCLM P⁻¹).le_opNorm _

/--
explicit constant for DPR p. 8 (iii). Totalized inverse of the Euclidean operator norm of P⁻¹;
equals zero in dimension zero.
-/
def matrixEllipticityConstant {𝕜 : Type*} [RCLike 𝕜]
    (P : Matrix (Fin n) (Fin n) 𝕜) : ℝ := ‖matrixEuclideanCLM P⁻¹‖⁻¹

open scoped Matrix.Norms.L2Operator in
/--
The norm used in De Philippis–Rindler, p. 8 (iii). Definitional bridge to Mathlib's scoped L²
operator norm, over ℝ or ℂ and in every dimension.
-/
theorem matrixEllipticityConstant_eq_l2 {𝕜 : Type*} [RCLike 𝕜]
    (P : Matrix (Fin n) (Fin n) 𝕜) :
    matrixEllipticityConstant P = ‖P⁻¹‖⁻¹ := rfl

/--
DPR p. 8 (iii). Positivity of the explicit constant for an invertible matrix in strictly positive
dimension.
-/
theorem matrixEllipticityConstant_pos {𝕜 : Type*} [RCLike 𝕜] [NeZero n]
    (P : Matrix (Fin n) (Fin n) 𝕜) (hP : P.det ≠ 0) :
    0 < matrixEllipticityConstant P := by
  apply inv_pos.mpr
  apply norm_pos_iff.mpr
  intro hz
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : EuclideanSpace 𝕜 (Fin n))
  apply hξ
  have h := matrixEuclideanCLM_inv_apply P hP ξ
  rw [hz] at h
  exact h.symm

/--
DPR p. 8 (iii). Explicit lower bound on the Euclidean action of an invertible matrix over ℝ or ℂ, in
positive dimension.
-/
theorem matrix_elliptic_bound {𝕜 : Type*} [RCLike 𝕜] [NeZero n]
    (P : Matrix (Fin n) (Fin n) 𝕜) (hP : P.det ≠ 0)
    (ξ : EuclideanSpace 𝕜 (Fin n)) :
    matrixEllipticityConstant P * ‖ξ‖ ≤ ‖matrixEuclideanCLM P ξ‖ := by
  have hp : 0 < ‖matrixEuclideanCLM P⁻¹‖ :=
    inv_pos.mp (matrixEllipticityConstant_pos P hP)
  exact (inv_mul_le_iff₀ hp).mpr (matrix_norm_le_inv_norm_mul P hP ξ)

/--
DPR p. 8 (iii). Lower bound on the symbol by 2π times the inverse constant, with real frequency and
complex values.
-/
theorem matrixDivergenceSymbol_elliptic_bound [NeZero n]
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.det ≠ 0)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    (2 * Real.pi * matrixEllipticityConstant P) * ‖ξ‖ ≤
      ‖matrixDivergenceSymbol P ξ‖ := by
  rw [norm_matrixDivergenceSymbol, mul_assoc]
  exact mul_le_mul_of_nonneg_left (matrix_elliptic_bound P hP ξ)
    (le_of_lt (mul_pos (by norm_num) Real.pi_pos))

/--
DPR p. 8 (iii). Algebraic package for a fixed matrix outside the cone: nonzero determinant,
positive constant and two lower bounds; no analytic freezing of the polar.
-/
theorem matrixDivergence_ellipticity_of_not_mem [NeZero n] (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∉ matrixDivergenceWaveCone n) :
    P.det ≠ 0 ∧ 0 < matrixEllipticityConstant P ∧
      (∀ ξ : EuclideanSpace ℝ (Fin n),
        matrixEllipticityConstant P * ‖ξ‖ ≤ ‖matrixEuclideanCLM P ξ‖) ∧
      (∀ ξ : EuclideanSpace ℝ (Fin n),
        (2 * Real.pi * matrixEllipticityConstant P) * ‖ξ‖ ≤
          ‖matrixDivergenceSymbol P ξ‖) := by
  have hd : P.det ≠ 0 := fun h => hP ((mem_matrixDivergenceWaveCone_iff P).mpr h)
  exact ⟨hd, matrixEllipticityConstant_pos P hd,
    matrix_elliptic_bound P hd, matrixDivergenceSymbol_elliptic_bound P hd⟩

end GeometricMeasure
