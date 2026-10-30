import GeometricMeasure.Matrix.WaveCone

/-!
# Ellipticity and the scalar wave cone of a fixed matrix

## Main results
The Euclidean operator norm, invertibility and the scalar wave cone describe the ellipticity of a
fixed matrix. The norm is connected to Mathlib's scoped L² operator norm.

Reference: De Philippis–Rindler, arXiv:1601.06543v2, p. 8 (iii).
-/

noncomputable section
open scoped Matrix
open WithLp
namespace GeometricMeasure
set_option autoImplicit false
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

/--
DPR pp. 8 and 15. The set of annihilating frequencies is {0} exactly when the determinant is
nonzero, even in dimension zero.
-/
theorem matrixDivergenceSymbol_zeroSet_iff (P : Matrix (Fin n) (Fin n) ℝ) :
    {ξ : EuclideanSpace ℝ (Fin n) | matrixDivergenceSymbol P ξ = 0} = {0} ↔
      P.det ≠ 0 := by
  constructor
  · intro h hd
    obtain ⟨ξ, hξ, hP⟩ := (mem_matrixDivergenceWaveCone_iff P).mpr hd
    have hm : ξ ∈ ({0} : Set (EuclideanSpace ℝ (Fin n))) := h ▸ hP
    exact hξ hm
  · intro hd
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, matrixDivergenceSymbol_eq_zero_iff]
    constructor
    · intro h
      have hi := matrixEuclideanCLM_inv_apply P hd ξ
      simpa [h] using hi.symm
    · rintro rfl
      exact map_zero _

/--
DPR pp. 8 and 15. Reformulation of the trivial frequency kernel as invertibility of the matrix.
-/
theorem matrixDivergenceSymbol_zeroSet_iff_isUnit (P : Matrix (Fin n) (Fin n) ℝ) :
    {ξ : EuclideanSpace ℝ (Fin n) | matrixDivergenceSymbol P ξ = 0} = {0} ↔
      IsUnit P := by
  rw [matrixDivergenceSymbol_zeroSet_iff, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]

/--
6, O3; supplement to DPR p. 8 (iii). Bound for all complex frequencies with the complex
operator constant, without identifying it with the real constant.
-/
theorem matrixComplexification_ellipticity [NeZero n]
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.det ≠ 0) :
    0 < matrixEllipticityConstant (matrixComplexification P) ∧
      ∀ ξ : EuclideanSpace ℂ (Fin n),
        matrixEllipticityConstant (matrixComplexification P) * ‖ξ‖ ≤
          ‖matrixEuclideanCLM (matrixComplexification P) ξ‖ := by
  have hd : (matrixComplexification P).det ≠ 0 := by
    rw [det_matrixComplexification]
    exact_mod_cast hP
  exact ⟨matrixEllipticityConstant_pos _ hd, matrix_elliptic_bound _ hd⟩

/--
6, O3; DPR p. 15. Matrix multiplication commutes with embedding a real matrix and a real frequency
into ℂ.
-/
theorem matrixEuclideanCLM_complexification (P : Matrix (Fin n) (Fin n) ℝ)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    matrixEuclideanCLM (matrixComplexification P) (euclideanComplexification ξ) =
      euclideanComplexification (matrixEuclideanCLM P ξ) := by
  ext i
  simp [matrixEuclideanCLM_apply, matrixComplexification, euclideanComplexification,
    Matrix.mulVec, dotProduct]

/--
DPR pp. 1 and 8. Cone of real scalar amplitudes of the frozen operator u ↦ P∇u; distinct from the
matrix cone and the frequency kernel.
-/
def frozenMatrixDivergenceWaveCone (P : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  {a | ∃ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 ∧
    (a : ℂ) • matrixDivergenceSymbol P ξ = 0}

/--
DPR pp. 1 and 8. In positive dimension, the frozen scalar cone equals {0} exactly for an invertible
matrix.
-/
theorem frozenMatrixDivergenceWaveCone_eq_singleton_iff [NeZero n]
    (P : Matrix (Fin n) (Fin n) ℝ) :
    frozenMatrixDivergenceWaveCone P = {0} ↔ P.det ≠ 0 := by
  constructor
  · intro h hd
    obtain ⟨ξ, hξ, hP⟩ := (mem_matrixDivergenceWaveCone_iff P).mpr hd
    have hm : (1 : ℝ) ∈ frozenMatrixDivergenceWaveCone P := ⟨ξ, hξ, by simp [hP]⟩
    rw [h] at hm
    norm_num at hm
  · intro hd
    ext a
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨ξ, hξ, ha⟩
      rcases smul_eq_zero.mp ha with ha | hP
      · exact Complex.ofReal_eq_zero.mp ha
      · have hz : ξ = 0 := by
          have hm : ξ ∈ ({0} : Set (EuclideanSpace ℝ (Fin n))) :=
            (matrixDivergenceSymbol_zeroSet_iff P).mpr hd ▸ hP
          exact hm
        exact (hξ hz).elim
    · rintro rfl
      obtain ⟨ξ, hξ⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
      exact ⟨ξ, hξ, by simp⟩

/--
7 supplement to DPR p. 8 (iii) (the converse is not stated by DPR). Quantitative characterization of
invertibility by a strictly positive constant in Euclidean norm.
-/
theorem matrix_det_ne_zero_iff_elliptic [NeZero n]
    (P : Matrix (Fin n) (Fin n) ℝ) :
    P.det ≠ 0 ↔ ∃ c : ℝ, 0 < c ∧ ∀ ξ : EuclideanSpace ℝ (Fin n),
      c * ‖ξ‖ ≤ ‖matrixEuclideanCLM P ξ‖ := by
  constructor
  · intro hd
    exact ⟨matrixEllipticityConstant P, matrixEllipticityConstant_pos P hd,
      matrix_elliptic_bound P hd⟩
  · rintro ⟨c, hc, h⟩ hd
    obtain ⟨ξ, hξ, hz⟩ := (mem_matrixDivergenceWaveCone_iff P).mpr hd
    have hle := h ξ
    rw [(matrixDivergenceSymbol_eq_zero_iff P ξ).mp hz, norm_zero] at hle
    exact (not_le_of_gt (mul_pos hc (norm_pos_iff.mpr hξ))) hle

end GeometricMeasure
