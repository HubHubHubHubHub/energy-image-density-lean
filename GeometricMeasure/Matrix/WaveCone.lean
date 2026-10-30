import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Wave Cone

## Main results
Row-wise matrix-divergence cone. Source: De Philippis–Rindler, arXiv:1601.06543v2, pp. 1, 7, 15.1,
5.3, 5.5. Algebraic content on Euclidean spaces; no dependency on measures or currents.
-/

noncomputable section
open scoped Matrix
open WithLp
namespace GeometricMeasure
set_option autoImplicit false
variable {n : ℕ}

/-- DPR p. 15. Entrywise embedding of a real matrix into ℂ. -/
def matrixComplexification (P : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℂ := P.map Complex.ofRealHom

/--
DPR p. 15. Nontrivial real kernel exactly for singular square matrices, including in dimension zero.
-/
theorem matrix_exists_real_kernel_iff (P : Matrix (Fin n) (Fin n) ℝ) :
    (∃ ξ : Fin n → ℝ, ξ ≠ 0 ∧ P *ᵥ ξ = 0) ↔ P.det = 0 :=
  Matrix.exists_mulVec_eq_zero_iff

/--
algebraic supplement to DPR p. 15. Nontrivial complex kernel exactly when the complex determinant is
zero.
-/
theorem matrix_exists_complex_kernel_iff (P : Matrix (Fin n) (Fin n) ℂ) :
    (∃ ξ : Fin n → ℂ, ξ ≠ 0 ∧ P *ᵥ ξ = 0) ↔ P.det = 0 :=
  Matrix.exists_mulVec_eq_zero_iff

/-- algebraic supplement to DPR p. 15. Embedding from ℝ into ℂ commutes with determinant. -/
theorem det_matrixComplexification (P : Matrix (Fin n) (Fin n) ℝ) :
    (matrixComplexification P).det = (P.det : ℂ) :=
  (Complex.ofRealHom.map_det P).symm

/--
DPR p. 15. For real coefficients only, existence of a nontrivial complex kernel is equivalent to
existence of a nontrivial real kernel.
-/
theorem matrix_complex_kernel_iff_real (P : Matrix (Fin n) (Fin n) ℝ) :
    (∃ ξ : Fin n → ℂ, ξ ≠ 0 ∧ matrixComplexification P *ᵥ ξ = 0) ↔
      ∃ ξ : Fin n → ℝ, ξ ≠ 0 ∧ P *ᵥ ξ = 0 := by
  rw [matrix_exists_complex_kernel_iff, det_matrixComplexification,
    matrix_exists_real_kernel_iff]
  exact Complex.ofReal_eq_zero

/-- DPR p. 15. Euclidean matrix action supplied by Mathlib, over ℝ or ℂ, with the ℓ² norm. -/
def matrixEuclideanCLM {𝕜 : Type*} [RCLike 𝕜]
    (P : Matrix (Fin n) (Fin n) 𝕜) :
    EuclideanSpace 𝕜 (Fin n) →L[𝕜] EuclideanSpace 𝕜 (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) P

/-- DPR p. 15. Expression of Euclidean action by matrix-vector multiplication in coordinates. -/
theorem matrixEuclideanCLM_apply {𝕜 : Type*} [RCLike 𝕜]
    (P : Matrix (Fin n) (Fin n) 𝕜) (ξ : EuclideanSpace 𝕜 (Fin n)) :
    matrixEuclideanCLM P ξ = toLp 2 (P *ᵥ ofLp ξ) := rfl

/-- DPR p. 15. Euclidean vanishing is equivalent to vanishing of the coordinate product. -/
theorem matrixEuclideanCLM_eq_zero_iff {𝕜 : Type*} [RCLike 𝕜]
    (P : Matrix (Fin n) (Fin n) 𝕜) (ξ : EuclideanSpace 𝕜 (Fin n)) :
    matrixEuclideanCLM P ξ = 0 ↔ P *ᵥ ofLp ξ = 0 := by
  change toLp 2 (P *ᵥ ofLp ξ) = toLp 2 0 ↔ _
  exact (WithLp.toLp_injective 2).eq_iff

/--
complex convention of DPR pp. 7 and 15. Coordinate embedding of real Euclidean frequencies into ℂ.
-/
def euclideanComplexification (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n) := toLp 2 (fun j => (ξ j : ℂ))

/-- DPR pp. 7 and 15. The real-to-complex Euclidean embedding reflects the zero vector. -/
theorem euclideanComplexification_eq_zero (ξ : EuclideanSpace ℝ (Fin n)) :
    euclideanComplexification ξ = 0 ↔ ξ = 0 := by
  constructor
  · intro h
    ext j
    have hj := congrArg (fun z : EuclideanSpace ℂ (Fin n) => z j) h
    simpa [euclideanComplexification] using hj
  · rintro rfl
    rfl

/-- DPR pp. 7 and 15. The real-to-complex embedding preserves the Euclidean norm exactly. -/
theorem norm_euclideanComplexification (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖euclideanComplexification ξ‖ = ‖ξ‖ := by
  simp [EuclideanSpace.norm_eq, euclideanComplexification]

/--
DPR pp. 7 and 15. Algebraic symbol of row-wise divergence with factor +2πi; no Fourier identity for
distributions is asserted.
-/
def matrixDivergenceSymbol (P : Matrix (Fin n) (Fin n) ℝ)
    (ξ : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  (((2 * Real.pi : ℝ) : ℂ) * Complex.I) •
    euclideanComplexification (matrixEuclideanCLM P ξ)

/-- DPR p. 15. Coordinate i of the symbol contracts row i with the real frequency. -/
theorem matrixDivergenceSymbol_apply (P : Matrix (Fin n) (Fin n) ℝ)
    (ξ : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    matrixDivergenceSymbol P ξ i =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((∑ j, P i j * ξ j : ℝ) : ℂ) := rfl

/-- DPR p. 15. The complex factor +2πi does not change the annihilating frequencies. -/
theorem matrixDivergenceSymbol_eq_zero_iff (P : Matrix (Fin n) (Fin n) ℝ)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    matrixDivergenceSymbol P ξ = 0 ↔ matrixEuclideanCLM P ξ = 0 := by
  rw [matrixDivergenceSymbol, smul_eq_zero]
  have h : ((2 * Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast (mul_pos (by norm_num) Real.pi_pos).ne')
      Complex.I_ne_zero
  simp only [h, false_or, euclideanComplexification_eq_zero]

/-- DPR pp. 8 and 15. Euclidean norm of the symbol: positive real factor 2π times the norm of Pξ. -/
theorem norm_matrixDivergenceSymbol (P : Matrix (Fin n) (Fin n) ℝ)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖matrixDivergenceSymbol P ξ‖ = (2 * Real.pi) * ‖matrixEuclideanCLM P ξ‖ := by
  simp [matrixDivergenceSymbol, norm_smul, norm_euclideanComplexification,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/--
DPR pp. 1 and 15. Set of matrices admitting a nonzero annihilating real frequency, independent of
any fixed polar.
-/
def matrixDivergenceWaveCone (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {P | ∃ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 ∧ matrixDivergenceSymbol P ξ = 0}

/--
DPR p. 15. The row-wise divergence cone is characterized by zero determinant, in every dimension.
-/
theorem mem_matrixDivergenceWaveCone_iff (P : Matrix (Fin n) (Fin n) ℝ) :
    P ∈ matrixDivergenceWaveCone n ↔ P.det = 0 := by
  rw [← matrix_exists_real_kernel_iff]
  constructor
  · rintro ⟨ξ, hξ, hP⟩
    refine ⟨ofLp ξ, ?_, ?_⟩
    · intro hz
      apply hξ
      exact (WithLp.ofLp_injective 2) hz
    · exact (matrixEuclideanCLM_eq_zero_iff P ξ).mp
        ((matrixDivergenceSymbol_eq_zero_iff P ξ).mp hP)
  · rintro ⟨ξ, hξ, hP⟩
    refine ⟨toLp 2 ξ, ?_, ?_⟩
    · intro hz
      exact hξ (congrArg (ofLp (p := 2)) hz)
    · apply (matrixDivergenceSymbol_eq_zero_iff P _).mpr
      exact (matrixEuclideanCLM_eq_zero_iff P _).mpr hP

/--
DPR p. 15. Set equality with the cone of singular square matrices; no measure structure conclusion.
-/
theorem matrixDivergenceWaveCone_eq (n : ℕ) :
    matrixDivergenceWaveCone n = {P : Matrix (Fin n) (Fin n) ℝ | P.det = 0} := by
  ext P
  exact mem_matrixDivergenceWaveCone_iff P

/-- DPR p. 1. Exact equivalence between nonzero frequencies and unit-norm frequencies. -/
theorem matrixDivergenceWaveCone_iff_unit (P : Matrix (Fin n) (Fin n) ℝ) :
    P ∈ matrixDivergenceWaveCone n ↔
      ∃ ξ : EuclideanSpace ℝ (Fin n), ‖ξ‖ = 1 ∧ matrixDivergenceSymbol P ξ = 0 := by
  constructor
  · rintro ⟨ξ, hξ, hP⟩
    refine ⟨‖ξ‖⁻¹ • ξ, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]
    · apply (matrixDivergenceSymbol_eq_zero_iff P _).mpr
      rw [map_smul, (matrixDivergenceSymbol_eq_zero_iff P ξ).mp hP, smul_zero]
  · rintro ⟨ξ, hξ, hP⟩
    refine ⟨ξ, ?_, hP⟩
    intro hz
    simp [hz] at hξ

/-- 5, O2; DPR p. 7. Homogeneity of the embedding for every real scalar, including zero. -/
theorem euclideanComplexification_smul (a : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    euclideanComplexification (a • ξ) = (a : ℂ) • euclideanComplexification ξ := by
  ext j
  simp [euclideanComplexification]

/-- 5, O2; DPR pp. 7 and 15. Real homogeneity of the symbol in frequency, with P fixed. -/
theorem matrixDivergenceSymbol_smul (P : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    matrixDivergenceSymbol P (a • ξ) = (a : ℂ) • matrixDivergenceSymbol P ξ := by
  unfold matrixDivergenceSymbol
  rw [map_smul, euclideanComplexification_smul, smul_comm]

/--
5, O2; supplement to DPR p. 7. Continuity of the embedding between real and complex Euclidean
spaces.
-/
theorem continuous_euclideanComplexification :
    Continuous (euclideanComplexification : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun j =>
    Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ j)))

/--
5, O2; DPR pp. 7 and 15. Continuity in real frequency for a fixed matrix, without a claim about a
spatial polar.
-/
theorem continuous_matrixDivergenceSymbol (P : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (matrixDivergenceSymbol P) :=
  (continuous_euclideanComplexification.comp (matrixEuclideanCLM P).continuous).const_smul
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I)

end GeometricMeasure
