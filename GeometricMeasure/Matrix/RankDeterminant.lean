import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Real.Basic

/-!
# Rank and determinant of a real square matrix

## Main results
For every size n, rank P < n is equivalent to det P = 0. Under positive dimension, rank P ≤ n − 1 is
equivalent to the same condition. These algebraic equivalences convert the determinant description
of the matrix divergence wave cone into its rank form.

Reference: De Philippis–Rindler, arXiv p. 15, proof of Corollary 1.13, Λ_𝒜 = {rank ≤ d − 1}. The
proofs use Mathlib's matrix rank and determinant theory.
-/

noncomputable section
set_option autoImplicit false
namespace GeometricMeasure
variable {n : ℕ}

/--
DPR arXiv p. 15 (proof of Corollary 1.13). A real square matrix has rank strictly less than its
size if and only if its determinant is zero (every size, including n = 0, where both sides are
false).
-/
theorem matrix_rank_lt_iff_det_eq_zero (P : Matrix (Fin n) (Fin n) ℝ) :
    P.rank < n ↔ P.det = 0 := by
  constructor
  · intro h
    by_contra hd
    have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr hd)
    have hr := Matrix.rank_of_isUnit P hu
    rw [Fintype.card_fin] at hr
    omega
  · intro h
    obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    have hker : LinearMap.ker P.mulVecLin ≠ ⊥ := by
      intro hb
      apply hv
      have hm : v ∈ LinearMap.ker P.mulVecLin := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        exact hPv
      rw [hb] at hm
      exact (Submodule.mem_bot ℝ).mp hm
    have hpos : 0 < Module.finrank ℝ (LinearMap.ker P.mulVecLin) := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact hker (Submodule.finrank_eq_zero.mp h0)
    have hrn := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
    rw [Module.finrank_fin_fun] at hrn
    unfold Matrix.rank
    omega

/--
DPR arXiv p. 15. Printed form: rank ≤ n − 1 if and only if det = 0, for n ≥ 1 (in size zero, the
rank is zero and the determinant is one).
-/
theorem matrix_rank_le_pred_iff_det_eq_zero [NeZero n] (P : Matrix (Fin n) (Fin n) ℝ) :
    P.rank ≤ n - 1 ↔ P.det = 0 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [← matrix_rank_lt_iff_det_eq_zero]
  omega

end GeometricMeasure
