import Foundations.Hermite.Orthogonality

noncomputable section
open Filter Topology Set MeasureTheory Polynomial
open scoped InnerProductSpace
namespace Foundations

def polynomialPairing (f : Lp ℝ 2 standardGaussian) : ℝ[X] →ₗ[ℝ] ℝ :=
  (innerSL ℝ f).toLinearMap.comp polynomialLpLinear

theorem polynomialPairing_apply (f : Lp ℝ 2 standardGaussian) (p : ℝ[X]) :
    polynomialPairing f p = ∫ x, f x * p.eval x ∂standardGaussian := by
  change ⟪f, polynomialLp p⟫_ℝ = _
  exact inner_polynomialLp f p

theorem hermite_inner_eq_zero_iff_moments (f : Lp ℝ 2 standardGaussian) :
    (∀ n, ⟪f, hermiteLp n⟫_ℝ = 0) ↔ (∀ n : ℕ, ∫ x, f x * x^n ∂standardGaussian = 0) := by
  constructor
  · intro h n
    have hk : Submodule.span ℝ (range hermitePolynomial) ≤ LinearMap.ker (polynomialPairing f) := by
      apply Submodule.span_le.mpr
      rintro p ⟨k,rfl⟩
      exact h k
    have hp : X^n ∈ LinearMap.ker (polynomialPairing f) := hk (by rw [span_hermitePolynomial]; trivial)
    have he := LinearMap.mem_ker.mp hp
    rw [polynomialPairing_apply] at he
    simpa only [eval_pow, eval_X] using he
  · intro h
    have hX (n : ℕ) : polynomialPairing f (X^n) = 0 := by
      rw [polynomialPairing_apply]
      simpa only [eval_pow, eval_X] using h n
    have hp (p : ℝ[X]) : polynomialPairing f p = 0 := by
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp [map_add, hp, hq]
      | monomial n a =>
        rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, hX, smul_zero]
    intro n
    exact hp (hermitePolynomial n)

theorem span_hermiteLp_eq_polynomial_range :
    Submodule.span ℝ (range hermiteLp) = LinearMap.range polynomialLpLinear := by
  have h := congrArg (Submodule.map polynomialLpLinear) span_hermitePolynomial
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp] at h
  exact h

theorem span_hermiteNormalized_eq :
    Submodule.span ℝ (range hermiteNormalized) = Submodule.span ℝ (range hermiteLp) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨n,rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro x ⟨n,rfl⟩
    have h := (Submodule.span ℝ (range hermiteNormalized)).smul_mem
      (Real.sqrt (n.factorial : ℝ)) (Submodule.subset_span (mem_range_self n))
    have hn : Real.sqrt (n.factorial : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos n))).ne'
    change hermiteLp n ∈ Submodule.span ℝ (range hermiteNormalized)
    simpa only [hermiteNormalized, smul_smul, mul_inv_cancel₀ hn, one_smul] using h

theorem span_hermiteLp_le_eq_polynomial_image (n : ℕ) :
    Submodule.span ℝ (hermiteLp '' Iic n) = (Polynomial.degreeLE ℝ n).map polynomialLpLinear := by
  have h := congrArg (Submodule.map polynomialLpLinear) (span_hermite_eq_polynomials n)
  rw [Submodule.map_span, ← Set.image_comp] at h
  exact h

end Foundations
