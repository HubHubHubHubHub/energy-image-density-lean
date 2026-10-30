import Foundations.Hermite.Rodrigues
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
open Filter Topology Set MeasureTheory ProbabilityTheory Polynomial
open scoped InnerProductSpace
namespace Foundations

theorem iterate_derivative_hermite_self (n : ℕ) :
    Polynomial.derivative^[n] (hermitePolynomial n) = C (n.factorial : ℝ) := by
  ext k
  rw [coeff_iterate_derivative]
  by_cases hk : k = 0
  · subst k
    simp only [zero_add, Nat.descFactorial_self, coeff_C_zero]
    have hc : (hermitePolynomial n).leadingCoeff = 1 := hermitePolynomial_monic n
    rw [← coeff_natDegree, natDegree_hermitePolynomial] at hc
    rw [hc]
    simp
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_hermitePolynomial]; omega), smul_zero,
      coeff_C, if_neg hk]

theorem integral_hermite_mul_hermite (m n : ℕ) :
    (∫ x, hermiteFun m x * hermiteFun n x ∂standardGaussian) =
      if m = n then (n.factorial : ℝ) else 0 := by
  have he : (fun x => hermiteFun m x * hermiteFun n x) =
      (fun x => (hermitePolynomial m * hermitePolynomial n).eval x) := by
    ext x; simp [hermiteFun]
  rw [he]
  change gaussianPolynomialIntegral (hermitePolynomial m * hermitePolynomial n) = _
  rcases lt_trichotomy m n with h | rfl | h
  · rw [if_neg (ne_of_lt h), gaussianPolynomialIntegral_mul_hermite,
      iterate_derivative_eq_zero (by simpa using h), map_zero]
  · rw [if_pos rfl, gaussianPolynomialIntegral_mul_hermite, iterate_derivative_hermite_self]
    simp [gaussianPolynomialIntegral]
  · rw [if_neg (ne_of_gt h), mul_comm, gaussianPolynomialIntegral_mul_hermite,
      iterate_derivative_eq_zero (by simpa using h), map_zero]

def polynomialLp (p : ℝ[X]) : Lp ℝ 2 standardGaussian :=
  (memLp_polynomial_gaussian p).toLp p.eval

theorem coe_polynomialLp (p : ℝ[X]) : polynomialLp p =ᵐ[standardGaussian] p.eval :=
  (memLp_polynomial_gaussian p).coeFn_toLp

def polynomialLpLinear : ℝ[X] →ₗ[ℝ] Lp ℝ 2 standardGaussian where
  toFun := polynomialLp
  map_add' p q := by
    unfold polynomialLp
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact ae_of_all _ fun x => by simp
  map_smul' a p := by
    apply Lp.ext
    filter_upwards [coe_polynomialLp (a • p), coe_polynomialLp p,
      Lp.coeFn_smul a (polynomialLp p)] with x hap hp hs
    simp [hs, hap, hp]

def hermiteLp (n : ℕ) : Lp ℝ 2 standardGaussian := polynomialLp (hermitePolynomial n)
def hermiteNormalized (n : ℕ) : Lp ℝ 2 standardGaussian :=
  (Real.sqrt (n.factorial : ℝ))⁻¹ • hermiteLp n

theorem inner_polynomialLp (f : Lp ℝ 2 standardGaussian) (p : ℝ[X]) :
    ⟪f, polynomialLp p⟫_ℝ = ∫ x, f x * p.eval x ∂standardGaussian := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_polynomialLp p] with x hx
  simp [hx, mul_comm]

theorem inner_hermiteLp (m n : ℕ) :
    ⟪hermiteLp m, hermiteLp n⟫_ℝ = if m=n then (n.factorial : ℝ) else 0 := by
  change ⟪polynomialLp (hermitePolynomial m), polynomialLp (hermitePolynomial n)⟫_ℝ = _
  rw [inner_polynomialLp]
  convert integral_hermite_mul_hermite m n using 1
  apply integral_congr_ae
  filter_upwards [coe_polynomialLp (hermitePolynomial m)] with x hx
  simp [hx, hermiteFun]

theorem orthonormal_hermiteNormalized : Orthonormal ℝ hermiteNormalized := by
  rw [orthonormal_iff_ite]
  intro m n
  simp only [hermiteNormalized, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    inner_hermiteLp]
  by_cases h : m=n
  · subst m
    rw [if_pos rfl, if_pos rfl]
    have hn : (0:ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
    have hs := Real.sq_sqrt hn.le
    have hp := Real.sqrt_pos.mpr hn
    field_simp
    nlinarith
  · simp [h]

end Foundations
