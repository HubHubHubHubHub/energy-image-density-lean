import Foundations.Hermite.Polynomial

noncomputable section
open Polynomial
namespace Foundations

theorem derivative_hermitePolynomial (n : ℕ) :
    (hermitePolynomial (n+1)).derivative = C ((n+1 : ℕ) : ℝ) * hermitePolynomial n := by
  induction n with
  | zero => simp [hermitePolynomial_succ]
  | succ n ih =>
    rw [hermitePolynomial_succ, derivative_sub, derivative_mul, derivative_X, one_mul,
      ih, derivative_mul, derivative_C, zero_mul, zero_add, hermitePolynomial_succ n]
    push_cast
    simp only [map_add, map_one]
    ring

theorem hermitePolynomial_three_term (n : ℕ) :
    X * hermitePolynomial (n+1) = hermitePolynomial (n+2) +
      C ((n+1 : ℕ) : ℝ) * hermitePolynomial n := by
  rw [hermitePolynomial_succ (n+1), derivative_hermitePolynomial]
  ring

theorem hasDerivAt_hermiteFun (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteFun (n+1)) ((n+1 : ℕ) * hermiteFun n x) x := by
  change HasDerivAt (fun y => (hermitePolynomial (n+1)).eval y)
    ((n+1 : ℕ) * hermiteFun n x) x
  simpa [hermiteFun, derivative_hermitePolynomial] using (hermitePolynomial (n+1)).hasDerivAt x

theorem hermiteFun_three_term (n : ℕ) (x : ℝ) :
    x * hermiteFun (n+1) x = hermiteFun (n+2) x + (n+1 : ℕ) * hermiteFun n x := by
  have h := congrArg (fun p : ℝ[X] => p.eval x) (hermitePolynomial_three_term n)
  simpa [hermiteFun] using h

end Foundations
