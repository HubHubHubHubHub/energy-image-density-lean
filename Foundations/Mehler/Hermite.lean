import Foundations.Mehler.Kernel
import Foundations.Hermite.Recurrence

noncomputable section
open Filter Topology Set MeasureTheory Polynomial
open scoped InnerProductSpace
namespace Foundations

def gaussianAffineIntegral (a b x : ℝ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := gaussianPolynomialIntegral (p.comp (C (a*x)+C b*X))
  map_add' p q := by simp [add_comp]
  map_smul' c p := by simp [smul_comp]

theorem gaussianAffineIntegral_apply (a b x : ℝ) (p : ℝ[X]) :
    gaussianAffineIntegral a b x p = ∫ y, p.eval (a*x+b*y) ∂standardGaussian := by
  simp [gaussianAffineIntegral, gaussianPolynomialIntegral, eval_comp]

@[simp] theorem gaussianAffineIntegral_one (a b x : ℝ) :
    gaussianAffineIntegral a b x 1 = 1 := by
  simp [gaussianAffineIntegral_apply]

theorem gaussianAffineIntegral_X_mul (a b x : ℝ) (p : ℝ[X]) :
    gaussianAffineIntegral a b x (X*p) = a*x * gaussianAffineIntegral a b x p +
      b^2 * gaussianAffineIntegral a b x p.derivative := by
  let q : ℝ[X] := C (a*x)+C b*X
  have hd : (p.comp q).derivative = b • (p.derivative.comp q) := by
    rw [derivative_comp]
    simp only [q, derivative_add, derivative_C, derivative_mul, derivative_X,
      zero_mul, mul_one, zero_add, smul_eq_C_mul]
  have he : q*(p.comp q) = (a*x) • (p.comp q) + b • (X*(p.comp q)) := by
    simp only [q, smul_eq_C_mul]
    ring
  change gaussianPolynomialIntegral ((X*p).comp q) =
    a*x * gaussianPolynomialIntegral (p.comp q) + b^2 * gaussianPolynomialIntegral (p.derivative.comp q)
  rw [mul_comp, X_comp, he, map_add, map_smul, map_smul,
    ← gaussianPolynomialIntegral_derivative, hd, map_smul]
  simp only [smul_eq_mul]
  ring

/--
Polynomial integration by parts gives the Hermite eigenvalue identity without an analytic generating
function.
-/
theorem gaussianAffineIntegral_hermite {a b : ℝ} (hab : a^2+b^2=1) (n : ℕ) (x : ℝ) :
    gaussianAffineIntegral a b x (hermitePolynomial n) = a^n * hermiteFun n x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hermiteFun]
  | one =>
    rw [hermitePolynomial_succ, map_sub, gaussianAffineIntegral_X_mul]
    simp [hermiteFun, hermitePolynomial_succ]
  | more n ih ih' =>
    rw [hermitePolynomial_succ (n+1), map_sub, gaussianAffineIntegral_X_mul,
      derivative_hermitePolynomial n, ← smul_eq_C_mul, map_smul, ih, ih']
    simp only [smul_eq_mul]
    have he : hermiteFun (n+2) x = x * hermiteFun (n+1) x -
        (n+1 : ℕ) * hermiteFun n x := by linarith [hermiteFun_three_term n x]
    rw [he, show b^2 = 1-a^2 by linarith, pow_succ, pow_succ]
    ring

theorem mehlerKernel_hermite {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (x : ℝ) :
    mehlerKernel t (hermiteFun n) x = Real.exp (-(n:ℝ)*t) * hermiteFun n x := by
  have h := gaussianAffineIntegral_hermite (mehlerCoeff_sq ht) n x
  rw [gaussianAffineIntegral_apply] at h
  have he : mehlerCoeffA t ^ n = Real.exp (-(n:ℝ)*t) := by
    rw [mehlerCoeffA, ← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [he, mehlerKernel, hermiteFun] using h

theorem mehler_hermite {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    mehler t (hermiteLp n) = Real.exp (-(n:ℝ)*t) • hermiteLp n := by
  apply Lp.ext
  filter_upwards [coe_mehler_toLp ht (memLp_polynomial_gaussian (hermitePolynomial n)),
    Lp.coeFn_smul (Real.exp (-(n:ℝ)*t)) (hermiteLp n), coe_polynomialLp (hermitePolynomial n)]
    with x hx hy hz
  change mehler t (hermiteLp n) x = _ at hx ⊢
  rw [hx, hy]
  change hermiteLp n x = hermiteFun n x at hz
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hz]
  exact mehlerKernel_hermite ht n x

theorem mehler_hermiteNormalized {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    mehler t (hermiteNormalized n) = Real.exp (-(n:ℝ)*t) • hermiteNormalized n := by
  rw [hermiteNormalized, map_smul, mehler_hermite ht]
  exact smul_comm _ _ _

end Foundations
