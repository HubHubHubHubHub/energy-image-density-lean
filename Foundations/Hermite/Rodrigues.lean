import Foundations.Hermite.Polynomial
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
open Filter Topology Set MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal
namespace Foundations

theorem gaussianDensity_eq (x : ℝ) : gaussianPDFReal 0 1 x =
    (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(x^2/2)) := by
  simp [gaussianPDFReal, neg_div]

theorem hermite_rodrigues (n : ℕ) (x : ℝ) :
    deriv^[n] (gaussianPDFReal 0 1) x = (-1:ℝ)^n * hermiteFun n x * gaussianPDFReal 0 1 x := by
  have he : gaussianPDFReal 0 1 = fun x => (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(x^2/2)) :=
    funext gaussianDensity_eq
  rw [← iteratedDeriv_eq_iterate, he, iteratedDeriv_const_mul_field,
    iteratedDeriv_eq_iterate, Polynomial.deriv_gaussian_eq_hermite_mul_gaussian,
    hermiteFun_eq_aeval]
  ring

theorem hasDerivAt_gaussianDensity (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hd : HasDerivAt (fun y : ℝ => -(y^2/2)) (-x) x := by
    apply ((((hasDerivAt_id x).pow 2).div_const 2).neg).congr_deriv
    dsimp
    ring
  have h := hd.exp.const_mul (Real.sqrt (2*Real.pi))⁻¹
  have he : gaussianPDFReal 0 1 = fun y => (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(y^2/2)) := funext gaussianDensity_eq
  rw [he]
  apply h.congr_deriv
  ring

theorem integrable_polynomial_mul_density (p : ℝ[X]) :
    Integrable (fun x => p.eval x * gaussianPDFReal 0 1 x) := by
  have hp := integrable_polynomial_gaussian p
  rw [standardGaussian, gaussianReal_of_var_ne_zero _ (one_ne_zero : (1:ℝ≥0)≠0)] at hp
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (ae_of_all _ fun x => gaussianPDF_lt_top) ).mp hp
  simpa only [toReal_gaussianPDF, smul_eq_mul, mul_comm] using h

theorem hasDerivAt_polynomial_mul_density (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => p.eval y * gaussianPDFReal 0 1 y)
      ((p.derivative - X*p).eval x * gaussianPDFReal 0 1 x) x := by
  apply ((p.hasDerivAt x).mul (hasDerivAt_gaussianDensity x)).congr_deriv
  simp only [eval_sub, eval_mul, eval_X]
  ring

theorem tendsto_polynomial_mul_density_atTop (p : ℝ[X]) :
    Tendsto (fun x => p.eval x * gaussianPDFReal 0 1 x) atTop (𝓝 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (fun x _ => hasDerivAt_polynomial_mul_density p x)
    (integrable_polynomial_mul_density _).integrableOn
    (integrable_polynomial_mul_density p).integrableOn

theorem tendsto_polynomial_mul_density_atBot (p : ℝ[X]) :
    Tendsto (fun x => p.eval x * gaussianPDFReal 0 1 x) atBot (𝓝 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
    (fun x _ => hasDerivAt_polynomial_mul_density p x)
    (integrable_polynomial_mul_density _).integrableOn
    (integrable_polynomial_mul_density p).integrableOn

def gaussianPolynomialIntegral : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x, p.eval x ∂standardGaussian
  map_add' p q := by
    simp only [eval_add]
    exact integral_add (integrable_polynomial_gaussian p) (integrable_polynomial_gaussian q)
  map_smul' a p := by simp [integral_const_mul]

theorem gaussianPolynomialIntegral_density (p : ℝ[X]) :
    gaussianPolynomialIntegral p = ∫ x, p.eval x * gaussianPDFReal 0 1 x := by
  change (∫ x, p.eval x ∂standardGaussian) = _
  simpa only [standardGaussian, smul_eq_mul, mul_comm] using
    (integral_gaussianReal_eq_integral_smul (f := p.eval) (one_ne_zero : (1:ℝ≥0)≠0))

/-- Gaussian integration by parts; both boundary limits vanish. -/
theorem gaussianPolynomialIntegral_derivative (p : ℝ[X]) :
    gaussianPolynomialIntegral p.derivative = gaussianPolynomialIntegral (X*p) := by
  have h := integral_of_hasDerivAt_of_tendsto (fun x => hasDerivAt_polynomial_mul_density p x)
    (integrable_polynomial_mul_density _) (tendsto_polynomial_mul_density_atBot p)
    (tendsto_polynomial_mul_density_atTop p)
  rw [← gaussianPolynomialIntegral_density, map_sub] at h
  exact sub_eq_zero.mp (by simpa using h)

/-- Repeated integration by parts in polynomial form. -/
theorem gaussianPolynomialIntegral_mul_hermite (p : ℝ[X]) (n : ℕ) :
    gaussianPolynomialIntegral (p * hermitePolynomial n) =
      gaussianPolynomialIntegral (Polynomial.derivative^[n] p) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    have he : p * hermitePolynomial (n+1) =
        X * (p * hermitePolynomial n) - (p * hermitePolynomial n).derivative +
        p.derivative * hermitePolynomial n := by
      rw [hermitePolynomial_succ, derivative_mul]; ring
    rw [he, map_add, map_sub, ← gaussianPolynomialIntegral_derivative, sub_self, zero_add, ih,
      Function.iterate_succ_apply]

/-- The iterated integration-by-parts identity for derivatives of the normalized density. -/
theorem integral_polynomial_mul_deriv_gaussian (p : ℝ[X]) (n : ℕ) :
    (∫ x, p.eval x * deriv^[n] (gaussianPDFReal 0 1) x) =
      (-1:ℝ)^n * ∫ x, (Polynomial.derivative^[n] p).eval x * gaussianPDFReal 0 1 x := by
  simp_rw [hermite_rodrigues]
  have he (x : ℝ) : p.eval x * ((-1:ℝ)^n * hermiteFun n x * gaussianPDFReal 0 1 x) =
      (-1:ℝ)^n * ((p * hermitePolynomial n).eval x * gaussianPDFReal 0 1 x) := by
    simp only [eval_mul, hermiteFun]; ring
  simp_rw [he]
  rw [integral_const_mul, ← gaussianPolynomialIntegral_density,
    gaussianPolynomialIntegral_mul_hermite, gaussianPolynomialIntegral_density]

end Foundations
