import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open Filter Topology Set MeasureTheory ProbabilityTheory Polynomial
namespace Foundations

abbrev standardGaussian : Measure ℝ := gaussianReal 0 1

def hermitePolynomial (n : ℕ) : ℝ[X] := (Polynomial.hermite n).map (Int.castRingHom ℝ)
def hermiteFun (n : ℕ) (x : ℝ) : ℝ := (hermitePolynomial n).eval x

theorem hermiteFun_eq_aeval (n : ℕ) (x : ℝ) :
    hermiteFun n x = aeval x (Polynomial.hermite n) := by
  simp [hermiteFun, hermitePolynomial, aeval_def, eval_map]

theorem hermitePolynomial_monic (n : ℕ) : (hermitePolynomial n).Monic :=
  (Polynomial.hermite_monic n).map _

@[simp] theorem natDegree_hermitePolynomial (n : ℕ) : (hermitePolynomial n).natDegree = n := by
  rw [hermitePolynomial, (Polynomial.hermite_monic n).natDegree_map]
  exact Polynomial.natDegree_hermite

@[simp] theorem degree_hermitePolynomial (n : ℕ) : (hermitePolynomial n).degree = n := by
  rw [degree_eq_natDegree (hermitePolynomial_monic n).ne_zero, natDegree_hermitePolynomial]

@[simp] theorem hermitePolynomial_zero : hermitePolynomial 0 = 1 := by
  simp [hermitePolynomial]

theorem hermitePolynomial_succ (n : ℕ) :
    hermitePolynomial (n+1) = X * hermitePolynomial n - (hermitePolynomial n).derivative := by
  simp [hermitePolynomial, Polynomial.derivative_map]

def hermiteSequence : Polynomial.Sequence ℝ where
  elems' := hermitePolynomial
  degree_eq' := degree_hermitePolynomial

theorem span_hermite_eq_polynomials (n : ℕ) :
    Submodule.span ℝ (hermitePolynomial '' Iic n) = Polynomial.degreeLE ℝ n :=
  hermiteSequence.span_degreeLE (fun k _ => (by change IsUnit (hermitePolynomial k).leadingCoeff; rw [hermitePolynomial_monic k]; exact isUnit_one))

theorem span_hermitePolynomial : Submodule.span ℝ (range hermitePolynomial) = ⊤ :=
  hermiteSequence.span (fun k => (by change IsUnit (hermitePolynomial k).leadingCoeff; rw [hermitePolynomial_monic k]; exact isUnit_one))

theorem integrable_pow_gaussian (n : ℕ) : Integrable (fun x : ℝ => x^n) standardGaussian := by
  apply (integrable_norm_iff (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^n) standardGaussian)).mp
  simpa [norm_pow] using (memLp_id_gaussianReal' (μ := 0) (v := 1) n (by simp)).integrable_norm_pow'

theorem integrable_polynomial_gaussian (p : ℝ[X]) : Integrable p.eval standardGaussian := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact (hp.add hq).congr (ae_of_all _ fun x => by simp)
  | monomial n a => simpa only [eval_monomial] using (integrable_pow_gaussian n).const_mul a

theorem memLp_polynomial_gaussian (p : ℝ[X]) : MemLp p.eval 2 standardGaussian := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  exact (integrable_polynomial_gaussian (p^2)).congr (ae_of_all _ fun x => by simp)

end Foundations
