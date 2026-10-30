import Foundations.Hermite.Basis
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

noncomputable section
open MeasureTheory ProbabilityTheory Polynomial Set
open scoped InnerProductSpace
namespace Foundations

abbrev gaussianProduct (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => standardGaussian)

abbrev gaussianPi (d : ℕ) : Measure (Fin d → ℝ) := gaussianProduct (Fin d)

variable {ι : Type*} [Fintype ι]

def hermiteD (α : ι → ℕ) (x : ι → ℝ) : ℝ := ∏ i, hermiteFun (α i) (x i)

def hermiteUnit (n : ℕ) (x : ℝ) : ℝ := (Real.sqrt (n.factorial : ℝ))⁻¹ * hermiteFun n x

def hermiteNormalizedFunD (α : ι → ℕ) (x : ι → ℝ) : ℝ := ∏ i, hermiteUnit (α i) (x i)

theorem continuous_hermiteUnit (n : ℕ) : Continuous (hermiteUnit n) := by
  unfold hermiteUnit hermiteFun
  fun_prop

theorem memLp_hermiteUnit (n : ℕ) : MemLp (hermiteUnit n) 2 standardGaussian :=
  (memLp_polynomial_gaussian (hermitePolynomial n)).const_mul _

theorem coe_hermiteNormalized (n : ℕ) : hermiteNormalized n =ᵐ[standardGaussian] hermiteUnit n := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt (n.factorial : ℝ))⁻¹ (hermiteLp n),
    coe_polynomialLp (hermitePolynomial n)] with x hs hx
  change ((Real.sqrt (n.factorial : ℝ))⁻¹ • hermiteLp n) x = hermiteUnit n x
  rw [hs]
  change hermiteLp n x = (hermitePolynomial n).eval x at hx
  simp only [Pi.smul_apply, smul_eq_mul, hx, hermiteUnit, hermiteFun]

theorem memLp_two_gaussianProduct_prod {g : ι → ℝ → ℝ}
    (hc : ∀ i, Continuous (g i)) (hm : ∀ i, MemLp (g i) 2 standardGaussian) :
    MemLp (fun x : ι → ℝ => ∏ i, g i (x i)) 2 (gaussianProduct ι) := by
  have hcont : Continuous (fun x : ι → ℝ => ∏ i, g i (x i)) :=
    continuous_finset_prod _ (fun i _ => (hc i).comp (continuous_apply i))
  apply (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).mpr
  simpa only [Finset.prod_pow] using Integrable.fintype_prod (fun i => (hm i).integrable_sq)

theorem memLp_hermiteD (α : ι → ℕ) : MemLp (hermiteD α) 2 (gaussianProduct ι) := by
  apply memLp_two_gaussianProduct_prod
  · intro i; unfold hermiteFun; fun_prop
  · intro i; exact memLp_polynomial_gaussian _

theorem memLp_hermiteNormalizedFunD (α : ι → ℕ) :
    MemLp (hermiteNormalizedFunD α) 2 (gaussianProduct ι) :=
  memLp_two_gaussianProduct_prod (fun i => continuous_hermiteUnit _) (fun i => memLp_hermiteUnit _)

def hermiteLpD (α : ι → ℕ) : Lp ℝ 2 (gaussianProduct ι) :=
  (memLp_hermiteD α).toLp (hermiteD α)

def hermiteNormalizedD (α : ι → ℕ) : Lp ℝ 2 (gaussianProduct ι) :=
  (memLp_hermiteNormalizedFunD α).toLp (hermiteNormalizedFunD α)

theorem coe_hermiteLpD (α : ι → ℕ) : hermiteLpD α =ᵐ[gaussianProduct ι] hermiteD α :=
  (memLp_hermiteD α).coeFn_toLp

theorem coe_hermiteNormalizedD (α : ι → ℕ) :
    hermiteNormalizedD α =ᵐ[gaussianProduct ι] hermiteNormalizedFunD α :=
  (memLp_hermiteNormalizedFunD α).coeFn_toLp

def tensorPolynomialD : MultilinearMap ℝ (fun _ : ι => ℝ[X]) (MvPolynomial ι ℝ) :=
  (MultilinearMap.mkPiAlgebra ℝ ι (MvPolynomial ι ℝ)).compLinearMap
    (fun i => (Polynomial.aeval (MvPolynomial.X i)).toLinearMap)

def hermitePolynomialD (α : ι → ℕ) : MvPolynomial ι ℝ :=
  tensorPolynomialD (fun i => hermitePolynomial (α i))

theorem eval_tensorPolynomialD (p : ι → ℝ[X]) (x : ι → ℝ) :
    MvPolynomial.eval x (tensorPolynomialD p) = ∏ i, (p i).eval (x i) := by
  simp only [tensorPolynomialD, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply]
  change (MvPolynomial.aeval x) (∏ i, Polynomial.aeval (MvPolynomial.X i) (p i)) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Polynomial.aeval_algHom_apply]
  simp

theorem eval_hermitePolynomialD (α : ι → ℕ) (x : ι → ℝ) :
    MvPolynomial.eval x (hermitePolynomialD α) = hermiteD α x :=
  eval_tensorPolynomialD _ _

end Foundations
