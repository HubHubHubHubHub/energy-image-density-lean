import Foundations.Hermite.Polynomial
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open Filter Topology Set MeasureTheory ProbabilityTheory
namespace Foundations

theorem integrable_exp_abs_gaussian (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a*|x|)) standardGaussian := by
  apply ((integrable_exp_mul_gaussianReal a).add (integrable_exp_mul_gaussianReal (-a))).mono'
    (by fun_prop)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos hx, mul_neg, ← neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

theorem memLp_exp_abs_gaussian (a : ℝ) :
    MemLp (fun x : ℝ => Real.exp (a*|x|)) 2 standardGaussian := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  convert integrable_exp_abs_gaussian (2*a) using 1
  ext x
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem integrable_abs_mul_exp_abs_gaussian {f : ℝ → ℝ} (hf : MemLp f 2 standardGaussian) (a : ℝ) :
    Integrable (fun x => |f x| * Real.exp (a*|x|)) standardGaussian := by
  exact (hf.norm.integrable_mul (memLp_exp_abs_gaussian a)).congr
    (ae_of_all _ fun x => by simp [Real.norm_eq_abs])

/-- The complex exponential series may be integrated against any real Gaussian L² function. -/
theorem hasSum_integral_mul_exp {f : ℝ → ℝ} (hf : MemLp f 2 standardGaussian) (z : ℂ) :
    HasSum (fun n : ℕ => z^n / (n.factorial : ℂ) *
      (∫ x, f x * x^n ∂standardGaussian : ℝ))
      (∫ x, (f x : ℂ) * Complex.exp (z*x) ∂standardGaussian) := by
  have hfm : AEStronglyMeasurable (fun x => (f x : ℂ)) standardGaussian := hf.ofReal.aestronglyMeasurable
  let F (n : ℕ) (x : ℝ) : ℂ := (f x : ℂ) * (z*x)^n / n.factorial
  let B (n : ℕ) (x : ℝ) : ℝ := |f x| * (‖z‖*|x|)^n / n.factorial
  have hb (x : ℝ) : HasSum (fun n => B n x) (|f x| * Real.exp (‖z‖*|x|)) := by
    simpa [B, Real.exp_eq_exp_ℝ, mul_div_assoc] using
      (NormedSpace.expSeries_div_hasSum_exp (‖z‖*|x|)).mul_left |f x|
  have hi := hasSum_integral_of_dominated_convergence (μ := standardGaussian)
    (F := F) (f := fun x => (f x : ℂ) * Complex.exp (z*x)) B
    (fun n => by dsimp [F]; fun_prop)
    (fun n => ae_of_all _ fun x => by
      dsimp [F, B]
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_natCast,
        Real.norm_eq_abs]
      exact le_rfl)
    (ae_of_all _ fun x => (hb x).summable)
    (by simpa only [(funext fun x => (hb x).tsum_eq)] using integrable_abs_mul_exp_abs_gaussian hf ‖z‖)
    (ae_of_all _ fun x => by
      simpa [F, Complex.exp_eq_exp_ℂ, mul_div_assoc] using
        (NormedSpace.expSeries_div_hasSum_exp (z*(x:ℂ))).mul_left (f x : ℂ))
  apply hi.congr_fun
  intro n
  symm
  have he (x : ℝ) : F n x = (z^n / (n.factorial:ℂ)) * ((f x * x^n : ℝ) : ℂ) := by
    simp only [F, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_complex_ofReal]

theorem integral_mul_exp_eq_tsum {f : ℝ → ℝ} (hf : MemLp f 2 standardGaussian) (z : ℂ) :
    (∫ x, (f x : ℂ) * Complex.exp (z*x) ∂standardGaussian) =
      ∑' n : ℕ, z^n / (n.factorial:ℂ) * (∫ x, f x * x^n ∂standardGaussian : ℝ) :=
  (hasSum_integral_mul_exp hf z).tsum_eq.symm

theorem integral_mul_exp_eq_zero_of_moments {f : ℝ → ℝ} (hf : MemLp f 2 standardGaussian)
    (hm : ∀ n : ℕ, ∫ x, f x * x^n ∂standardGaussian = 0) (z : ℂ) :
    (∫ x, (f x : ℂ) * Complex.exp (z*x) ∂standardGaussian) = 0 := by
  rw [integral_mul_exp_eq_tsum hf]
  simp [hm]

end Foundations
