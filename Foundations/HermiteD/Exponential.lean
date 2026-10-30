import Foundations.HermiteD.Polynomial

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Foundations
variable {ι : Type*} [Fintype ι]

def gaussianDot (t x : ι → ℝ) : ℝ := ∑ i, t i * x i

theorem continuous_gaussianDot (t : ι → ℝ) : Continuous (gaussianDot t) := by
  unfold gaussianDot
  exact continuous_finset_sum _ (fun i _ => continuous_const.mul (continuous_apply i))

def dotPolynomialD (t : ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ i, MvPolynomial.C (t i) * MvPolynomial.X i

theorem eval_dotPolynomialD (t x : ι → ℝ) :
    MvPolynomial.eval x (dotPolynomialD t) = gaussianDot t x := by
  simp [dotPolynomialD,gaussianDot]

theorem abs_gaussianDot_le (t x : ι → ℝ) :
    |gaussianDot t x| ≤ ∑ i, |t i| * |x i| := by
  simpa only [gaussianDot,abs_mul] using Finset.abs_sum_le_sum_abs (fun i => t i*x i) Finset.univ

theorem memLp_exp_abs_gaussianDot (t : ι → ℝ) :
    MemLp (fun x => Real.exp |gaussianDot t x|) 2 (gaussianProduct ι) := by
  have H := memLp_two_gaussianProduct_prod
    (g := fun i x => Real.exp (|t i| *|x|)) (fun i => by fun_prop)
    (fun i => memLp_exp_abs_gaussian (|t i|))
  apply H.mono' ((continuous_gaussianDot t).abs.rexp.aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _), ← Real.exp_sum]
    exact Real.exp_le_exp.mpr (abs_gaussianDot_le t x)

theorem integral_mul_exp_gaussianDot_eq_zero {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (gaussianProduct ι))
    (hm : ∀ p : MvPolynomial ι ℝ, ∫ x, f x * MvPolynomial.eval x p ∂gaussianProduct ι = 0)
    (t : ι → ℝ) :
    (∫ x, (f x : ℂ) * Complex.exp ((gaussianDot t x : ℂ)*Complex.I) ∂gaussianProduct ι) = 0 := by
  let F (n : ℕ) (x : ι → ℝ) : ℂ :=
    (f x : ℂ) * ((gaussianDot t x : ℂ)*Complex.I)^n / n.factorial
  let B (n : ℕ) (x : ι → ℝ) : ℝ := |f x| * |gaussianDot t x|^n / n.factorial
  have hfm : AEStronglyMeasurable (fun x => (f x : ℂ)) (gaussianProduct ι) :=
    hf.ofReal.aestronglyMeasurable
  have hdot := (continuous_gaussianDot t).aestronglyMeasurable (μ := gaussianProduct ι)
  have hb (x : ι → ℝ) : HasSum (fun n => B n x) (|f x| *Real.exp |gaussianDot t x|) := by
    simpa [B,Real.exp_eq_exp_ℝ,mul_div_assoc] using
      (NormedSpace.expSeries_div_hasSum_exp |gaussianDot t x|).mul_left |f x|
  have hdom : Integrable (fun x => |f x| *Real.exp |gaussianDot t x|) (gaussianProduct ι) := by
    simpa only [Real.norm_eq_abs, Pi.mul_def] using hf.norm.integrable_mul (memLp_exp_abs_gaussianDot t)
  have h := hasSum_integral_of_dominated_convergence (μ := gaussianProduct ι)
    (F := F) (f := fun x => (f x : ℂ)*Complex.exp ((gaussianDot t x : ℂ)*Complex.I)) B
    (fun n => by dsimp [F]; fun_prop)
    (fun n => ae_of_all _ fun x => by
      simp [F,B,norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs])
    (ae_of_all _ fun x => (hb x).summable)
    (by simpa only [(funext fun x => (hb x).tsum_eq)] using hdom)
    (ae_of_all _ fun x => by
      simpa [F,Complex.exp_eq_exp_ℂ,mul_div_assoc] using
        (NormedSpace.expSeries_div_hasSum_exp ((gaussianDot t x : ℂ)*Complex.I)).mul_left (f x : ℂ))
  have hz (n : ℕ) : (∫ x, F n x ∂gaussianProduct ι) = 0 := by
    have he (x : ι → ℝ) : F n x = (Complex.I^n / (n.factorial : ℂ)) *
        ((f x * (gaussianDot t x)^n : ℝ) : ℂ) := by
      simp only [F,mul_pow,Complex.ofReal_mul,Complex.ofReal_pow]
      ring
    simp_rw [he]
    rw [integral_const_mul,integral_complex_ofReal]
    have hm' := hm ((dotPolynomialD t)^n)
    simp only [map_pow,eval_dotPolynomialD] at hm'
    rw [hm']; simp
  have hzero : HasSum (fun _ : ℕ => (0 : ℂ))
      (∫ x, (f x : ℂ)*Complex.exp ((gaussianDot t x : ℂ)*Complex.I) ∂gaussianProduct ι) :=
    h.congr_fun (fun n => (hz n).symm)
  exact hzero.unique hasSum_zero

end Foundations
