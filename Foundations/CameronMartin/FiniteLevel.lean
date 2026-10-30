import Foundations.CameronMartin.WienerIntegral
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Foundations

def gaussianShiftDensity (a x : ℝ) : ℝ := Real.exp (a*x-a^2/2)

theorem integrable_gaussianShiftDensity (a : ℝ) :
    Integrable (gaussianShiftDensity a) standardGaussian := by
  change Integrable (fun x => Real.exp (a*x-a^2/2)) (gaussianReal 0 1)
  simpa only [Real.exp_sub] using
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) a).div_const (Real.exp (a^2/2))

theorem gaussianReal_shift_eq_withDensity (a : ℝ) :
    gaussianReal a 1 = standardGaussian.withDensity
      (fun x => ENNReal.ofReal (gaussianShiftDensity a x)) := by
  rw [standardGaussian,gaussianReal_of_var_ne_zero _ one_ne_zero,
    gaussianReal_of_var_ne_zero _ one_ne_zero, ← withDensity_mul _ (by fun_prop) (by
      unfold gaussianShiftDensity; fun_prop)]
  congr 1
  funext x
  simp only [Pi.mul_apply,gaussianPDF_def, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal_def,NNReal.coe_one,mul_one,sub_zero,gaussianShiftDensity]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

def finiteGaussianShiftDensity {ι : Type*} [Fintype ι] (a x : ι → ℝ) : ℝ :=
  ∏ i, gaussianShiftDensity (a i) (x i)

theorem finiteGaussianShiftDensity_eq_exp {ι : Type*} [Fintype ι] (a x : ι → ℝ) :
    finiteGaussianShiftDensity a x = Real.exp ((∑ i, a i*x i)-(∑ i, (a i)^2)/2) := by
  simp [finiteGaussianShiftDensity,gaussianShiftDensity, ← Real.exp_sum,
    Finset.sum_sub_distrib,Finset.sum_div]

theorem integrable_finiteGaussianShiftDensity {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Integrable (finiteGaussianShiftDensity a) (gaussianProduct ι) :=
  Integrable.fintype_prod (fun i => integrable_gaussianShiftDensity (a i))

theorem gaussianProduct_shift_eq_withDensity {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Measure.pi (fun i => gaussianReal (a i) 1) =
      (gaussianProduct ι).withDensity (fun x => ENNReal.ofReal (finiteGaussianShiftDensity a x)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_finiteGaussianShiftDensity a).integrableOn
      (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)))]
  change ENNReal.ofReal (∫ x in Set.univ.pi s, ∏ i, gaussianShiftDensity (a i) (x i)
    ∂Measure.pi (fun _ : ι => standardGaussian)) = _
  rw [Measure.restrict_pi_pi,integral_fintype_prod_eq_prod]
  have hn (i : ι) (_ : i ∈ Finset.univ) :
      0 ≤ ∫ x in s i, gaussianShiftDensity (a i) x ∂standardGaussian :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  rw [ENNReal.ofReal_prod_of_nonneg hn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [gaussianReal_shift_eq_withDensity,withDensity_apply _ (hs i),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianShiftDensity (a i)).integrableOn
      (ae_of_all _ (fun x => (Real.exp_pos _).le))]

theorem finiteLevel_cameronMartin {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (gaussianProduct ι).map (fun x => x+a) =
      (gaussianProduct ι).withDensity (fun x => ENNReal.ofReal (finiteGaussianShiftDensity a x)) := by
  have h : (gaussianProduct ι).map (fun x => x+a) =
      Measure.pi (fun i => gaussianReal (a i) 1) := by
    change (Measure.pi (fun _ : ι => standardGaussian)).map (fun x i => x i+a i) = _
    rw [Measure.pi_map_pi (f := fun i (x : ℝ) => x+a i) (μ := fun _ : ι => standardGaussian) (by fun_prop)]
    simp only [standardGaussian,gaussianReal_map_add_const,zero_add]
  rw [h,gaussianProduct_shift_eq_withDensity]

end Foundations
