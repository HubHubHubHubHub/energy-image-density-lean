import Foundations.CameronMartin.ExpEstimate
import Foundations.CameronMartin.FiniteLevel

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Foundations

def cameronMartinDensitySet (a : ℕ → ℝ) (s : Finset ℕ) (x : ℕ → ℝ) : ℝ :=
  Real.exp (wienerPartialFun a s x-cameronMartinEnergy a s/2)

def cameronMartinDensityFin (a : CameronMartinSpace) (n : ℕ) : (ℕ → ℝ) → ℝ :=
  cameronMartinDensitySet a (Finset.range n)

def cameronMartinDensity (a : CameronMartinSpace) (x : ℕ → ℝ) : ℝ :=
  Real.exp (wienerIntegral a x-‖a‖^2/2)

theorem measurable_cameronMartinDensitySet (a : ℕ → ℝ) (s : Finset ℕ) :
    Measurable (cameronMartinDensitySet a s) := by
  unfold cameronMartinDensitySet wienerPartialFun
  fun_prop

theorem aemeasurable_cameronMartinDensity (a : CameronMartinSpace) :
    AEMeasurable (cameronMartinDensity a) gaussianInf := by
  have := (Lp.aestronglyMeasurable (wienerIntegral a)).aemeasurable
  unfold cameronMartinDensity
  fun_prop

theorem cameronMartinDensitySet_eq (a : ℕ → ℝ) (s : Finset ℕ) (x : ℕ → ℝ) :
    cameronMartinDensitySet a s x = finiteGaussianShiftDensity (s.restrict a) (s.restrict x) := by
  rw [finiteGaussianShiftDensity_eq_exp]
  simp only [cameronMartinDensitySet,wienerPartialFun,cameronMartinEnergy]
  congr 1
  simp only [Finset.restrict_def]
  rw [Finset.sum_coe_sort s (fun i => a i*x i),Finset.sum_coe_sort s (fun i => (a i)^2)]

theorem wienerPartialFun_map (a : ℕ → ℝ) (s : Finset ℕ) :
    gaussianInf.map (wienerPartialFun a s) =
      gaussianReal 0 (NNReal.mk (cameronMartinEnergy a s) (cameronMartinEnergy_nonneg a s)) := by
  rw [← Measure.map_congr (coe_wienerPartial a s),wienerPartial_map]

theorem memLp_cameronMartinDensitySet (a : ℕ → ℝ) (s : Finset ℕ) :
    MemLp (cameronMartinDensitySet a s) 2 gaussianInf := by
  unfold cameronMartinDensitySet
  simpa only [one_mul] using memLp_exp_gaussian_linear (wienerPartialFun_map a s) 1
    (cameronMartinEnergy a s/2)

theorem integral_cameronMartinDensitySet (a : ℕ → ℝ) (s : Finset ℕ) :
    (∫ x, cameronMartinDensitySet a s x ∂gaussianInf) = 1 := by
  have h := integral_exp_gaussian_linear (wienerPartialFun_map a s) 1 (cameronMartinEnergy a s/2)
  simpa [cameronMartinDensitySet] using h

theorem integral_sq_cameronMartinDensitySet (a : ℕ → ℝ) (s : Finset ℕ) :
    (∫ x, (cameronMartinDensitySet a s x)^2 ∂gaussianInf) = Real.exp (cameronMartinEnergy a s) := by
  have h := integral_sq_exp_gaussian_linear (wienerPartialFun_map a s) 1 (cameronMartinEnergy a s/2)
  convert h using 1 <;> simp [cameronMartinDensitySet] <;> congr 1 <;> ring

theorem integral_cameronMartinDensityFin (a : CameronMartinSpace) (n : ℕ) :
    (∫ x, cameronMartinDensityFin a n x ∂gaussianInf) = 1 :=
  integral_cameronMartinDensitySet a (Finset.range n)

theorem integral_sq_cameronMartinDensityFin_le (a : CameronMartinSpace) (n : ℕ) :
    (∫ x, (cameronMartinDensityFin a n x)^2 ∂gaussianInf) ≤ Real.exp (‖a‖^2) := by
  rw [cameronMartinDensityFin,integral_sq_cameronMartinDensitySet]
  exact Real.exp_le_exp.mpr (cameronMartinEnergy_le a _)

theorem memLp_cameronMartinDensity (a : CameronMartinSpace) :
    MemLp (cameronMartinDensity a) 2 gaussianInf := by
  unfold cameronMartinDensity
  simpa only [one_mul] using memLp_exp_gaussian_linear (wienerIntegral_map a) 1 (‖a‖^2/2)

theorem integral_cameronMartinDensity (a : CameronMartinSpace) :
    (∫ x, cameronMartinDensity a x ∂gaussianInf) = 1 := by
  have h := integral_exp_gaussian_linear (wienerIntegral_map a) 1 (‖a‖^2/2)
  simpa [cameronMartinDensity] using h

theorem integral_sq_cameronMartinDensity (a : CameronMartinSpace) :
    (∫ x, (cameronMartinDensity a x)^2 ∂gaussianInf) = Real.exp (‖a‖^2) := by
  have h := integral_sq_exp_gaussian_linear (wienerIntegral_map a) 1 (‖a‖^2/2)
  convert h using 1 <;> simp [cameronMartinDensity] <;> congr 1 <;> ring

def gaussianOne : Lp ℝ 2 gaussianInf := (memLp_const (1 : ℝ)).toLp (fun _ => 1)

theorem coe_gaussianOne : gaussianOne =ᵐ[gaussianInf] fun _ => (1 : ℝ) :=
  (memLp_const (1 : ℝ)).coeFn_toLp

def cameronMartinExponent (a : CameronMartinSpace) : Lp ℝ 2 gaussianInf :=
  wienerIntegral a - (‖a‖^2/2) • gaussianOne

def cameronMartinExponentFin (a : CameronMartinSpace) (n : ℕ) : Lp ℝ 2 gaussianInf :=
  wienerPartial a (Finset.range n) - (cameronMartinEnergy a (Finset.range n)/2) • gaussianOne

theorem exp_cameronMartinExponent (a : CameronMartinSpace) :
    (fun x => Real.exp (cameronMartinExponent a x)) =ᵐ[gaussianInf] cameronMartinDensity a := by
  filter_upwards [Lp.coeFn_sub (wienerIntegral a) ((‖a‖^2/2) • gaussianOne),
    Lp.coeFn_smul (‖a‖^2/2) gaussianOne,coe_gaussianOne] with x hs hm h1
  unfold cameronMartinExponent cameronMartinDensity
  rw [hs,Pi.sub_apply,hm,Pi.smul_apply,h1]
  simp

theorem exp_cameronMartinExponentFin (a : CameronMartinSpace) (n : ℕ) :
    (fun x => Real.exp (cameronMartinExponentFin a n x)) =ᵐ[gaussianInf] cameronMartinDensityFin a n := by
  filter_upwards [Lp.coeFn_sub (wienerPartial a (Finset.range n))
      ((cameronMartinEnergy a (Finset.range n)/2) • gaussianOne),
    Lp.coeFn_smul (cameronMartinEnergy a (Finset.range n)/2) gaussianOne,
    coe_gaussianOne,coe_wienerPartial a (Finset.range n)] with x hs hm h1 hp
  unfold cameronMartinExponentFin cameronMartinDensityFin cameronMartinDensitySet
  rw [hs,Pi.sub_apply,hm,Pi.smul_apply,h1,hp]
  simp

theorem tendsto_cameronMartinExponentFin (a : CameronMartinSpace) :
    Tendsto (cameronMartinExponentFin a) atTop (𝓝 (cameronMartinExponent a)) :=
  (tendsto_wienerPartial a).sub (((tendsto_cameronMartinEnergy a).div_const 2).smul tendsto_const_nhds)

end Foundations
