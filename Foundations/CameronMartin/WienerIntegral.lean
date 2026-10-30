import Foundations.Chaos.Normalization
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace Topology
namespace Foundations

abbrev CameronMartinSpace := lp (fun _ : ℕ => ℝ) 2

def gaussianCoordinate (i : ℕ) : Lp ℝ 2 gaussianInf := hermiteInf (Finsupp.single i 1)

theorem coe_gaussianCoordinate (i : ℕ) : gaussianCoordinate i =ᵐ[gaussianInf] fun x => x i := by
  filter_upwards [coe_hermiteInf (Finsupp.single i 1)] with x hx
  simpa [gaussianCoordinate,hermiteNormalizedFunInf,Finsupp.prod_single_index,
    hermiteUnit,hermiteFun,hermitePolynomial_succ] using hx

theorem orthonormal_gaussianCoordinate : Orthonormal ℝ gaussianCoordinate :=
  orthonormal_hermiteInf.comp (fun i => Finsupp.single i 1)
    (Finsupp.single_left_injective (by norm_num))

/-- The Wiener integral is the isometry induced by the orthonormal coordinate family. -/
def wienerIntegral : CameronMartinSpace →ₗᵢ[ℝ] Lp ℝ 2 gaussianInf :=
  orthonormal_gaussianCoordinate.orthogonalFamily.linearIsometry

theorem hasSum_wienerIntegral (a : CameronMartinSpace) :
    HasSum (fun i => a i • gaussianCoordinate i) (wienerIntegral a) :=
  orthonormal_gaussianCoordinate.orthogonalFamily.hasSum_linearIsometry a

@[simp] theorem wienerIntegral_single (i : ℕ) (a : ℝ) :
    wienerIntegral (lp.single 2 i a) = a • gaussianCoordinate i :=
  orthonormal_gaussianCoordinate.orthogonalFamily.linearIsometry_apply_single a

@[simp] theorem norm_wienerIntegral (a : CameronMartinSpace) : ‖wienerIntegral a‖ = ‖a‖ :=
  wienerIntegral.norm_map a

theorem integral_wienerIntegral_mul (a b : CameronMartinSpace) :
    (∫ x, wienerIntegral a x * wienerIntegral b x ∂gaussianInf) = ⟪a,b⟫_ℝ := by
  rw [← wienerIntegral.inner_map_map a b,L2.inner_def]
  congr 1
  funext x
  simp [mul_comm]

def wienerPartial (a : ℕ → ℝ) (s : Finset ℕ) : Lp ℝ 2 gaussianInf :=
  ∑ i ∈ s, a i • gaussianCoordinate i

def wienerPartialFun (a : ℕ → ℝ) (s : Finset ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ s, a i * x i

theorem coe_wienerPartial (a : ℕ → ℝ) (s : Finset ℕ) :
    wienerPartial a s =ᵐ[gaussianInf] wienerPartialFun a s := by
  have h (i : ℕ) : (a i • gaussianCoordinate i : Lp ℝ 2 gaussianInf) =ᵐ[gaussianInf]
      fun x => a i * x i := by
    filter_upwards [Lp.coeFn_smul (a i) (gaussianCoordinate i),coe_gaussianCoordinate i] with x hx hy
    simp only [hx,Pi.smul_apply,smul_eq_mul,hy]
  filter_upwards [Lp.coeFn_finsetSum s (fun i => a i • gaussianCoordinate i),
    ae_all_iff.mpr h] with x hx hy
  change (∑ i ∈ s, a i • gaussianCoordinate i : Lp ℝ 2 gaussianInf) x = _
  rw [hx]
  simpa only [Finset.sum_apply,wienerPartialFun] using Finset.sum_congr rfl (fun i _ => hy i)

theorem tendsto_wienerPartial (a : CameronMartinSpace) :
    Tendsto (fun n => wienerPartial a (Finset.range n)) atTop (𝓝 (wienerIntegral a)) :=
  (hasSum_wienerIntegral a).tendsto_sum_nat

theorem hasSum_sq_cameronMartin (a : CameronMartinSpace) :
    HasSum (fun i => (a i)^2) (‖a‖^2) := by
  simpa [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using lp.hasSum_inner (𝕜 := ℝ) a a

def cameronMartinEnergy (a : ℕ → ℝ) (s : Finset ℕ) : ℝ := ∑ i ∈ s, (a i)^2

theorem tendsto_cameronMartinEnergy (a : CameronMartinSpace) :
    Tendsto (fun n => cameronMartinEnergy a (Finset.range n)) atTop (𝓝 (‖a‖^2)) :=
  (hasSum_sq_cameronMartin a).tendsto_sum_nat

theorem cameronMartinEnergy_nonneg (a : ℕ → ℝ) (s : Finset ℕ) : 0 ≤ cameronMartinEnergy a s :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem cameronMartinEnergy_le (a : CameronMartinSpace) (s : Finset ℕ) :
    cameronMartinEnergy a s ≤ ‖a‖^2 :=
by
  rw [← (hasSum_sq_cameronMartin a).tsum_eq]
  exact (hasSum_sq_cameronMartin a).summable.sum_le_tsum s (fun _ _ => sq_nonneg _)

end Foundations
