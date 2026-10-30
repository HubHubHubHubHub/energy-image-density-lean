import Foundations.MehlerD.Kernel
import Foundations.Mehler.Hermite

noncomputable section
open MeasureTheory Set
namespace Foundations
variable {ι : Type*} [Fintype ι]

def hermiteDegreeD (α : ι → ℕ) : ℕ := ∑ i, α i

theorem mehlerKernelD_hermite {t : ℝ} (ht : 0 ≤ t) (α : ι → ℕ) (x : ι → ℝ) :
    mehlerKernelD t (hermiteD α) x =
      Real.exp (-(hermiteDegreeD α : ℝ)*t) * hermiteD α x := by
  change (∫ y, ∏ i, hermiteFun (α i) (mehlerCoeffA t*x i+mehlerCoeffB t*y i)
    ∂gaussianProduct ι) = _
  rw [integral_fintype_prod_eq_prod
    (fun i y => hermiteFun (α i) (mehlerCoeffA t*x i+mehlerCoeffB t*y))]
  change (∏ i, mehlerKernel t (hermiteFun (α i)) (x i)) = _
  simp_rw [mehlerKernel_hermite ht]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 1
  simp [hermiteDegreeD, Finset.sum_mul, Finset.sum_neg_distrib]

theorem mehlerD_hermite {t : ℝ} (ht : 0 ≤ t) (α : ι → ℕ) :
    mehlerD t (hermiteLpD α) =
      Real.exp (-(hermiteDegreeD α : ℝ)*t) • hermiteLpD α := by
  apply Lp.ext
  filter_upwards [coe_mehlerD_toLp ht (memLp_hermiteD α),
    Lp.coeFn_smul (Real.exp (-(hermiteDegreeD α : ℝ)*t)) (hermiteLpD α),
    coe_hermiteLpD α] with x hx hy hz
  change mehlerD t (hermiteLpD α) x = _ at hx ⊢
  rw [hx,hy]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hz]
  exact mehlerKernelD_hermite ht α x

theorem mehlerD_hermiteNormalized {t : ℝ} (ht : 0 ≤ t) (α : ι → ℕ) :
    mehlerD t (hermiteNormalizedD α) =
      Real.exp (-(hermiteDegreeD α : ℝ)*t) • hermiteNormalizedD α := by
  rw [hermiteNormalizedD_eq,map_smul,mehlerD_hermite ht]
  exact smul_comm _ _ _

end Foundations
