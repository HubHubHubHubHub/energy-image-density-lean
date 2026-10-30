import Foundations.HermiteD.Basis
import Foundations.Mehler.Gaussian

noncomputable section
open MeasureTheory Set
namespace Foundations
variable {ι : Type*} [Fintype ι]

/-- Coordinatewise Gaussian mixing, with the order adapted to the section isometry. -/
def mehlerMixD (t : ℝ) (z : (ι → ℝ) × (ι → ℝ)) : ι → ℝ :=
  fun i => mehlerCoeffA t * z.2 i + mehlerCoeffB t * z.1 i

theorem measurePreserving_mehlerMixD {t : ℝ} (ht : 0 ≤ t) :
    MeasurePreserving (mehlerMixD (ι := ι) t)
      ((gaussianProduct ι).prod (gaussianProduct ι)) (gaussianProduct ι) := by
  have hp := measurePreserving_pi
    (fun _ : ι => standardGaussian.prod standardGaussian)
    (fun _ : ι => standardGaussian) (fun _ => measurePreserving_mehlerMix ht)
  have he := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun _ => standardGaussian) (fun _ => standardGaussian)).symm
  exact hp.comp he

def mehlerKernelD (t : ℝ) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∫ y, f (fun i => mehlerCoeffA t * x i + mehlerCoeffB t * y i) ∂gaussianProduct ι

@[simp] theorem mehlerKernelD_zero (f : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    mehlerKernelD 0 f x = f x := by
  simp [mehlerKernelD]

@[simp] theorem hermiteD_zero (x : ι → ℝ) : hermiteD (0 : ι → ℕ) x = 1 := by
  simp [hermiteD, hermiteFun, hermitePolynomial]

@[simp] theorem hermiteFactorD_zero : hermiteFactorD (0 : ι → ℕ) = 1 := by
  simp [hermiteFactorD]

@[simp] theorem hermiteNormalizedD_zero :
    hermiteNormalizedD (0 : ι → ℕ) = hermiteLpD 0 := by
  simp [hermiteNormalizedD_eq]

end Foundations
