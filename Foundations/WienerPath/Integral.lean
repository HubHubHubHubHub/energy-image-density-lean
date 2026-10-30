import Foundations.WienerPath.Coefficients
import Foundations.CameronMartinPath.Space

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace
namespace Foundations

def schauderGaussianCoordinate (i : SchauderIndex) : Lp ℝ 2 schauderGaussianMeasure :=
  schauderL2Reindex.symm (gaussianCoordinate (schauderEnum i))

theorem coe_schauderGaussianCoordinate (i : SchauderIndex) :
    schauderGaussianCoordinate i =ᵐ[schauderGaussianMeasure] fun x => x i := by
  have h := measurePreserving_schauderReindex_symm.quasiMeasurePreserving.ae
    (coe_gaussianCoordinate (schauderEnum i))
  filter_upwards [Lp.coeFn_compMeasurePreserving (gaussianCoordinate (schauderEnum i))
    measurePreserving_schauderReindex_symm, h] with x hx hi
  change (Lp.compMeasurePreserving _ _ _) x = _
  rw [hx, Function.comp_apply, hi]
  simp

theorem hasSum_wienerIntegralSchauder (a : SchauderL2Coefficients) :
    HasSum (fun i => a i • schauderGaussianCoordinate i) (wienerIntegralSchauder a) := by
  change HasSum (fun i => a i • schauderL2Reindex.symm (gaussianCoordinate (schauderEnum i)))
    (schauderL2Reindex.symm (wienerIntegral (schauderCoefficientReindex a)))
  have h := (hasSum_wienerIntegral (schauderCoefficientReindex a)).mapL
    (Lp.compMeasurePreservingₗᵢ ℝ schauderReindex.symm
      measurePreserving_schauderReindex_symm).toContinuousLinearMap
  have h' := schauderEnum.hasSum_iff.mpr h
  convert h' using 1
  · ext i
    simp only [Function.comp_def,map_smul,schauderCoefficientReindex_apply,
      Equiv.symm_apply_apply]
    rfl
  · rfl

def wienerIntegralPath : HaarL2 →ₗᵢ[ℝ] Lp ℝ 2 wienerMeasure :=
  wienerL2Equiv.symm.toLinearIsometry.comp
    (wienerIntegralSchauder.comp haarBasis.repr.toLinearIsometry)

theorem coe_wienerIntegralPath (g : HaarL2) :
    wienerIntegralPath g =ᵐ[wienerMeasure]
      fun ω => wienerIntegralSchauder (haarBasis.repr g) (schauderCoordinate ω) :=
  coe_wienerL2Equiv_symm _

theorem wienerIntegralPath_map (g : HaarL2) :
    wienerMeasure.map (wienerIntegralPath g) =
      gaussianReal 0 (NNReal.mk (‖g‖^2) (sq_nonneg _)) := by
  rw [Measure.map_congr (coe_wienerIntegralPath g)]
  have h := AEMeasurable.map_map_of_aemeasurable
    (g := (wienerIntegralSchauder (haarBasis.repr g) : (SchauderIndex → ℝ) → ℝ))
    (by rw [measurePreserving_schauderCoordinate.map_eq]
        exact (Lp.aestronglyMeasurable _).aemeasurable)
    measurePreserving_schauderCoordinate.aemeasurable
  rw [measurePreserving_schauderCoordinate.map_eq,wienerIntegralSchauder_map,
    haarBasis.repr.norm_map] at h
  exact h.symm

theorem integral_wienerIntegralPath_mul (g h : HaarL2) :
    (∫ ω, wienerIntegralPath g ω * wienerIntegralPath h ω ∂wienerMeasure) = ⟪g,h⟫_ℝ := by
  rw [← wienerIntegralPath.inner_map_map g h,L2.inner_def]
  congr 1
  funext ω
  simp [mul_comm]

end Foundations
