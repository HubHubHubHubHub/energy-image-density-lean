import Foundations.WienerPath.Reindex

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
set_option backward.isDefEq.respectTransparency false
namespace Foundations

abbrev SchauderL2Coefficients := lp (fun _ : SchauderIndex => ℝ) 2

/-- Reindexing square-summable families preserves their norm. -/
def schauderCoefficientReindex : SchauderL2Coefficients ≃ₗᵢ[ℝ] CameronMartinSpace where
  toFun a := ⟨fun n => a (schauderEnum.symm n), memℓp_gen
    ((schauderEnum.symm.summable_iff).mpr (a.2.summable (by norm_num)))⟩
  invFun a := ⟨fun i => a (schauderEnum i), memℓp_gen
    ((schauderEnum.summable_iff).mpr (a.2.summable (by norm_num)))⟩
  left_inv a := by ext i; simp
  right_inv a := by ext n; simp
  map_add' a b := by ext n; rfl
  map_smul' c a := by ext n; rfl
  norm_map' a := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact schauderEnum.symm.tsum_eq (fun i => ‖a i‖ ^ (2 : ENNReal).toReal)

@[simp] theorem schauderCoefficientReindex_apply (a : SchauderL2Coefficients) (n : ℕ) :
    schauderCoefficientReindex a n = a (schauderEnum.symm n) := rfl

def wienerIntegralSchauder : SchauderL2Coefficients →ₗᵢ[ℝ] Lp ℝ 2 schauderGaussianMeasure :=
  schauderL2Reindex.symm.toLinearIsometry.comp
    (wienerIntegral.comp schauderCoefficientReindex.toLinearIsometry)

theorem coe_wienerIntegralSchauder (a : SchauderL2Coefficients) :
    wienerIntegralSchauder a =ᵐ[schauderGaussianMeasure]
      fun x => wienerIntegral (schauderCoefficientReindex a) (schauderReindex.symm x) :=
  Lp.coeFn_compMeasurePreserving _ measurePreserving_schauderReindex_symm

theorem wienerIntegralSchauder_map (a : SchauderL2Coefficients) :
    schauderGaussianMeasure.map (wienerIntegralSchauder a) =
      gaussianReal 0 (NNReal.mk (‖a‖^2) (sq_nonneg _)) := by
  rw [Measure.map_congr (coe_wienerIntegralSchauder a)]
  have h := AEMeasurable.map_map_of_aemeasurable
    (g := (wienerIntegral (schauderCoefficientReindex a) : (ℕ → ℝ) → ℝ))
    (by rw [measurePreserving_schauderReindex_symm.map_eq]
        exact (Lp.aestronglyMeasurable _).aemeasurable)
    measurePreserving_schauderReindex_symm.aemeasurable
  rw [measurePreserving_schauderReindex_symm.map_eq, wienerIntegral_map,
    schauderCoefficientReindex.norm_map] at h
  exact h.symm

end Foundations
