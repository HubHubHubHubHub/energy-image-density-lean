import Foundations.CameronMartin.Theorem
import Foundations.Wiener.L2
import Mathlib.Logic.Denumerable

noncomputable section
open MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
namespace Foundations

/-- The Schauder coordinates form a countably infinite index set. -/
instance infinite_schauderIndex : Infinite SchauderIndex :=
  Infinite.of_injective (fun j : ℕ => (some ⟨j, ⟨0, by positivity⟩⟩ : SchauderIndex))
    (by intro j k h; exact congrArg Sigma.fst (Option.some.inj h))

/-- An enumeration is used only for transport; no order of summation is imposed. -/
def schauderEnum : SchauderIndex ≃ ℕ := nonempty_equiv_of_countable.some

def schauderReindex : (ℕ → ℝ) ≃ᵐ (SchauderIndex → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) schauderEnum.symm

@[simp] theorem schauderReindex_apply (x : ℕ → ℝ) (i : SchauderIndex) :
    schauderReindex x i = x (schauderEnum i) := by simp [schauderReindex, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

@[simp] theorem schauderReindex_symm_apply (x : SchauderIndex → ℝ) (n : ℕ) :
    schauderReindex.symm x n = x (schauderEnum.symm n) := rfl

theorem map_reindex_gaussianInf :
    gaussianInf.map schauderReindex = schauderGaussianMeasure :=
  Measure.infinitePi_map_piCongrLeft (fun _ : SchauderIndex => gaussianReal 0 1)
    schauderEnum.symm

theorem measurePreserving_schauderReindex :
    MeasurePreserving schauderReindex gaussianInf schauderGaussianMeasure :=
  ⟨schauderReindex.measurable, map_reindex_gaussianInf⟩

theorem measurePreserving_schauderReindex_symm :
    MeasurePreserving schauderReindex.symm schauderGaussianMeasure gaussianInf := by
  refine ⟨schauderReindex.symm.measurable, ?_⟩
  rw [← map_reindex_gaussianInf, Measure.map_map schauderReindex.symm.measurable
    schauderReindex.measurable]
  simpa only [schauderReindex.symm_comp_self] using (Measure.map_id (μ := gaussianInf))

def schauderL2Reindex : Lp ℝ 2 schauderGaussianMeasure ≃ₗᵢ[ℝ] Lp ℝ 2 gaussianInf :=
  LinearIsometryEquiv.ofLinearIsometry
    (Lp.compMeasurePreservingₗᵢ ℝ schauderReindex measurePreserving_schauderReindex)
    (Lp.compMeasurePreservingₗ ℝ schauderReindex.symm measurePreserving_schauderReindex_symm)
    (by ext f : 1; change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
        rw [← Lp.compMeasurePreserving_comp_apply]
        exact lp_compMeasurePreserving_eq_self _ (Filter.Eventually.of_forall
          schauderReindex.symm_apply_apply) f)
    (by ext f : 1; change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
        rw [← Lp.compMeasurePreserving_comp_apply]
        exact lp_compMeasurePreserving_eq_self _ (Filter.Eventually.of_forall
          schauderReindex.apply_symm_apply) f)

end Foundations
