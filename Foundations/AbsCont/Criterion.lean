import Foundations.AbsCont.IntegrationByParts
import Foundations.AbsCont.Sobolev
import Foundations.AbsCont.WeakLimit
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open MeasureTheory Filter Set Function ContinuousLinearMap
open scoped Topology ENNReal NNReal ContDiff BigOperators
set_option maxHeartbeats 800000
namespace Foundations

/-- Coordinate control of the norm of a linear functional in Euclidean space. -/
theorem norm_clm_le_sum_basis {d : ℕ} (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i, ‖L (EuclideanSpace.basisFun (Fin d) ℝ i)‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro x
  have he : L x = ∑ i, x i * L (EuclideanSpace.basisFun (Fin d) ℝ i) := by
    nth_rw 1 [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
    simp [EuclideanSpace.basisFun_repr, map_sum, map_smul]
  rw [he]
  calc
    _ ≤ ∑ i, ‖x i * L (EuclideanSpace.basisFun (Fin d) ℝ i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x‖ * ‖L (EuclideanSpace.basisFun (Fin d) ℝ i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem integral_norm_fderiv_measureMollify_le {d : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    {C : Fin d → ℝ} (hb : ∀ i, HasIBPBound ν (EuclideanSpace.basisFun (Fin d) ℝ i) (C i))
    (n : ℕ) : ∫ x, ‖fderiv ℝ (measureMollify ν n) x‖ ≤ ∑ i, C i := by
  have hsum : Integrable (fun x => ∑ i, ‖fderiv ℝ (measureMollify ν n) x
      (EuclideanSpace.basisFun (Fin d) ℝ i)‖) :=
    integrable_finset_sum _ fun i _ => (integrable_deriv_measureMollify ν n _).norm
  have hi : Integrable (fun x => ‖fderiv ℝ (measureMollify ν n) x‖) := hsum.mono'
    ((contDiff_measureMollify ν n).continuous_fderiv (by simp)).norm.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [norm_norm] using norm_clm_le_sum_basis (fderiv ℝ (measureMollify ν n) x))
  calc
    _ ≤ ∫ x, ∑ i, ‖fderiv ℝ (measureMollify ν n) x (EuclideanSpace.basisFun (Fin d) ℝ i)‖ :=
      integral_mono hi hsum (fun x => norm_clm_le_sum_basis _)
    _ = ∑ i, ∫ x, ‖fderiv ℝ (measureMollify ν n) x (EuclideanSpace.basisFun (Fin d) ℝ i)‖ :=
      integral_finset_sum _ fun i _ => (integrable_deriv_measureMollify ν n _).norm
    _ ≤ ∑ i, C i := Finset.sum_le_sum fun i _ => integral_norm_deriv_measureMollify_le ν _ (hb i) n

/-- Endpoint Sobolev bound, uniform in the regularization index. -/
theorem eLpNorm_measureMollify_le {d : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    {C : Fin d → ℝ} (hb : ∀ i, HasIBPBound ν (EuclideanSpace.basisFun (Fin d) ℝ i) (C i))
    {p : ℝ≥0} (hp : NNReal.HolderConjugate d p) (n : ℕ) :
    eLpNorm (measureMollify ν n) p ≤
      eLpNormLESNormFDerivOneConst (volume : Measure (EuclideanSpace ℝ (Fin d))) p *
        ENNReal.ofReal (∑ i, C i) := by
  have hsum : Integrable (fun x => ∑ i, ‖fderiv ℝ (measureMollify ν n) x
      (EuclideanSpace.basisFun (Fin d) ℝ i)‖) :=
    integrable_finset_sum _ fun i _ => (integrable_deriv_measureMollify ν n _).norm
  have hi : Integrable (fderiv ℝ (measureMollify ν n)) := hsum.mono'
    ((contDiff_measureMollify ν n).continuous_fderiv (by simp)).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_clm_le_sum_basis _)
  have H := eLpNorm_le_eLpNorm_fderiv_one_of_integrable
    ((contDiff_measureMollify ν n).of_le (by simp)) (integrable_measureMollify ν n) hi
    (by simpa using hp)
  apply H.trans
  apply mul_le_mul_right
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi]
  exact ENNReal.ofReal_le_ofReal (integral_norm_fderiv_measureMollify_le ν hb n)

/-- Malliavin's finite-measure criterion, dimensions at least two. -/
theorem absolutelyContinuous_of_integral_deriv_le_of_two_le {d : ℕ} (hd : 2 ≤ d)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    {C : Fin d → ℝ} (hb : ∀ i, HasIBPBound ν (EuclideanSpace.basisFun (Fin d) ℝ i) (C i)) :
    ν ≪ volume := by
  have hp : NNReal.HolderConjugate (d : ℝ≥0) (NNReal.conjExponent d) :=
    NNReal.HolderConjugate.conjExponent (by exact_mod_cast (by omega : 1 < d))
  letI : ENNReal.HolderConjugate (d : ℝ≥0∞) (NNReal.conjExponent d : ℝ≥0∞) := by
    simpa using hp.coe_ennreal
  apply absolutelyContinuous_of_eLpNorm_measureMollify_le ν (p := (d : ℝ≥0∞))
    (q := (NNReal.conjExponent d : ℝ≥0∞))
    (M := eLpNormLESNormFDerivOneConst (volume : Measure (EuclideanSpace ℝ (Fin d)))
      (NNReal.conjExponent d) * ENNReal.ofReal (∑ i, C i)) (by exact_mod_cast (by omega : 1 ≤ d)) (by simp)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
  exact eLpNorm_measureMollify_le ν hb hp

end Foundations
