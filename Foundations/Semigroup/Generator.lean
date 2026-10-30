import Foundations.Semigroup.Semigroup
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
open Filter Topology Set MeasureTheory
namespace Foundations.ContractionResolvent
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable (R : ContractionResolvent H)

theorem semigroupApprox_sub_eq_integral (b t : ℝ) (x : H) :
    R.semigroupApprox b t x - x = ∫ s in 0..t, R.semigroupApprox b s (R.yosida b x) := by
  have hc : Continuous (fun s => R.semigroupApprox b s (R.yosida b x)) :=
    continuous_iff_continuousAt.mpr fun s =>
      (R.hasDerivAt_semigroupApprox_apply b s _).continuousAt
  simpa using (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => R.hasDerivAt_semigroupApprox_apply b s x) (hc.intervalIntegrable 0 t)).symm

theorem semigroup_sub_eq_integral {t : ℝ} (ht : 0 ≤ t) (x : R.dom) :
    R.semigroup t x - x = ∫ s in 0..t, R.semigroup s (R.generator x) := by
  have hc (b : ℝ) : Continuous (fun s => R.semigroupApprox b s (R.yosida b x)) :=
    continuous_iff_continuousAt.mpr fun s =>
      (R.hasDerivAt_semigroupApprox_apply b s _).continuousAt
  have hi := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := 0) (b := t) (l := (atTop : Filter ℝ))
    (F := fun b s => R.semigroupApprox b s (R.yosida b x))
    (f := fun s => R.semigroup s (R.generator x)) (fun _ => ‖R.generator x‖)
    (Eventually.of_forall fun b => (hc b).aestronglyMeasurable) ?_ intervalIntegrable_const ?_
  · apply tendsto_nhds_unique ((R.tendsto_semigroupApprox_apply ht x).sub tendsto_const_nhds)
    exact hi.congr (fun b => (R.semigroupApprox_sub_eq_integral b t x).symm)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb
    apply Eventually.of_forall
    intro s hs
    have hs0 : 0 ≤ s := (show s ∈ Ioc 0 t from (uIoc_of_le ht) ▸ hs).1.le
    apply (R.norm_semigroupApprox_apply_le hb hs0 _).trans
    rw [R.yosida_generator hb]
    exact (b • R.G b).le_opNorm (R.generator x) |>.trans (by
      simpa using mul_le_mul_of_nonneg_right (R.norm_le hb) (norm_nonneg (R.generator x)))
  · apply Eventually.of_forall
    intro s hs
    have hs0 : 0 ≤ s := (show s ∈ Ioc 0 t from (uIoc_of_le ht) ▸ hs).1.le
    exact R.tendsto_semigroupApprox_moving hs0 (R.tendsto_yosida x)

theorem hasDerivWithinAt_semigroup_zero (x : R.dom) :
    HasDerivWithinAt (fun t => R.semigroup t x) (R.generator x) (Ici 0) 0 := by
  have hc := R.continuous_semigroup_apply (R.generator x)
  have hm : StronglyMeasurableAtFilter (fun t => R.semigroup t (R.generator x))
      (𝓝[Ioi 0] 0) volume :=
    ⟨Ici 0, mem_of_superset self_mem_nhdsWithin Ioi_subset_Ici_self,
      hc.aestronglyMeasurable measurableSet_Ici⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right
    (a := 0) (b := 0) (s := Ici 0) (t := Ioi 0)
    (show IntervalIntegrable (fun t => R.semigroup t (R.generator x)) volume 0 0 by simp)
    hm ((hc 0 (show (0:ℝ) ∈ Ici 0 by simp)).mono Ioi_subset_Ici_self)
  have hd' : HasDerivWithinAt (fun t => (x:H) + ∫ s in 0..t, R.semigroup s (R.generator x))
      (R.generator x) (Ici 0) 0 := by simpa using hd.const_add (x:H)
  apply hd'.congr
  · intro t ht
    have hi := R.semigroup_sub_eq_integral ht x
    linear_combination (norm := module) hi
  · simp

theorem tendsto_semigroup_sub_div (x : R.dom) :
    Tendsto (fun t : ℝ => t⁻¹ • (R.semigroup t x - x)) (𝓝[>] 0) (𝓝 (R.generator x)) := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp
    ((R.hasDerivWithinAt_semigroup_zero x).mono Ioi_subset_Ici_self)
  convert h using 1
  ext t
  simp [slope_def_module]

end Foundations.ContractionResolvent
