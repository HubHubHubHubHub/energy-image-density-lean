import Foundations.Semigroup.Convergence
import Mathlib.Topology.UniformSpace.UniformApproximation

noncomputable section
open Filter Topology Set
namespace Foundations.ContractionResolvent
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable (R : ContractionResolvent H)

def semigroupLinear (t : ℝ) (ht : 0 ≤ t) : H →ₗ[ℝ] H where
  toFun := R.semigroupLimit t
  map_add' x y := tendsto_nhds_unique
    ((R.tendsto_semigroupApprox ht x).add (R.tendsto_semigroupApprox ht y))
    (by simpa using R.tendsto_semigroupApprox ht (x+y)) |>.symm
  map_smul' c x := tendsto_nhds_unique
    ((R.tendsto_semigroupApprox ht x).const_smul c)
    (by simpa using R.tendsto_semigroupApprox ht (c • x)) |>.symm

/-- Negative times are assigned zero; all semigroup laws concern nonnegative times. -/
def semigroup (t : ℝ) : H →L[ℝ] H :=
  if ht : 0 ≤ t then (R.semigroupLinear t ht).mkContinuous 1
    (fun x => by simpa [semigroupLinear] using R.norm_semigroupLimit_le ht x) else 0

theorem semigroup_apply {t : ℝ} (ht : 0 ≤ t) (x : H) :
    R.semigroup t x = R.semigroupLimit t x := by simp [semigroup, ht, semigroupLinear]

theorem tendsto_semigroupApprox_apply {t : ℝ} (ht : 0 ≤ t) (x : H) :
    Tendsto (fun b => R.semigroupApprox b t x) atTop (𝓝 (R.semigroup t x)) := by
  rw [R.semigroup_apply ht]
  exact R.tendsto_semigroupApprox ht x

theorem norm_semigroup_le_one {t : ℝ} (ht : 0 ≤ t) : ‖R.semigroup t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa [R.semigroup_apply ht] using R.norm_semigroupLimit_le ht x

theorem norm_semigroup_apply_le {t : ℝ} (ht : 0 ≤ t) (x : H) :
    ‖R.semigroup t x‖ ≤ ‖x‖ := by
  rw [R.semigroup_apply ht]; exact R.norm_semigroupLimit_le ht x

@[simp] theorem semigroup_zero : R.semigroup 0 = 1 := by
  ext x
  apply tendsto_nhds_unique (R.tendsto_semigroupApprox_apply (le_refl 0) x)
  simp

theorem tendsto_semigroupApprox_moving {t : ℝ} (ht : 0 ≤ t) {y : ℝ → H} {x : H}
    (hy : Tendsto y atTop (𝓝 x)) :
    Tendsto (fun b => R.semigroupApprox b t (y b)) atTop (𝓝 (R.semigroup t x)) := by
  have hzero : Tendsto (fun b => R.semigroupApprox b t (y b - x)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (show ∀ᶠ b : ℝ in atTop, ‖R.semigroupApprox b t (y b-x)‖ ≤ ‖y b-x‖ from ?_)
    · simpa using (hy.sub (tendsto_const_nhds (x := x))).norm
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb
      exact R.norm_semigroupApprox_apply_le hb ht _
  have h := hzero.add (R.tendsto_semigroupApprox_apply ht x)
  simpa using h

theorem semigroup_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    R.semigroup (s+t) = R.semigroup s * R.semigroup t := by
  ext x
  apply tendsto_nhds_unique (R.tendsto_semigroupApprox_apply (add_nonneg hs ht) x)
  simpa [R.semigroupApprox_add, mul_apply_eq_comp] using
    R.tendsto_semigroupApprox_moving hs (R.tendsto_semigroupApprox_apply ht x)

theorem tendstoUniformlyOn_semigroup (x : H) {T : ℝ} (hT : 0 ≤ T) :
    TendstoUniformlyOn (fun b t => R.semigroupApprox b t x) (fun t => R.semigroup t x)
      atTop (Icc 0 T) := by
  apply (R.tendstoUniformlyOn_semigroupApprox x hT).congr_right
  intro t ht
  exact (R.semigroup_apply ht.1 x).symm

theorem continuousOn_semigroup_Icc (x : H) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => R.semigroup t x) (Icc 0 T) :=
  (R.tendstoUniformlyOn_semigroup x hT).continuousOn (Eventually.frequently (Eventually.of_forall fun b =>
    (continuous_iff_continuousAt.mpr fun t =>
      (R.hasDerivAt_semigroupApprox_apply b t x).continuousAt).continuousOn))

theorem continuous_semigroup_apply (x : H) :
    ContinuousOn (fun t => R.semigroup t x) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  apply ((R.continuousOn_semigroup_Icc x (show 0 ≤ t+1 by linarith)).continuousWithinAt
    (show t ∈ Icc 0 (t+1) by exact ⟨ht, by linarith⟩)).mono_of_mem_nhdsWithin
  exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith)))

theorem norm_semigroup_sub_le {t : ℝ} (ht : 0 ≤ t) (x : R.dom) :
    ‖R.semigroup t x - x‖ ≤ t * ‖R.generator x‖ := by
  apply le_of_tendsto ((R.tendsto_semigroupApprox_apply ht x).sub tendsto_const_nhds).norm
  filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb
  exact R.norm_semigroupApprox_sub_self_generator_le hb ht x

end Foundations.ContractionResolvent
