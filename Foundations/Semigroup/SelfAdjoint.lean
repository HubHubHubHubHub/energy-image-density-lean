import Foundations.Semigroup.Generator
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace Foundations.ContractionResolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (R : ContractionResolvent H)

def IsSelfAdjointResolvent : Prop := ∀ b > 0, IsSelfAdjoint (R.G b)

theorem yosida_selfAdjoint (hR : R.IsSelfAdjointResolvent) {b : ℝ} (hb : 0 < b) :
    IsSelfAdjoint (R.yosida b) := by
  unfold yosida
  simp only [IsSelfAdjoint, star_smul, star_sub, star_one, star_trivial, hR b hb |>.star_eq]

theorem semigroupApprox_selfAdjoint (hR : R.IsSelfAdjointResolvent) {b : ℝ} (hb : 0 < b)
    (t : ℝ) : IsSelfAdjoint (R.semigroupApprox b t) := by
  apply IsSelfAdjoint.exp
  simp only [IsSelfAdjoint, star_smul, star_trivial, (R.yosida_selfAdjoint hR hb).star_eq]

theorem semigroup_selfAdjoint (hR : R.IsSelfAdjointResolvent) {t : ℝ} (ht : 0 ≤ t) :
    IsSelfAdjoint (R.semigroup t) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  apply tendsto_nhds_unique
    ((R.tendsto_semigroupApprox_apply ht x).inner tendsto_const_nhds)
  apply ((tendsto_const_nhds (x := x)).inner (R.tendsto_semigroupApprox_apply ht y)).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb
  exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (R.semigroupApprox_selfAdjoint hR hb t)) x y).symm

theorem inner_semigroup_self_nonneg (hR : R.IsSelfAdjointResolvent) {t : ℝ}
    (ht : 0 ≤ t) (x : H) : 0 ≤ ⟪R.semigroup t x, x⟫_ℝ := by
  have ht2 : 0 ≤ t/2 := by positivity
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (R.semigroup_selfAdjoint hR ht2)
  have he : t = t/2+t/2 := by ring
  rw [he, R.semigroup_add ht2 ht2, mul_apply_eq_comp]
  have hi : ⟪R.semigroup (t/2) (R.semigroup (t/2) x), x⟫_ℝ =
      ⟪R.semigroup (t/2) x, R.semigroup (t/2) x⟫_ℝ := hsym _ _
  rw [hi]
  exact real_inner_self_nonneg

omit [CompleteSpace H] in
theorem inner_yosida_self_nonpos {b : ℝ} (hb : 0 < b) (x : H) :
    ⟪R.yosida b x, x⟫_ℝ ≤ 0 := by
  have hn : ‖b • R.G b x‖ ≤ ‖x‖ :=
    (b • R.G b).le_opNorm x |>.trans (by
      simpa using mul_le_mul_of_nonneg_right (R.norm_le hb) (norm_nonneg x))
  have hi := real_inner_le_norm (b • R.G b x) x
  rw [R.yosida_apply, real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq]
  apply mul_nonpos_of_nonneg_of_nonpos hb.le
  nlinarith [mul_le_mul_of_nonneg_right hn (norm_nonneg x)]

omit [CompleteSpace H] in
theorem inner_generator_self_nonpos (x : R.dom) : ⟪R.generator x, (x:H)⟫_ℝ ≤ 0 := by
  apply le_of_tendsto ((R.tendsto_yosida x).inner (tendsto_const_nhds (x := (x:H))))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb
  exact R.inner_yosida_self_nonpos hb x

end Foundations.ContractionResolvent
