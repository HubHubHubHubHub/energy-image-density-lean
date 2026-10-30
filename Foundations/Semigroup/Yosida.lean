import Foundations.Semigroup.Resolvent
import Foundations.Semigroup.Exponential
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Filter Topology
namespace Foundations.ContractionResolvent
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (R : ContractionResolvent H)

def yosida (b : ℝ) : H →L[ℝ] H := b • (b • R.G b - 1)

theorem yosida_eq (b : ℝ) : R.yosida b = b^2 • R.G b - b • 1 := by
  unfold yosida
  rw [smul_sub, smul_smul, pow_two]

theorem yosida_commute {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Commute (R.yosida a) (R.yosida b) := by
  exact (((R.commute_G ha hb).smul_left a |>.smul_right b).sub_right
    (Commute.one_right _)).sub_left (Commute.one_left _) |>.smul_left a |>.smul_right b

theorem yosida_commute_G {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Commute (R.yosida a) (R.G b) := by
  exact ((R.commute_G ha hb).smul_left a |>.sub_left (Commute.one_left _)).smul_left a

theorem yosida_apply (b : ℝ) (x : H) : R.yosida b x = b • (b • R.G b x - x) := rfl

theorem yosida_generator {b : ℝ} (hb : 0 < b) (x : R.dom) :
    R.yosida b x = b • R.G b (R.generator x) := by
  have h := R.G_generator hb x
  rw [map_sub, map_smul] at h
  rw [yosida_apply]
  congr 1
  linear_combination (norm := module) h

theorem tendsto_yosida (x : R.dom) :
    Tendsto (fun b => R.yosida b x) atTop (𝓝 (R.generator x)) := by
  apply (R.tendsto_id (R.generator x)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  exact (R.yosida_generator hb x).symm

variable [CompleteSpace H]
def semigroupApprox (b t : ℝ) : H →L[ℝ] H := NormedSpace.exp (t • R.yosida b)

omit [CompleteSpace H] in
@[simp] theorem semigroupApprox_zero (b : ℝ) : R.semigroupApprox b 0 = 1 := by
  simp [semigroupApprox]

theorem semigroupApprox_add (b s t : ℝ) :
    R.semigroupApprox b (s+t) = R.semigroupApprox b s * R.semigroupApprox b t := by
  letI : NormedAlgebra ℚ (H →L[ℝ] H) := .restrictScalars ℚ ℝ _
  rw [semigroupApprox, add_smul]
  exact NormedSpace.exp_add_of_commute ((Commute.refl _).smul_left s |>.smul_right t)

omit [CompleteSpace H] in
theorem semigroupApprox_commute_yosida {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    Commute (R.semigroupApprox a t) (R.yosida b) :=
  ((R.yosida_commute ha hb).smul_left t).exp_left

omit [CompleteSpace H] in
theorem semigroupApprox_commute_G {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    Commute (R.semigroupApprox a t) (R.G b) :=
  ((R.yosida_commute_G ha hb).smul_left t).exp_left

omit [CompleteSpace H] in
theorem semigroupApprox_commute {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s t : ℝ) :
    Commute (R.semigroupApprox a s) (R.semigroupApprox b t) :=
  ((R.yosida_commute ha hb).smul_left s |>.smul_right t).exp

theorem semigroupApprox_factor (b t : ℝ) :
    R.semigroupApprox b t = Real.exp (-(t*b)) •
      NormedSpace.exp ((t*b) • (b • R.G b)) := by
  letI : NormedAlgebra ℚ (H →L[ℝ] H) := .restrictScalars ℚ ℝ _
  have he : t • R.yosida b = (-(t*b)) • (1 : H →L[ℝ] H) + (t*b) • (b • R.G b) := by
    unfold yosida; module
  rw [semigroupApprox, he, NormedSpace.exp_add_of_commute
    (((Commute.one_left _).smul_left (-(t*b))).smul_right (t*b)),
    exp_real_smul_one, smul_mul_assoc, one_mul]

theorem norm_semigroupApprox_le_one {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    ‖R.semigroupApprox b t‖ ≤ 1 := by
  nontriviality H
  rw [R.semigroupApprox_factor, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-(t*b)) * Real.exp ‖(t*b) • (b • R.G b)‖ :=
      mul_le_mul_of_nonneg_left (norm_exp_le_real_exp_norm _) (Real.exp_pos _).le
    _ ≤ Real.exp (-(t*b)) * Real.exp (t*b) := by
      gcongr
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht hb.le)]
      simpa using mul_le_mul_of_nonneg_left (R.norm_le hb) (mul_nonneg ht hb.le)
    _ = 1 := by rw [← Real.exp_add]; simp

theorem norm_semigroupApprox_apply_le {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) (x : H) :
    ‖R.semigroupApprox b t x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using
    (R.semigroupApprox b t).le_of_opNorm_le (R.norm_semigroupApprox_le_one hb ht) x

theorem hasDerivAt_semigroupApprox (b t : ℝ) :
    HasDerivAt (R.semigroupApprox b) (R.semigroupApprox b t * R.yosida b) t :=
  hasDerivAt_exp_smul_const (R.yosida b) t

theorem hasDerivAt_semigroupApprox_apply (b t : ℝ) (x : H) :
    HasDerivAt (fun s => R.semigroupApprox b s x) (R.semigroupApprox b t (R.yosida b x)) t := by
  simpa using (R.hasDerivAt_semigroupApprox b t).clm_apply (hasDerivAt_const t x)

theorem continuous_semigroupApprox (b : ℝ) : Continuous (R.semigroupApprox b) :=
  continuous_iff_continuousAt.mpr fun t => (R.hasDerivAt_semigroupApprox b t).continuousAt

end Foundations.ContractionResolvent
