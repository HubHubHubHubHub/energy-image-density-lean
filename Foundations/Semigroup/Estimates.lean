import Foundations.Semigroup.Yosida
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Filter Topology Set
namespace Foundations.ContractionResolvent
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable (R : ContractionResolvent H)

theorem hasDerivAt_bridge {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t s : ℝ) (x : H) :
    HasDerivAt (fun r => R.semigroupApprox b (t-r) (R.semigroupApprox a r x))
      (R.semigroupApprox b (t-s) (R.semigroupApprox a s (R.yosida a x - R.yosida b x))) s := by
  have hd := ((R.hasDerivAt_semigroupApprox b (t-s)).scomp s
    ((hasDerivAt_id s).const_sub t)).clm_apply (R.hasDerivAt_semigroupApprox_apply a s x)
  have hc := congrArg (fun f : H →L[ℝ] H => f x)
    (R.semigroupApprox_commute_yosida ha hb s).eq
  change R.semigroupApprox a s (R.yosida b x) = R.yosida b (R.semigroupApprox a s x) at hc
  convert hd using 1 <;>
    simp only [Function.comp_apply, neg_smul, one_smul, neg_apply, mul_apply_eq_comp,
      map_sub, ← hc]
  abel

theorem norm_semigroupApprox_sub_le {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : 0 ≤ t) (x : H) :
    ‖R.semigroupApprox a t x - R.semigroupApprox b t x‖ ≤ t * ‖R.yosida a x - R.yosida b x‖ := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s (_ : s ∈ Icc 0 t) => (R.hasDerivAt_bridge ha hb t s x).hasDerivWithinAt)
    (fun s (hs : s ∈ Ico 0 t) =>
      (R.norm_semigroupApprox_apply_le hb (sub_nonneg.mpr hs.2.le) _).trans
        (R.norm_semigroupApprox_apply_le ha hs.1 _)) t (right_mem_Icc.mpr ht)
  simpa [sub_self, sub_zero, mul_comm] using h

theorem norm_semigroupApprox_sub_self_le {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) (x : H) :
    ‖R.semigroupApprox b t x - x‖ ≤ t * ‖R.yosida b x‖ := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s (_ : s ∈ Icc 0 t) => (R.hasDerivAt_semigroupApprox_apply b s x).hasDerivWithinAt)
    (fun s (hs : s ∈ Ico 0 t) => R.norm_semigroupApprox_apply_le hb hs.1 _) t
    (right_mem_Icc.mpr ht)
  simpa [mul_comm] using h

theorem norm_semigroupApprox_sub_self_generator_le {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t)
    (x : R.dom) : ‖R.semigroupApprox b t x - x‖ ≤ t * ‖R.generator x‖ := by
  apply (R.norm_semigroupApprox_sub_self_le hb ht x).trans
  apply mul_le_mul_of_nonneg_left _ ht
  rw [R.yosida_generator hb]
  exact (b • R.G b).le_opNorm (R.generator x) |>.trans (by
    simpa using mul_le_mul_of_nonneg_right (R.norm_le hb) (norm_nonneg (R.generator x)))

end Foundations.ContractionResolvent
