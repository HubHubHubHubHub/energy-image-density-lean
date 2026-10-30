import Foundations.CameronMartin.Exponential
import Mathlib.MeasureTheory.Function.LpOrder

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Topology
namespace Foundations

theorem abs_exp_sub_exp_le (x y : ℝ) :
    |Real.exp x-Real.exp y| ≤ |x-y| *(Real.exp x+Real.exp y) := by
  suffices h : ∀ x y : ℝ, x ≤ y → Real.exp y-Real.exp x ≤ (y-x)*(Real.exp x+Real.exp y) by
    rcases le_total x y with hxy | hyx
    · simpa [abs_of_nonpos (sub_nonpos.mpr hxy),abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hxy))] using h x y hxy
    · simpa [abs_of_nonneg (sub_nonneg.mpr hyx),abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hyx)),add_comm] using h y x hyx
  intro x y hxy
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (x-y)) (Real.exp_pos y).le
  rw [← Real.exp_add] at h
  have he : x-y+y=x := by ring
  rw [he] at h
  have hp : 0 ≤ (y-x)*Real.exp x := mul_nonneg (sub_nonneg.mpr hxy) (Real.exp_pos x).le
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

theorem integral_abs_exp_sub_le (X Y : Lp ℝ 2 P)
    (hX : MemLp (fun x => Real.exp (X x)) 2 P)
    (hY : MemLp (fun x => Real.exp (Y x)) 2 P) :
    (∫ x, |Real.exp (X x)-Real.exp (Y x)| ∂P) ≤
      ‖X-Y‖*(‖hX.toLp _‖+‖hY.toLp _‖) := by
  let U := hX.toLp (fun x => Real.exp (X x))
  let V := hY.toLp (fun x => Real.exp (Y x))
  have he : (∫ x, |X x-Y x| *(Real.exp (X x)+Real.exp (Y x)) ∂P) =
      ⟪|X-Y|,U+V⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_abs (X-Y),Lp.coeFn_sub X Y,Lp.coeFn_add U V,
      hX.coeFn_toLp,hY.coeFn_toLp] with x ha hs hp hu hv
    change |X x-Y x| * (Real.exp (X x)+Real.exp (Y x)) = (U+V) x * |X-Y| x
    rw [ha,hs,hp]
    simp only [Pi.sub_apply,Pi.add_apply]
    change _ = (hX.toLp _ x+hY.toLp _ x) * |X x-Y x|
    rw [hu,hv]
    ring
  have hp : Integrable (fun x => |X x-Y x| *(Real.exp (X x)+Real.exp (Y x))) P :=
    ((Lp.memLp X).sub (Lp.memLp Y)).norm.integrable_mul (hX.add hY)
  calc
    _ ≤ ∫ x, |X x-Y x| *(Real.exp (X x)+Real.exp (Y x)) ∂P :=
      integral_mono ((hX.sub hY).integrable (by norm_num)).norm hp
        (fun x => abs_exp_sub_exp_le _ _)
    _ = ⟪|X-Y|,U+V⟫_ℝ := he
    _ ≤ ‖|X-Y|‖*‖U+V‖ := real_inner_le_norm _ _
    _ ≤ ‖X-Y‖*(‖U‖+‖V‖) := by
      rw [norm_abs_eq_norm]
      exact mul_le_mul_of_nonneg_left (norm_add_le U V) (norm_nonneg _)

end Foundations
