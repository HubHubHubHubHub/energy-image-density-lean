import Foundations.Wiener.Coordinates
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace NNReal
namespace Foundations

abbrev haarMeasure : Measure ℝ := volume.restrict (Ico (0 : ℝ) 1)
abbrev HaarL2 := Lp ℝ 2 haarMeasure

instance isFiniteMeasure_haarMeasure : IsFiniteMeasure haarMeasure := by
  exact isFiniteMeasure_restrict.mpr (by simp)

def dyadicLp (j k : ℕ) : HaarL2 :=
  indicatorConstLp 2 measurableSet_Ico (measure_ne_top _ _) 1
    (s := dyadicCell j k)

theorem coe_dyadicLp (j k : ℕ) : dyadicLp j k =ᵐ[haarMeasure] dyadicIndicator j k :=
  indicatorConstLp_coeFn

def haarFamily : SchauderIndex → HaarL2
  | none => dyadicLp 0 0
  | some ⟨j,k⟩ => Real.sqrt ((2 : ℝ)^j) •
      (dyadicLp (j+1) (2*k) - dyadicLp (j+1) (2*k+1))

def haarFunction : SchauderIndex → ℝ → ℝ
  | none => dyadicIndicator 0 0
  | some ⟨j,k⟩ => haar j k

theorem coe_haarFamily (i : SchauderIndex) :
    haarFamily i =ᵐ[haarMeasure] haarFunction i := by
  cases i with
  | none => exact coe_dyadicLp 0 0
  | some p =>
    obtain ⟨j,k⟩ := p
    filter_upwards [Lp.coeFn_smul (Real.sqrt ((2 : ℝ)^j))
      (dyadicLp (j+1) (2*k) - dyadicLp (j+1) (2*k+1)),
      Lp.coeFn_sub (dyadicLp (j+1) (2*k)) (dyadicLp (j+1) (2*k+1)),
      coe_dyadicLp (j+1) (2*k), coe_dyadicLp (j+1) (2*k+1)] with x h1 h2 h3 h4
    change (_ • (_ - _) : HaarL2) x = _
    simp only [h1, Pi.smul_apply, smul_eq_mul, h2, Pi.sub_apply, h3, h4]
    rfl

theorem dyadicCell_subset_unit {j k : ℕ} (hk : k < 2^j) :
    dyadicCell j k ⊆ Ico (0 : ℝ) 1 := by
  intro x hx
  refine ⟨(by positivity : 0 ≤ (k : ℝ) / 2^j).trans hx.1, hx.2.trans_le ?_⟩
  rw [div_le_one (by positivity)]
  exact_mod_cast hk

theorem intervalIntegrable_haarL2 (g : HaarL2) : IntervalIntegrable g volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ico_of_le (by norm_num)).mpr
    ((Lp.memLp g).integrable (by norm_num))

theorem inner_dyadicLp (g : HaarL2) {j k : ℕ} (hk : k < 2^j) :
    ⟪dyadicLp j k, g⟫_ℝ =
      ∫ x in ((k : ℝ)/2^j)..(((k : ℝ)+1)/2^j), g x := by
  rw [dyadicLp, L2.inner_indicatorConstLp_one]
  change (∫ x, g x ∂(volume.restrict (Ico 0 1)).restrict (dyadicCell j k)) = _
  rw [Measure.restrict_restrict (show MeasurableSet (dyadicCell j k) from measurableSet_Ico),
    inter_eq_left.mpr (dyadicCell_subset_unit hk)]
  rw [intervalIntegral.integral_of_le (by gcongr <;> linarith),
    ← integral_Ico_eq_integral_Ioc]
  rfl

theorem inner_dyadicLp_primitive (g : HaarL2) {j k : ℕ} (hk : k < 2^j) :
    ⟪dyadicLp j k, g⟫_ℝ =
      (∫ x in (0 : ℝ)..(((k : ℝ)+1)/2^j), g x) -
      (∫ x in (0 : ℝ)..((k : ℝ)/2^j), g x) := by
  rw [inner_dyadicLp g hk]
  have ha : (k : ℝ)/2^j ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr (by exact_mod_cast hk.le)⟩
  have hb : ((k : ℝ)+1)/2^j ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr (by exact_mod_cast hk)⟩
  have h0a : IntervalIntegrable g volume 0 ((k : ℝ)/2^j) :=
    (intervalIntegrable_haarL2 g).mono_set (by
      rw [uIcc_of_le ha.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc le_rfl ha.2)
  have hab : IntervalIntegrable g volume ((k : ℝ)/2^j) (((k : ℝ)+1)/2^j) :=
    (intervalIntegrable_haarL2 g).mono_set (by
      rw [uIcc_of_le (show (k : ℝ)/2^j ≤ ((k : ℝ)+1)/2^j by gcongr <;> linarith),
        uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc ha.1 hb.2)
  have h := intervalIntegral.integral_add_adjacent_intervals h0a hab
  linarith

end Foundations
