import Foundations.HaarBasis.Complete

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace NNReal
namespace Foundations

def haarIndicator (t : WienerTime) : HaarL2 :=
  indicatorConstLp 2 measurableSet_Ico (measure_ne_top _ _) 1 (s := Ico (0 : ℝ) (t : ℝ≥0))

theorem inner_haarIndicator (t : WienerTime) (g : HaarL2) :
    ⟪haarIndicator t, g⟫_ℝ = ∫ x in (0 : ℝ)..(t : ℝ≥0), g x := by
  rw [haarIndicator, L2.inner_indicatorConstLp_one]
  change (∫ x, g x ∂(volume.restrict (Ico (0 : ℝ) 1)).restrict (Ico (0 : ℝ) (t : ℝ≥0))) = _
  rw [Measure.restrict_restrict measurableSet_Ico,
    inter_eq_left.mpr (Ico_subset_Ico le_rfl (by exact_mod_cast t.property.2)),
    intervalIntegral.integral_of_le (t : ℝ≥0).coe_nonneg, ← integral_Ico_eq_integral_Ioc]

theorem haar_coeff_indicator (t : WienerTime) (i : SchauderIndex) :
    ⟪haarIndicator t, haarFamily i⟫_ℝ = schauderCoefficient i t := by
  rw [inner_haarIndicator, primitive_haarFamily i
    ⟨(t : ℝ≥0).coe_nonneg, by exact_mod_cast t.property.2⟩]
  cases i <;> rfl

theorem haarBasis_repr_indicator (t : WienerTime) (i : SchauderIndex) :
    haarBasis.repr (haarIndicator t) i = schauderCoefficient i t := by
  rw [HilbertBasis.repr_apply_apply, haarBasis_apply, real_inner_comm, haar_coeff_indicator]

theorem norm_haarIndicator_sq (t : WienerTime) : ‖haarIndicator t‖^2 = (t : ℝ≥0) := by
  rw [← real_inner_self_eq_norm_sq, haarIndicator,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one, inter_self]
  rw [measureReal_restrict_apply measurableSet_Ico,
    inter_eq_left.mpr (Ico_subset_Ico le_rfl (by exact_mod_cast t.property.2))]
  simp [Real.volume_real_Ico, (t : ℝ≥0).coe_nonneg]

theorem norm_haarIndicator_le_one (t : WienerTime) : ‖haarIndicator t‖ ≤ 1 := by
  have h := norm_haarIndicator_sq t
  have ht : ((t : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast t.property.2
  nlinarith [norm_nonneg (haarIndicator t)]

theorem hasSum_haar_expansion (g : HaarL2) :
    HasSum (fun i => ⟪haarFamily i,g⟫_ℝ • haarFamily i) g := by
  simpa only [HilbertBasis.repr_apply_apply,haarBasis_apply] using haarBasis.hasSum_repr g

end Foundations
