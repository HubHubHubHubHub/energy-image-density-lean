import GeometricMeasure.VectorMeasure.Operations

/-! Affine dilations and pullbacks of compactly supported smooth tests. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped ENNReal Topology

namespace GeometricMeasure
variable {d : ℕ}

theorem preimage_closedBall_dilation (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (hr : r ≠ 0) (R : ℝ) :
    (dilationEquiv x₀ r hr) ⁻¹' Metric.closedBall 0 R =
      Metric.closedBall x₀ (|r| * R) := by
  ext x
  simp only [mem_preimage, Metric.mem_closedBall, dilationEquiv_apply, dist_eq_norm, sub_zero,
    norm_smul, Real.norm_eq_abs, abs_inv]
  rw [← div_eq_inv_mul, div_le_iff₀ (abs_pos.mpr hr), mul_comm R]

end GeometricMeasure
