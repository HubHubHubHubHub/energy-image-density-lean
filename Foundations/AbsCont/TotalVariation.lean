import Foundations.AbsCont.Mollify
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
namespace Foundations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [HasContDiffBump E] [MeasurableSpace E] [BorelSpace E]

/-- Expanding smooth cutoffs, equal to one on every fixed compact eventually. -/
def acCutoff (n : ℕ) (x : E) : ℝ :=
  (default : ContDiffBump (0:E)) ((n+1:ℝ)⁻¹ • x)

theorem contDiff_acCutoff (n : ℕ) : ContDiff ℝ ∞ (acCutoff (E := E) n) :=
  (default : ContDiffBump (0:E)).contDiff.comp (contDiff_const.smul contDiff_id)

theorem hasCompactSupport_acCutoff (n : ℕ) : HasCompactSupport (acCutoff (E := E) n) :=
  (default : ContDiffBump (0:E)).hasCompactSupport.comp_smul (by positivity)

theorem acCutoff_mem_Icc (n : ℕ) (x : E) : acCutoff n x ∈ Icc (0:ℝ) 1 :=
  ⟨(default : ContDiffBump (0:E)).nonneg, (default : ContDiffBump (0:E)).le_one⟩

theorem tendsto_acCutoff (x : E) : Tendsto (fun n => acCutoff n x) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => (n+1:ℝ)⁻¹ • x) atTop (𝓝 (0:E)) := by
    simpa only [one_div, zero_smul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const x
  have h0 : (default : ContDiffBump (0:E)) 0 = 1 :=
    (default : ContDiffBump (0:E)).one_of_mem_closedBall (by simpa using (default : ContDiffBump (0:E)).rIn_pos.le)
  simpa only [acCutoff, h0, Function.comp_def] using (default : ContDiffBump (0:E)).continuous.tendsto 0 |>.comp ht

/-- Continuous compact tests suffice to compute the total variation of a continuous L¹ density. -/
theorem integral_norm_le_of_test_bound {μ : Measure E} {h : E → ℝ}
    (hc : Continuous h) (hi : Integrable h μ) {C : ℝ}
    (hb : ∀ ψ : E → ℝ, Continuous ψ → HasCompactSupport ψ →
      (∀ x, ‖ψ x‖ ≤ 1) → |∫ x, ψ x * h x ∂μ| ≤ C) : ∫ x, ‖h x‖ ∂μ ≤ C := by
  let δ : ℕ → ℝ := fun n => 1/(n+1:ℝ)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  let ψ : ℕ → E → ℝ := fun n x => acCutoff n x * (h x / (|h x| + δ n))
  have hψc (n : ℕ) : Continuous (ψ n) :=
    (contDiff_acCutoff n).continuous.mul (hc.div (hc.abs.add continuous_const)
      (fun x => ne_of_gt (add_pos_of_nonneg_of_pos (abs_nonneg _) (hδ n))))
  have hψk (n : ℕ) : HasCompactSupport (ψ n) :=
    (hasCompactSupport_acCutoff n).mul_right
  have hψb (n : ℕ) (x : E) : ‖ψ n x‖ ≤ 1 := by
    have hd : 0 < |h x| + δ n := add_pos_of_nonneg_of_pos (abs_nonneg _) (hδ n)
    have hr : |h x| / (|h x| + δ n) ≤ 1 := (div_le_one hd).mpr (by linarith [hδ n])
    simp only [ψ, norm_mul, Real.norm_eq_abs, abs_div, abs_of_pos hd,
      abs_of_nonneg (acCutoff_mem_Icc n x).1]
    exact mul_le_one₀ (acCutoff_mem_Icc n x).2 (by positivity) hr
  have hp (x : E) : Tendsto (fun n => ψ n x * h x) atTop (𝓝 ‖h x‖) := by
    by_cases hx : h x = 0
    · simp [ψ, hx]
    · have ha : |h x| ≠ 0 := abs_ne_zero.mpr hx
      have H := ((tendsto_acCutoff x).mul ((tendsto_const_nhds (x := h x)).div
        ((tendsto_const_nhds (x := |h x|)).add tendsto_one_div_add_atTop_nhds_zero_nat)
        (by simpa using ha))).mul_const (h x)
      have he : (1:ℝ) * (h x / (|h x| + 0)) * h x = ‖h x‖ := by
        rw [Real.norm_eq_abs]
        field_simp
        nlinarith [sq_abs (h x)]
      simpa only [ψ, δ, he, Pi.div_apply] using H
  have hlim : Tendsto (fun n => ∫ x, ψ n x * h x ∂μ) atTop (𝓝 (∫ x, ‖h x‖ ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖h x‖)
    · intro n; exact ((hψc n).mul hc).aestronglyMeasurable
    · exact hi.norm
    · intro n
      exact Eventually.of_forall fun x => by
        rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hψb n x)
    · exact Eventually.of_forall hp
  exact le_of_tendsto' hlim fun n => (le_abs_self _).trans (hb _ (hψc n) (hψk n) (hψb n))

end Foundations
