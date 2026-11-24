import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Norm and dominated convergence of `L²` classes

This file contains the results of the development of `Foundations.Sections.Basic` that the main
statements of the library (the head theorems listed in the README of the repository) use.
`Foundations.Sections.Basic` imports it and continues the development.

## Main statements

* `tendsto_toLp_dominated`: Dominated pointwise convergence implies convergence of the associated L²
  classes.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Foundations
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (μ : Measure α)

/-- The squared norm in real L², expressed using any square-integrable representative. -/
theorem norm_toLp_sq {f : α → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx, pow_two]

/-- Dominated pointwise convergence implies convergence of the associated L² classes. -/
theorem tendsto_toLp_dominated {f : ℕ → α → ℝ} {g b : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ) (hb : MemLp b 2 μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hsq : Tendsto (fun n => ∫ x, (f n x - g x)^2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (F := fun n x => (f n x - g x)^2) (f := fun _ => (0 : ℝ))
      (fun x => (b x + ‖g x‖)^2)
      (fun n => ((hf n).1.sub hg.1).pow 2) (hb.add hg.norm).integrable_sq
    apply (by simpa only [integral_zero] using h : _ → _ → _)
    · intro n
      filter_upwards [hbound n] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc
        (f n x - g x)^2 = ‖f n x - g x‖^2 := by simp
        _ ≤ (b x + ‖g x‖)^2 := by
          apply pow_le_pow_left₀ (norm_nonneg _)
          have hn := norm_sub_le (f n x) (g x)
          linarith
    · filter_upwards [hlim] with x hx
      simpa using (hx.sub_const (g x)).pow 2
  have hn : ∀ n, ‖(hf n).toLp (f n) - hg.toLp g‖ =
      Real.sqrt (∫ x, (f n x - g x)^2 ∂μ) := by
    intro n
    change ‖((hf n).sub hg).toLp (f n - g)‖ = _
    have he := norm_toLp_sq μ ((hf n).sub hg)
    simp only [Pi.sub_apply] at he
    rw [← he, Real.sqrt_sq (norm_nonneg _)]
  rw [tendsto_iff_dist_tendsto_zero]
  simp_rw [dist_eq_norm, hn]
  simpa only [Function.comp_def, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq

end Foundations
