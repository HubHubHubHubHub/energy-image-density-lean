import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Foundations
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (μ : Measure α) {ν : Measure β}

/-- The square-integrable section, with zero as the value on bad sections. -/
def sectionLp (F : α × β → ℝ) (y : β) : Lp ℝ 2 μ := by
  classical
  exact if h : MemLp (fun x => F (x,y)) 2 μ then h.toLp _ else 0

omit [MeasurableSpace β] in
theorem sectionLp_of_memLp {F : α × β → ℝ} {y : β}
    (h : MemLp (fun x => F (x,y)) 2 μ) :
    sectionLp μ F y = h.toLp _ := by
  classical
  exact dif_pos h

omit [MeasurableSpace β] in
theorem sectionLp_congr {F G : α × β → ℝ} {y : β}
    (h : (fun x => F (x,y)) =ᵐ[μ] (fun x => G (x,y))) :
    sectionLp μ F y = sectionLp μ G y := by
  classical
  unfold sectionLp
  by_cases hf : MemLp (fun x => F (x,y)) 2 μ
  · rw [dif_pos hf, dif_pos (hf.ae_eq h)]
    exact hf.toLp_congr _ h
  · have hg : ¬ MemLp (fun x => G (x,y)) 2 μ := by
      intro hg
      exact hf (MemLp.ae_eq h.symm hg)
    rw [dif_neg hf, dif_neg hg]

theorem memLp_section_ae [SFinite μ] [SFinite ν] {F : α × β → ℝ}
    (hF : MemLp F 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, MemLp (fun x => F (x,y)) 2 μ := by
  filter_upwards [hF.1.prodMk_right, hF.integrable_sq.prod_left_ae] with y hy hi
  exact (memLp_two_iff_integrable_sq hy).2 hi

theorem coeFn_sectionLp [SFinite μ] [SFinite ν] {F : α × β → ℝ}
    (hF : MemLp F 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, (sectionLp μ F y : α → ℝ) =ᵐ[μ] fun x => F (x,y) := by
  filter_upwards [memLp_section_ae μ hF] with y hy
  rw [sectionLp_of_memLp μ hy]
  exact hy.coeFn_toLp

theorem sectionLp_congr_ae [SFinite μ] [SFinite ν] {F G : α × β → ℝ}
    (h : F =ᵐ[μ.prod ν] G) : sectionLp μ F =ᵐ[ν] sectionLp μ G := by
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq h
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with y hy
  exact sectionLp_congr μ hy

omit [MeasurableSpace β] in
theorem sectionLp_add_of_memLp {F G : α × β → ℝ} {y : β}
    (hf : MemLp (fun x => F (x,y)) 2 μ) (hg : MemLp (fun x => G (x,y)) 2 μ) :
    sectionLp μ (F + G) y = sectionLp μ F y + sectionLp μ G y := by
  rw [sectionLp_of_memLp μ (hf.add hg), sectionLp_of_memLp μ hf,
    sectionLp_of_memLp μ hg]
  exact hf.toLp_add hg

theorem sectionLp_add [SFinite μ] [SFinite ν] {F G : α × β → ℝ}
    (hf : MemLp F 2 (μ.prod ν)) (hg : MemLp G 2 (μ.prod ν)) :
    sectionLp μ (F + G) =ᵐ[ν] sectionLp μ F + sectionLp μ G := by
  filter_upwards [memLp_section_ae μ hf, memLp_section_ae μ hg] with y hy hz
  exact sectionLp_add_of_memLp μ hy hz

omit [MeasurableSpace β] in
theorem sectionLp_smul_of_memLp {F : α × β → ℝ} {y : β}
    (hf : MemLp (fun x => F (x,y)) 2 μ) (c : ℝ) :
    sectionLp μ (c • F) y = c • sectionLp μ F y := by
  rw [sectionLp_of_memLp μ (hf.const_smul c), sectionLp_of_memLp μ hf]
  apply Lp.ext
  exact (hf.const_smul c).coeFn_toLp.trans
    (((Lp.coeFn_smul c (hf.toLp _)).trans (hf.coeFn_toLp.const_smul c)).symm)

theorem sectionLp_smul [SFinite μ] [SFinite ν] {F : α × β → ℝ}
    (hf : MemLp F 2 (μ.prod ν)) (c : ℝ) :
    sectionLp μ (c • F) =ᵐ[ν] c • sectionLp μ F := by
  filter_upwards [memLp_section_ae μ hf] with y hy
  exact sectionLp_smul_of_memLp μ hy c

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
