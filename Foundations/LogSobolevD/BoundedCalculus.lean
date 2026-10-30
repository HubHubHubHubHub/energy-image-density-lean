import Foundations.LogSobolevD.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem partialD_comp {f : (ι → ℝ) → ℝ} {φ : ℝ → ℝ}
    (hf : IsC1BoundedD f) (x : ι → ℝ) (hφ : DifferentiableAt ℝ φ (f x)) (i : ι) :
    partialD (fun y => φ (f y)) i x = deriv φ (f x)*partialD f i x := by
  have hd := hφ.hasDerivAt.comp_hasFDerivAt x (hf.hasFDerivAt x)
  simpa [partialD,Function.comp_def] using congrArg
    (fun L : (ι → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) hd.fderiv

theorem IsC1BoundedD.comp_of_compact {f : (ι → ℝ) → ℝ} {φ : ℝ → ℝ} (hf : IsC1BoundedD f)
    {a b : ℝ} {U : Set ℝ} (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U)
    (hab : Icc a b ⊆ U) (hr : ∀ x, f x ∈ Icc a b) :
    IsC1BoundedD (fun x => φ (f x)) := by
  have hp (x : ι → ℝ) := (hφ.contDiffAt (hU.mem_nhds (hab (hr x)))).differentiableAt (by norm_num)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφ.continuousOn.mono hab)
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hφ.continuousOn_deriv_of_isOpen hU le_rfl).mono hab)
  refine ⟨contDiff_iff_contDiffAt.mpr (fun x =>
    (hφ.contDiffAt (hU.mem_nhds (hab (hr x)))).comp x hf.contDiff.contDiffAt),
    ⟨C,fun x => hC _ (hr x)⟩,fun i => ?_⟩
  obtain ⟨E,hE⟩ := hf.partial_bounded i
  refine ⟨D*E,fun x => ?_⟩
  rw [partialD_comp hf x (hp x),norm_mul]
  exact mul_le_mul (hD _ (hr x)) (hE x) (norm_nonneg _)
    ((norm_nonneg _).trans (hD _ (hr 0)))

theorem partialD_log {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (x : ι → ℝ)
    (hne : f x ≠ 0) (i : ι) :
    partialD (fun x => Real.log (f x)) i x = partialD f i x/f x := by
  rw [partialD_comp hf x (Real.differentiableAt_log hne),Real.deriv_log]
  ring

theorem IsC1BoundedD.log {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) : IsC1BoundedD (fun x => Real.log (f x)) := by
  obtain ⟨C,hC⟩ := hf.bounded
  have hne : ∀ x, f x ≠ 0 := fun x => (hε.trans_le (hpos x)).ne'
  refine ⟨hf.contDiff.log hne,⟨‖Real.log ε‖+‖Real.log C‖,fun x =>
    norm_log_le_of_bounds hε (hpos x) ((le_abs_self _).trans (hC x))⟩,fun i => ?_⟩
  obtain ⟨D,hD⟩ := hf.partial_bounded i
  refine ⟨D/ε,fun x => ?_⟩
  rw [partialD_log hf x (hne x),norm_div,Real.norm_of_nonneg (hε.le.trans (hpos x))]
  exact div_le_div₀ ((norm_nonneg _).trans (hD x)) (hD x) hε (hpos x)

end Foundations
