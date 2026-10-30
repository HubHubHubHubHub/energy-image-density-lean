import Foundations.Sections.Measurable

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Foundations
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The section norm, without requiring measurability of the class-valued map. -/
theorem norm_sq_sectionLp_ae {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    (fun y => ‖sectionLp μ F y‖^2) =ᵐ[ν] (fun y => ∫ x, F (x,y)^2 ∂μ) := by
  filter_upwards [memLp_section_ae μ hF] with y hy
  rw [sectionLp_of_memLp μ hy, norm_toLp_sq]

theorem memLp_sectionLp {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    MemLp (sectionLp μ F) 2 ν := by
  apply (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_sectionLp μ hF)).2
  have hi : Integrable (fun y => ∫ x, F (x,y)^2 ∂μ) ν := by
    simpa only [Real.norm_eq_abs, abs_sq] using
      hF.integrable_sq.integral_norm_prod_right
  exact hi.congr (norm_sq_sectionLp_ae μ ν hF).symm

theorem integral_norm_sq_sectionLp {F : α × β → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    ∫ y, ‖sectionLp μ F y‖^2 ∂ν = ∫ z, F z ^ 2 ∂μ.prod ν := by
  rw [integral_congr_ae (norm_sq_sectionLp_ae μ ν hF)]
  exact (integral_prod_symm _ hF.integrable_sq).symm

omit [IsFiniteMeasure ν] in
/-- The norm formula for an L² class with real Hilbert-space values. -/
theorem norm_toLp_sq_hilbert {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : β → E} (hf : MemLp f 2 ν) :
    ‖hf.toLp f‖^2 = ∫ y, ‖f y‖^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with y hy
  simp [hy]

/-- Fubini isometry, sending a joint class to its sections in the first variable. -/
def sectionLpₗᵢ : Lp ℝ 2 (μ.prod ν) →ₗᵢ[ℝ] Lp (Lp ℝ 2 μ) 2 ν where
  toFun F := (memLp_sectionLp μ ν (Lp.memLp F)).toLp (sectionLp μ F)
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(memLp_sectionLp μ ν (Lp.memLp (F+G))).coeFn_toLp,
      Lp.coeFn_add ((memLp_sectionLp μ ν (Lp.memLp F)).toLp _) ((memLp_sectionLp μ ν (Lp.memLp G)).toLp _),
      (memLp_sectionLp μ ν (Lp.memLp F)).coeFn_toLp,
      (memLp_sectionLp μ ν (Lp.memLp G)).coeFn_toLp,
      sectionLp_congr_ae μ (Lp.coeFn_add F G), sectionLp_add μ (Lp.memLp F) (Lp.memLp G)] with y h1 h2 h3 h4 h5 h6
    simpa only [Pi.add_apply] using h1.trans (h5.trans (h6.trans (by rw [h2]; simp only [Pi.add_apply, h3, h4])))
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(memLp_sectionLp μ ν (Lp.memLp (c • F))).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_sectionLp μ ν (Lp.memLp F)).toLp _),
      (memLp_sectionLp μ ν (Lp.memLp F)).coeFn_toLp,
      sectionLp_congr_ae μ (Lp.coeFn_smul c F), sectionLp_smul μ (Lp.memLp F) c] with y h1 h2 h3 h4 h5
    simpa only [Pi.smul_apply, RingHom.id_apply] using h1.trans (h4.trans (h5.trans (by rw [h2]; simp only [Pi.smul_apply, h3])))
  norm_map' F := by
    have h := norm_toLp_sq_hilbert ν (memLp_sectionLp μ ν (Lp.memLp F))
    rw [integral_norm_sq_sectionLp μ ν (Lp.memLp F), ← norm_toLp_sq (μ.prod ν) (Lp.memLp F),
      Lp.toLp_coeFn] at h
    change ‖(memLp_sectionLp μ ν (Lp.memLp F)).toLp (sectionLp μ F)‖ = ‖F‖
    nlinarith [norm_nonneg F, norm_nonneg ((memLp_sectionLp μ ν (Lp.memLp F)).toLp (sectionLp μ F))]

theorem coeFn_sectionLpₗᵢ (F : Lp ℝ 2 (μ.prod ν)) :
    (sectionLpₗᵢ μ ν F : β → Lp ℝ 2 μ) =ᵐ[ν] sectionLp μ F :=
  (memLp_sectionLp μ ν (Lp.memLp F)).coeFn_toLp

end Foundations
