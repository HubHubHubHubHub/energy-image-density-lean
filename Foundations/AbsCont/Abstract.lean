import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Foundations

/--
A finite Lᵖ bound on continuous compactly supported test functions forces absolute continuity.
The regularity assumption is on the sum measure and holds for locally finite Borel measures on
finite-dimensional real spaces. The density theorem used here is proved by regularity and Urysohn.
-/
theorem absolutelyContinuous_of_integral_le_eLpNorm
    {E : Type*} [TopologicalSpace E] [NormalSpace E] [R1Space E]
    [WeaklyLocallyCompactSpace E] [MeasurableSpace E] [BorelSpace E]
    {ν μ : Measure E} [IsFiniteMeasure ν] [(ν + μ).Regular]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ∞) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbound : ∀ f : E → ℝ, Continuous f → HasCompactSupport f →
      ‖∫ x, f x ∂ν‖ₑ ≤ M * eLpNorm f p μ) : ν ≪ μ := by
  classical
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hnull
  let f : E → ℝ := A.indicator (fun _ => 1)
  have hμA : (ν+μ) A ≠ ∞ := by simp [Measure.add_apply, hnull, measure_ne_top]
  have hf : MemLp f p (ν+μ) := memLp_indicator_const p hA 1 (Or.inr hμA)
  have hfν : Integrable f ν := (integrable_const (1:ℝ) (μ := ν)).indicator hA
  have hfzero : f =ᵐ[μ] 0 := by
    filter_upwards [show ∀ᵐ x ∂μ, x ∉ A from by simpa [ae_iff] using hnull] with x hx
    simp [f, hx]
  have hpr : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hpfin hp
  let C : ℝ≥0∞ := ν univ ^ (1 - 1 / p.toReal)
  have hC : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg
    (sub_nonneg.mpr ((div_le_one (by linarith)).mpr hpr)) (measure_ne_top _ _)
  let K : ℝ≥0∞ := C + M + 1
  have hK : K ≠ ∞ := by simp [K, hC, hM]
  have hK0 : K ≠ 0 := by simp [K]
  have hsmall (δ : ℝ≥0∞) (hδ : δ ≠ 0) : ν A ≤ K * δ := by
    obtain ⟨g, hgc, hg, hcont, hgp⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hpfin hδ
    have hνle : ν ≤ ν+μ := Measure.le_add_right le_rfl
    have hμle : μ ≤ ν+μ := Measure.le_add_left le_rfl
    have hgν : Integrable g ν := (hgp.mono_measure hνle).integrable hp
    have hsub : eLpNorm (f-g) p ν ≤ δ := (eLpNorm_mono_measure _ hνle).trans hg
    have hgμ : eLpNorm g p μ ≤ δ := by
      have heq : f-g =ᵐ[μ] -g := hfzero.mono fun x hx => by simp [Pi.sub_apply, hx]
      simpa [eLpNorm_congr_ae heq] using (eLpNorm_mono_measure (f-g) hμle).trans hg
    have hi : ‖∫ x, (f-g) x ∂ν‖ₑ ≤ δ*C := by
      apply (enorm_integral_le_lintegral_enorm _).trans
      rw [← eLpNorm_one_eq_lintegral_enorm]
      have H := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hfν.sub hgν).aestronglyMeasurable
      apply H.trans
      simpa only [ENNReal.toReal_one, div_one, C] using
        (show eLpNorm (f-g) p ν * C ≤ δ*C by gcongr)
    have hiA : ‖∫ x, f x ∂ν‖ₑ = ν A := by
      simp [f, integral_indicator hA, ENNReal.ofReal_toReal, measure_ne_top, Real.enorm_eq_ofReal_abs,
        abs_of_nonneg (measureReal_nonneg)]
    rw [← hiA, show (∫ x, f x ∂ν) = (∫ x, (f-g) x ∂ν) + ∫ x, g x ∂ν by
      simp only [Pi.sub_apply]
      rw [integral_sub hfν hgν]; ring]
    calc
      ‖(∫ x, (f-g) x ∂ν) + ∫ x, g x ∂ν‖ₑ ≤
          ‖∫ x, (f-g) x ∂ν‖ₑ + ‖∫ x, g x ∂ν‖ₑ := enorm_add_le _ _
      _ ≤ δ*C + M*δ := add_le_add hi ((hbound g hcont hgc).trans (mul_le_mul_left' hgμ M))
      _ ≤ K*δ := by dsimp [K]; rw [add_mul, add_mul]; simpa [mul_comm] using
        (le_add_right (le_refl ((C+M)*δ)) : (C+M)*δ ≤ (C+M)*δ+δ)
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have H := hsmall (ε/K) (ENNReal.div_ne_zero.mpr ⟨by exact_mod_cast hε.ne', hK⟩)
  simpa [ENNReal.mul_div_cancel hK0 hK] using H

end Foundations
