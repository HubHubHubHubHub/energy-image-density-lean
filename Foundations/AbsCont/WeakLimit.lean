import Foundations.AbsCont.Abstract
import Foundations.AbsCont.Mollify

noncomputable section
open MeasureTheory Filter Set Function ContinuousLinearMap
open scoped Topology ENNReal ContDiff Convolution
namespace Foundations
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [HasContDiffBump E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- Convolution with a positive mass-one kernel contracts the uniform bound. -/
theorem norm_acKernel_convolution_le {f : E → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) (n : ℕ) (x : E) :
    ‖(acKernel n ⋆[lsmul ℝ ℝ] f) x‖ ≤ C := by
  simpa only [dist_zero_right] using
    dist_convolution_le (μ := (volume : Measure E)) (x₀ := x) (z₀ := (0:ℝ))
      (R := (acMollifier E n).rOut) hC
      (by simpa [acKernel] using (acMollifier E n).support_normed_eq (μ := volume) |>.subset)
      (acKernel_nonneg n) (integral_acKernel n) hf.aestronglyMeasurable
      (fun z _ => by simpa using hb z)

theorem tendsto_acKernel_convolution {f : E → ℝ} (hf : Continuous f) (x : E) :
    Tendsto (fun n => (acKernel n ⋆[lsmul ℝ ℝ] f) x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous
    (show Tendsto (fun n => (acMollifier E n).rOut) atTop (𝓝 0) from
      tendsto_one_div_add_atTop_nhds_zero_nat) hf x

variable (ν : Measure E) [IsFiniteMeasure ν]

theorem integral_mul_measureMollify {f : E → ℝ} (hf : Continuous f)
    (hfk : HasCompactSupport f) (n : ℕ) :
    (∫ x, f x * measureMollify ν n x) = ∫ y, (acKernel n ⋆[lsmul ℝ ℝ] f) y ∂ν := by
  obtain ⟨C,hC⟩ := hfk.exists_bound_of_continuous hf
  have hj := (integrable_acKernel_sub ν n).bdd_mul (hf.comp continuous_fst).aestronglyMeasurable
    (Eventually.of_forall fun z : E × E => hC z.1)
  simp_rw [measureMollify, ← integral_const_mul]
  rw [integral_integral_swap hj]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    rw [convolution_lsmul_swap]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      have H := acKernel_neg n (x-y)
      rw [neg_sub] at H
      simp only [smul_eq_mul, H]
      ring

/-- Weak convergence against compact continuous tests, with a finite-measure domination. -/
theorem tendsto_integral_mul_measureMollify {f : E → ℝ}
    (hf : Continuous f) (hfk : HasCompactSupport f) :
    Tendsto (fun n => ∫ x, f x * measureMollify ν n x) atTop (𝓝 (∫ x, f x ∂ν)) := by
  simp_rw [integral_mul_measureMollify ν hf hfk]
  obtain ⟨C,hC⟩ := hfk.exists_bound_of_continuous hf
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  apply tendsto_integral_of_dominated_convergence (fun _ => C)
  · intro n
    exact ((hasCompactSupport_acKernel n).continuous_convolution_left (lsmul ℝ ℝ)
      (contDiff_acKernel n).continuous hf.locallyIntegrable).aestronglyMeasurable
  · exact integrable_const C
  · intro n; exact Eventually.of_forall (norm_acKernel_convolution_le hf hC0 hC n)
  · exact Eventually.of_forall (tendsto_acKernel_convolution hf)

/--
A uniform Lᑫ bound for the regularizations gives absolute continuity (p finite, p and q conjugate).
-/
theorem absolutelyContinuous_of_eLpNorm_measureMollify_le
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] (hp : 1 ≤ p) (hpfin : p ≠ ⊤)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hb : ∀ n, eLpNorm (measureMollify ν n) q ≤ M) :
    ν ≪ volume := by
  letI : IsLocallyFiniteMeasure (ν + volume) := ⟨fun x => by
    obtain ⟨s,hs,hvol⟩ := (volume : Measure E).finiteAt_nhds x
    exact ⟨s, hs, by simpa only [Measure.add_apply] using
      ENNReal.add_lt_top.mpr ⟨measure_lt_top ν s, hvol⟩⟩⟩
  apply absolutelyContinuous_of_integral_le_eLpNorm (ν := ν) (μ := volume) (p := p) (M := M) hp hpfin hM
  intro f hf hfk
  have ht := (tendsto_integral_mul_measureMollify ν hf hfk).enorm
  apply le_of_tendsto' ht
  intro n
  have hInt : ‖∫ x, f x * measureMollify ν n x‖ₑ ≤
      eLpNorm (fun x => f x * measureMollify ν n x) 1 volume := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact enorm_integral_le_lintegral_enorm (μ := (volume : Measure E)) _
  have hHolder : eLpNorm (fun x => f x * measureMollify ν n x) 1 volume ≤
      eLpNorm f p volume * eLpNorm (measureMollify ν n) q volume := by
    simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def] using eLpNorm_smul_le_mul_eLpNorm
      (μ := (volume : Measure E)) (p := p) (q := q) (r := 1)
      (f := measureMollify ν n) (φ := f) (contDiff_measureMollify ν n).continuous.aestronglyMeasurable
      hf.aestronglyMeasurable
  have hlast : eLpNorm f p volume * eLpNorm (measureMollify ν n) q volume ≤ M * eLpNorm f p volume :=
    (mul_le_mul_right (hb n) (eLpNorm f p volume)).trans_eq (mul_comm _ _)
  exact hInt.trans (hHolder.trans hlast)

end Foundations
