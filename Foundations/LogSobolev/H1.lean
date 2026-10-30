import Foundations.LogSobolev.EntropyLimit

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ContDiff
namespace Foundations

theorem densityMeasure_gaussian_eq : densityMeasure (gaussianPDFReal 0 1) = standardGaussian := by
  rw [standardGaussian,gaussianReal_of_var_ne_zero _ (one_ne_zero : (1 : NNReal) ≠ 0)]
  rfl

theorem continuous_standardGaussian_density : Continuous (gaussianPDFReal 0 1) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_gaussianDensity x).continuousAt)

theorem isC1Bounded_of_compactSupport {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : IsC1Bounded f :=
  ⟨hf,(C1c_bounded hf hc).1,(C1c_bounded hf hc).2.2⟩

theorem isC2Bounded_of_smooth_compactSupport {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : IsC2Bounded f :=
  ⟨isC1Bounded_of_compactSupport (hf.of_le (by simp)) hc,
    isC1Bounded_of_compactSupport ((contDiff_infty_iff_deriv.mp hf).2.of_le (by simp)) hc.deriv⟩

/--
Mollification extends the Gaussian logarithmic Sobolev inequality to compactly supported C¹
functions.
-/
theorem logSobolev_gaussian_C1c {f : ℝ → ℝ} (hC : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    Integrable (fun x => (f x)^2*Real.log ((f x)^2)) standardGaussian ∧
      entropy standardGaussian (fun x => (f x)^2) ≤ 2*∫ x, (deriv f x)^2 ∂standardGaussian := by
  have hf := isC1Bounded_of_compactSupport hC hc
  have hfρ : MemLp f 2 (densityMeasure (gaussianPDFReal 0 1)) := by
    rw [densityMeasure_gaussian_eq]; exact hf.memLp 2
  have hdfρ : MemLp (deriv f) 2 (densityMeasure (gaussianPDFReal 0 1)) := by
    rw [densityMeasure_gaussian_eq]; exact hf.memLp_deriv 2
  obtain ⟨w,hw,hdw,he,hCw,hsw,ht,hdt⟩ := exists_mollification_tendsto
    continuous_standardGaussian_density (fun x => gaussianPDFReal_pos 0 1 x one_ne_zero)
    (fun a b => hC.contDiffOn.absolutelyContinuousOnInterval) hc hfρ hdfρ
  have hh := logSobolev_of_L2_limit densityMeasure_gaussian_eq hw hdw hfρ hdfρ ht hdt
    (fun n => by
      rw [densityMeasure_gaussian_eq]
      have h := (isC2Bounded_of_smooth_compactSupport (hCw n) (hsw n)).1
      simpa only [pow_two] using integrable_mul_log_of_bounded (h.mul h).contDiff.continuous (h.mul h).bounded)
    (fun n => by
      rw [densityMeasure_gaussian_eq]
      exact logSobolev_gaussian_C2 (isC2Bounded_of_smooth_compactSupport (hCw n) (hsw n)))
  simpa only [densityMeasure_gaussian_eq] using hh

/-- Gross's inequality on the closed Sobolev graph, with an explicit derivative class. -/
theorem logSobolev_gaussian_of_mem_closure
    {U G : Lp ℝ 2 (densityMeasure (gaussianPDFReal 0 1))}
    (h : (U,G) ∈ closure (C1cGraph (gaussianPDFReal 0 1))) :
    Integrable (fun x => (U x)^2*Real.log ((U x)^2)) (densityMeasure (gaussianPDFReal 0 1)) ∧
      entropy (densityMeasure (gaussianPDFReal 0 1)) (fun x => (U x)^2) ≤
        2*∫ x, (G x)^2 ∂densityMeasure (gaussianPDFReal 0 1) := by
  obtain ⟨f,hf,hdf,hC,hc,ht,hdt⟩ := exists_C1c_seq_of_mem_closure h
  apply logSobolev_of_L2_limit densityMeasure_gaussian_eq hf hdf (Lp.memLp U) (Lp.memLp G)
    (by simpa only [Lp.toLp_coeFn] using ht) (by simpa only [Lp.toLp_coeFn] using hdt)
  · intro n; rw [densityMeasure_gaussian_eq]; exact (logSobolev_gaussian_C1c (hC n) (hc n)).1
  · intro n; rw [densityMeasure_gaussian_eq]; exact (logSobolev_gaussian_C1c (hC n) (hc n)).2

/-- The H¹ form of Gross's inequality. The witness G is the weak derivative in the closed
C¹ compact-support graph. In particular the entropy integrand is integrable. -/
theorem logSobolev_gaussian {U : Lp ℝ 2 (densityMeasure (gaussianPDFReal 0 1))}
    (hU : MemH1Density (gaussianPDFReal 0 1) U) :
    ∃ G : Lp ℝ 2 (densityMeasure (gaussianPDFReal 0 1)),
      (U,G) ∈ closure (C1cGraph (gaussianPDFReal 0 1)) ∧
      Integrable (fun x => (U x)^2*Real.log ((U x)^2)) (densityMeasure (gaussianPDFReal 0 1)) ∧
      entropy (densityMeasure (gaussianPDFReal 0 1)) (fun x => (U x)^2) ≤
        2*∫ x, (G x)^2 ∂densityMeasure (gaussianPDFReal 0 1) := by
  obtain ⟨G,hG⟩ := hU
  exact ⟨G,hG,logSobolev_gaussian_of_mem_closure hG⟩

end Foundations
