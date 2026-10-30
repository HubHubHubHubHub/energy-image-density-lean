import Foundations.Mehler.Spectral

noncomputable section
open Filter Topology Set MeasureTheory Polynomial
namespace Foundations

theorem mehler_nonneg {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 standardGaussian)
    (hf : ∀ᵐ x ∂standardGaussian, 0 ≤ f x) :
    ∀ᵐ x ∂standardGaussian, 0 ≤ mehler t f x := by
  have h := (measurePreserving_mehlerMix ht).quasiMeasurePreserving.ae hf
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae h
  filter_upwards [coe_mehler ht f, Measure.ae_ae_of_ae_prod hs] with x hx hy
  rw [hx]
  exact integral_nonneg_of_ae hy

theorem mehler_markov {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 standardGaussian)
    (hf : ∀ᵐ x ∂standardGaussian, 0 ≤ f x ∧ f x ≤ 1) :
    ∀ᵐ x ∂standardGaussian, 0 ≤ mehler t f x ∧ mehler t f x ≤ 1 := by
  have h := (measurePreserving_mehlerMix ht).quasiMeasurePreserving.ae hf
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae h
  have hm := (Lp.memLp f).comp_measurePreserving (measurePreserving_mehlerMix ht)
  filter_upwards [coe_mehler ht f, Measure.ae_ae_of_ae_prod hs,
    memLp_section_ae standardGaussian hm] with x hx hy hz
  rw [hx]
  refine ⟨integral_nonneg_of_ae (hy.mono fun _ h => h.1), ?_⟩
  have hi := integral_mono_ae (hz.integrable (by norm_num)) (integrable_const (1:ℝ))
    (hy.mono fun _ h => h.2)
  simpa only [mehlerKernel, mehlerMix, Function.comp_def, integral_const, probReal_univ, one_smul] using hi

theorem mehler_one {t : ℝ} (ht : 0 ≤ t) :
    mehler t (polynomialLp 1) = polynomialLp 1 := by
  simpa [hermiteLp] using mehler_hermite ht 0

theorem integral_mehler {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 standardGaussian) :
    (∫ x, mehler t f x ∂standardGaussian) = ∫ x, f x ∂standardGaussian := by
  have h := mehler_inner_hermite ht 0 f
  simpa [hermiteNormalized, ← gaussianMean_apply, gaussianMean] using h

end Foundations
