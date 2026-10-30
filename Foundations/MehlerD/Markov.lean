import Foundations.MehlerD.Spectral

noncomputable section
open Filter Topology Set MeasureTheory Polynomial
namespace Foundations
variable {ι : Type*} [Fintype ι]

theorem mehlerD_nonneg {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (gaussianProduct ι))
    (hf : ∀ᵐ x ∂(gaussianProduct ι), 0 ≤ f x) :
    ∀ᵐ x ∂(gaussianProduct ι), 0 ≤ mehlerD t f x := by
  have h := (measurePreserving_mehlerMixD ht).quasiMeasurePreserving.ae hf
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae h
  filter_upwards [coe_mehlerD ht f, Measure.ae_ae_of_ae_prod hs] with x hx hy
  rw [hx]
  exact integral_nonneg_of_ae hy

theorem mehlerD_markov {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (gaussianProduct ι))
    (hf : ∀ᵐ x ∂(gaussianProduct ι), 0 ≤ f x ∧ f x ≤ 1) :
    ∀ᵐ x ∂(gaussianProduct ι), 0 ≤ mehlerD t f x ∧ mehlerD t f x ≤ 1 := by
  have h := (measurePreserving_mehlerMixD ht).quasiMeasurePreserving.ae hf
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae h
  have hm := (Lp.memLp f).comp_measurePreserving (measurePreserving_mehlerMixD ht)
  filter_upwards [coe_mehlerD ht f, Measure.ae_ae_of_ae_prod hs,
    memLp_section_ae (gaussianProduct ι) hm] with x hx hy hz
  rw [hx]
  refine ⟨integral_nonneg_of_ae (hy.mono fun _ h => h.1), ?_⟩
  have hi := integral_mono_ae (hz.integrable (by norm_num)) (integrable_const (1:ℝ))
    (hy.mono fun _ h => h.2)
  change (∫ y, f (fun i => mehlerCoeffA t*x i+mehlerCoeffB t*y i) ∂gaussianProduct ι) ≤
    ∫ _ : ι → ℝ, (1 : ℝ) ∂gaussianProduct ι at hi
  simpa only [mehlerKernelD,integral_const,probReal_univ,one_smul] using hi

theorem mehlerD_one {t : ℝ} (ht : 0 ≤ t) :
    mehlerD t (hermiteLpD (0 : ι → ℕ)) = hermiteLpD 0 := by
  simpa [hermiteDegreeD] using mehlerD_hermite ht (0 : ι → ℕ)

end Foundations
