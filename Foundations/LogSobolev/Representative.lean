import Foundations.LogSobolev.H1

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations

theorem entropy_congr_ae {μ : Measure ℝ} {f g : ℝ → ℝ} (h : f =ᵐ[μ] g) :
    entropy μ f = entropy μ g := by
  unfold entropy
  have he := integral_congr_ae (h.fun_comp (fun z => z*Real.log z))
  simp only [Function.comp_def] at he
  rw [integral_congr_ae h,he]

/-- The representative formulation: no boundedness or global smoothness is assumed. -/
theorem logSobolev_gaussian_AC {u : ℝ → ℝ}
    (hu : MemLp u 2 standardGaussian) (hd : MemLp (deriv u) 2 standardGaussian)
    (hac : ∀ a b, AbsolutelyContinuousOnInterval u a b) :
    Integrable (fun x => (u x)^2*Real.log ((u x)^2)) standardGaussian ∧
      entropy standardGaussian (fun x => (u x)^2) ≤
        2*∫ x, (deriv u x)^2 ∂standardGaussian := by
  have huρ : MemLp u 2 (densityMeasure (gaussianPDFReal 0 1)) := by rwa [densityMeasure_gaussian_eq]
  have hdρ : MemLp (deriv u) 2 (densityMeasure (gaussianPDFReal 0 1)) := by rwa [densityMeasure_gaussian_eq]
  have he := eq_primitiveRepresentative_of_locallyAC hac
  have hup : MemLp (primitiveRepresentative (u 0) (deriv u)) 2 (densityMeasure (gaussianPDFReal 0 1)) := by
    rwa [← he]
  have hc := primitive_mem_closure_C1cGraph continuous_standardGaussian_density
    (fun x => gaussianPDFReal_pos 0 1 x one_ne_zero) (u 0) hup hdρ
  have hh := logSobolev_gaussian_of_mem_closure hc
  have hurep : (hup.toLp (primitiveRepresentative (u 0) (deriv u)) : ℝ → ℝ) =ᵐ[densityMeasure (gaussianPDFReal 0 1)] u := by
    simpa only [← he] using hup.coeFn_toLp
  have hdrep := hdρ.coeFn_toLp
  have hint := hh.1.congr (hurep.fun_comp (fun z => z^2*Real.log (z^2)))
  have heq := entropy_congr_ae (hurep.fun_comp (fun z => z^2))
  have heq' := integral_congr_ae (hdrep.fun_comp (fun z => z^2))
  simp only [Function.comp_def] at hint heq heq'
  rw [heq,heq'] at hh
  have hbound := hh.2
  rw [densityMeasure_gaussian_eq] at hint hbound
  exact ⟨hint,hbound⟩

/-- In particular, the original C¹_b formulation follows from the H¹ extension. -/
theorem logSobolev_gaussian_C1 {g : ℝ → ℝ} (hg : IsC1Bounded g) :
    Integrable (fun x => (g x)^2*Real.log ((g x)^2)) standardGaussian ∧
      entropy standardGaussian (fun x => (g x)^2) ≤
        2*∫ x, (deriv g x)^2 ∂standardGaussian :=
  logSobolev_gaussian_AC (hg.memLp 2) (hg.memLp_deriv 2)
    (fun _ _ => hg.contDiff.contDiffOn.absolutelyContinuousOnInterval)

end Foundations
