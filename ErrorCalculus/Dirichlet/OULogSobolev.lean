import ErrorCalculus.Dirichlet.LogSobolev
import ErrorCalculus.Dirichlet.OUDomain

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace ErrorCalculus

/-- Gaussian LSI on the entire closed OU domain, via its AC representative. -/
theorem ouStructure_hasLogSobolev : ouStructure.HasLogSobolev 4 := by
  intro u
  obtain ⟨g, hug, hac, hd⟩ := (mem_ouStructure_dom_iff u).mp u.property
  have hg : MemLp g 2 Foundations.standardGaussian := (memLp_congr_ae hug).mp (Lp.memLp (u : Lp ℝ 2 (gaussianReal 0 1)))
  obtain ⟨hi, hb⟩ := Foundations.logSobolev_gaussian_AC hg hd hac
  have hsq := hug.fun_comp (fun z => z^2)
  have hlog := hug.fun_comp (fun z => z^2 * Real.log (z^2))
  simp only [Function.comp_def] at hsq hlog
  refine ⟨hi.congr hlog.symm, ?_⟩
  rw [entropy_congr_ae hsq, entropy_eq_foundations]
  have he : (4 : ℝ) * ouStructure.energy.E u u =
      2 * ∫ x, (deriv g x)^2 ∂Foundations.standardGaussian := by
    change 4 * ((1/2:ℝ) * ∫ x, ouStructure.Γ u u x ∂gaussianReal 0 1) = _
    rw [integral_congr_ae (ouStructure_Γ_representative u hug hac hd)]
    ring
  rw [he]
  exact hb

/-- Unfolded version, recording integrability as well as the entropy bound. -/
theorem ouStructure_logSobolev (u : ouStructure.dom) :
    Integrable (fun x => ((u : Lp ℝ 2 (gaussianReal 0 1)) x)^2 *
      Real.log (((u : Lp ℝ 2 (gaussianReal 0 1)) x)^2)) (gaussianReal 0 1) ∧
    entropy (gaussianReal 0 1) (fun x => ((u : Lp ℝ 2 (gaussianReal 0 1)) x)^2) ≤
      4 * ouStructure.energy.E u u := ouStructure_hasLogSobolev u

/-- The bounded C¹ representative version, with the same Gaussian normalization. -/
theorem ouStructure_logSobolev_C1 {g : ℝ → ℝ} (hg : Foundations.IsC1Bounded g) :
    Integrable (fun x => (g x)^2 * Real.log ((g x)^2)) (gaussianReal 0 1) ∧
      entropy (gaussianReal 0 1) (fun x => (g x)^2) ≤
        2 * ∫ x, (deriv g x)^2 ∂gaussianReal 0 1 :=
  Foundations.logSobolev_gaussian_C1 hg

end ErrorCalculus
