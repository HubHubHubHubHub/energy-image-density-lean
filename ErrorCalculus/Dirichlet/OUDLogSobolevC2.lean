import ErrorCalculus.Dirichlet.LogSobolev
import ErrorCalculus.Dirichlet.OUDIBP
import Foundations.LogSobolevD.Gross

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus
variable {d : ℕ}

/-- The two bounded C¹ conventions agree in finite dimension. -/
theorem isC1BoundedD_of_foundations {g : (Fin d → ℝ) → ℝ}
    (hg : Foundations.IsC1BoundedD g) : ErrorCalculus.IsC1BoundedD g := by
  obtain ⟨C, _, hC⟩ := hg.fderiv_bounded
  exact ⟨hg.contDiff, hg.bounded, C, hC⟩

theorem foundations_isC1BoundedD {g : (Fin d → ℝ) → ℝ}
    (hg : ErrorCalculus.IsC1BoundedD g) : Foundations.IsC1BoundedD g := by
  refine ⟨hg.1, hg.2.1, fun i => ?_⟩
  obtain ⟨C, hC⟩ := hg.2.2
  refine ⟨C, fun x => ?_⟩
  apply le_trans _ (hC x)
  simpa only [Foundations.partialD, Pi.norm_single, norm_one, mul_one] using
    (ContinuousLinearMap.le_opNorm (fderiv ℝ g x) (Pi.single i 1))

/-- A bounded C¹ function as an element of the closed OU domain. -/
def ouDOfFunction (g : (Fin d → ℝ) → ℝ) (hg : ErrorCalculus.IsC1BoundedD g) :
    (ouStructureD d).dom :=
  (protoFormD (ouDensityD d)).inclusion (protoOfFunctionD (ouDensityD d) g hg)

theorem coe_ouDOfFunction (g : (Fin d → ℝ) → ℝ) (hg : ErrorCalculus.IsC1BoundedD g) :
    (ouDOfFunction g hg : Lp ℝ 2 (densityMeasureD (ouDensityD d))) =ᵐ[densityMeasureD (ouDensityD d)] g :=
  (hg.memLp _ 2).coeFn_toLp

theorem ouDOfFunction_Γ (g : (Fin d → ℝ) → ℝ) (hg : ErrorCalculus.IsC1BoundedD g) :
    (ouStructureD d).Γ (ouDOfFunction g hg) (ouDOfFunction g hg) =ᵐ[densityMeasureD (ouDensityD d)]
      Foundations.gradNormSqD g :=
  densityStructureD_Γ_ofFunction (ouDensityD d) g hg

theorem ouDOfFunction_energy (g : (Fin d → ℝ) → ℝ) (hg : ErrorCalculus.IsC1BoundedD g) :
    (ouStructureD d).energy.E (ouDOfFunction g hg) (ouDOfFunction g hg) =
      (1 / 2 : ℝ) * ∫ x, Foundations.gradNormSqD g x ∂densityMeasureD (ouDensityD d) := by
  change (1 / 2 : ℝ) * (∫ x, (ouStructureD d).Γ _ _ x ∂_) = _
  rw [integral_congr_ae (ouDOfFunction_Γ g hg)]

/-- Gross on C²_b, with integrability and the normalization E = ½∫Γ. -/
theorem ouStructureD_logSobolev_C2b {g : (Fin d → ℝ) → ℝ}
    (hg : Foundations.IsC2BoundedD g) :
    let u := ouDOfFunction g (isC1BoundedD_of_foundations hg.1)
    Integrable (fun x => ((u : Lp ℝ 2 (densityMeasureD (ouDensityD d))) x)^2 *
      Real.log (((u : Lp ℝ 2 (densityMeasureD (ouDensityD d))) x)^2))
        (densityMeasureD (ouDensityD d)) ∧
    entropy (densityMeasureD (ouDensityD d))
      (fun x => ((u : Lp ℝ 2 (densityMeasureD (ouDensityD d))) x)^2) ≤
        4 * (ouStructureD d).energy.E u u := by
  dsimp only
  have ha := coe_ouDOfFunction g (isC1BoundedD_of_foundations hg.1)
  have hi : Integrable (fun x => (g x)^2 * Real.log ((g x)^2))
      (densityMeasureD (ouDensityD d)) := by
    rw [ouDensityD_eq_gaussianPi]
    simpa only [pow_two] using Foundations.integrable_mul_log_of_boundedD
      (hg.1.mul hg.1).contDiff.continuous (hg.1.mul hg.1).bounded
  refine ⟨hi.congr (ha.fun_comp (fun z => z^2 * Real.log (z^2))).symm, ?_⟩
  have hsq := ha.fun_comp (fun z => z^2)
  simp only [Function.comp_def] at hsq
  rw [entropy_congr_ae hsq, ouDOfFunction_energy,
    ouDensityD_eq_gaussianPi]
  have hb := Foundations.logSobolev_gaussianD_C2 hg
  change entropy _ _ ≤ _ at hb
  convert hb using 1; ring

end ErrorCalculus
