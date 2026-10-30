import ErrorCalculus.Dirichlet.DensityDStructure
import ErrorCalculus.Dirichlet.DensityGaussian
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace ErrorCalculus

/-- The product of the normalized one-dimensional Gaussian densities. -/
def ouDensityD (d : ℕ) (x : Fin d → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

instance ouDensityD_smooth (d : ℕ) : SmoothDensityD (ouDensityD d) where
  contDiff := by
    unfold ouDensityD gaussianPDFReal
    fun_prop
  pos x := Finset.prod_pos (fun i _ => gaussianPDFReal_pos 0 1 (x i) (by norm_num))

theorem integrable_ouDensityD (d : ℕ) : Integrable (ouDensityD d) :=
  Integrable.fintype_prod (fun _ : Fin d => integrable_gaussianPDFReal 0 1)

/-- The normalization follows from the finite-product integral theorem. -/
theorem integral_ouDensityD (d : ℕ) : (∫ x, ouDensityD d x) = 1 := by
  calc
    _ = ∏ _i : Fin d, ∫ x : ℝ, gaussianPDFReal 0 1 x :=
      integral_fintype_prod_eq_prod (fun _ : Fin d => gaussianPDFReal 0 1)
    _ = 1 := by
      have h : (∫ x : ℝ, gaussianPDFReal 0 1 x) = 1 :=
        integral_gaussianPDFReal_eq_one 0 (by norm_num)
      simp only [h, Finset.prod_const_one]

instance ouDensityD_probability (d : ℕ) : IsProbabilityMeasure (densityMeasureD (ouDensityD d)) where
  measure_univ := by
    rw [densityMeasureD, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_ouDensityD d)
        (Eventually.of_forall fun x => (SmoothDensityD.pos (ρ := ouDensityD d) x).le),
      integral_ouDensityD, ENNReal.ofReal_one]

/-- (b): the Ornstein--Uhlenbeck error structure in every finite dimension. -/
def ouStructureD (d : ℕ) : ErrorStructure (Fin d → ℝ) (densityMeasureD (ouDensityD d)) :=
  densityStructureD (ouDensityD d)

@[simp] theorem ouStructureD_energy (d : ℕ) :
    (ouStructureD d).energy = dirichletFormD (ouDensityD d) :=
  densityStructure_energyD (ouDensityD d)

/-- On C¹_b the closed Gaussian carré du champ is the sum of squared partial derivatives. -/
theorem ouStructureD_Γ_ofFunction {d : ℕ} (g : (Fin d → ℝ) → ℝ) (hg : IsC1BoundedD g) :
    ⇑((ouStructureD d).Γ ((protoFormD (ouDensityD d)).inclusion (protoOfFunctionD (ouDensityD d) g hg))
      ((protoFormD (ouDensityD d)).inclusion (protoOfFunctionD (ouDensityD d) g hg)))
      =ᵐ[densityMeasureD (ouDensityD d)] fun x => ∑ i, (fderiv ℝ g x (Pi.single i 1))^2 :=
  densityStructureD_Γ_ofFunction (ouDensityD d) g hg

end ErrorCalculus
