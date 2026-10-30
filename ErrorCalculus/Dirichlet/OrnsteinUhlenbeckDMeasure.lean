import ErrorCalculus.Dirichlet.OrnsteinUhlenbeckD

noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace ErrorCalculus

/-- equality with Mathlib's finite product of standard Gaussian measures. -/
theorem ouDensityD_measure (d : ℕ) :
    densityMeasureD (ouDensityD d) = Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [densityMeasureD, withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_ouDensityD d).restrict
      (Eventually.of_forall fun x => (SmoothDensityD.pos (ρ := ouDensityD d) x).le)]
  have hi : (∫ x in Set.univ.pi s, ouDensityD d x) =
      ∏ i, ∫ x in s i, gaussianPDFReal 0 1 x := by
    change (∫ x, ouDensityD d x ∂(Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict (Set.univ.pi s)) = _
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod (fun _ : Fin d => gaussianPDFReal 0 1)
  rw [hi, ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply_eq_integral 0 (by norm_num) (s i)).symm

end ErrorCalculus
