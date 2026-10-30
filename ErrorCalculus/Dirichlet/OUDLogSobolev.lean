import ErrorCalculus.Dirichlet.OUDMollify

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus
variable {d : ℕ}

/-- The first partials converge in Gaussian L², by commutation and dominated convergence. -/
theorem tendsto_partialD_mollifyD_L2_gaussian {f : (Fin d → ℝ) → ℝ}
    (hf : ErrorCalculus.IsC1BoundedD f) (i : Fin d) :
    Tendsto (fun n => ((isC2BoundedD_mollifyD hf n).1.memLp_partial i 2).toLp
      (Foundations.partialD (Foundations.mollifyD f n) i)) atTop
        (𝓝 (((foundations_isC1BoundedD hf).memLp_partial i 2).toLp
          (Foundations.partialD f i))) := by
  simpa only [partialD_mollifyD hf] using
    (tendsto_mollifyD_L2 (μ := Foundations.gaussianPi d)
      ((foundations_isC1BoundedD hf).continuous_partial i)
      ((foundations_isC1BoundedD hf).partial_bounded i))

/-- The diagonal energies converge, with no bound on second derivatives uniform in n. -/
theorem tendsto_energy_mollifyD {f : (Fin d → ℝ) → ℝ}
    (hf : ErrorCalculus.IsC1BoundedD f) :
    Tendsto (fun n => (ouStructureD d).energy.E
      (ouDOfFunction (Foundations.mollifyD f n)
        (isC1BoundedD_of_foundations (isC2BoundedD_mollifyD hf n).1))
      (ouDOfFunction (Foundations.mollifyD f n)
        (isC1BoundedD_of_foundations (isC2BoundedD_mollifyD hf n).1))) atTop
      (𝓝 ((ouStructureD d).energy.E (ouDOfFunction f hf) (ouDOfFunction f hf))) := by
  have ht (i : Fin d) := (tendsto_partialD_mollifyD_L2_gaussian hf i).norm.pow 2
  simp only [Foundations.norm_toLp_sq] at ht
  simp_rw [ouDOfFunction_energy, ouDensityD_eq_gaussianPi, Foundations.gradNormSqD,
    integral_finsetSum _ (fun i _ =>
      ((isC2BoundedD_mollifyD hf _).1.memLp_partial i 2).integrable_sq),
    integral_finsetSum _ (fun i _ =>
      ((foundations_isC1BoundedD hf).memLp_partial i 2).integrable_sq)]
  exact (tendsto_finsetSum _ (fun i _ => ht i)).const_mul (1/2 : ℝ)

/-- inclusion preserves the proto-energy. -/
theorem ouD_inclusion_energy (u : protoDomD (ouDensityD d)) :
    (ouStructureD d).energy.E ((protoFormD (ouDensityD d)).inclusion u)
      ((protoFormD (ouDensityD d)).inclusion u) = (protoFormD (ouDensityD d)).E u u := by
  change (1/2 : ℝ) * (∫ x, (densityStructureD (ouDensityD d)).Γ _ _ x ∂_) = _
  rw [densityStructure_Γ_extendsD]
  rfl

/-- The C² inequality passes to every C¹_b representative in the proto-domain. -/
theorem ouProtoD_logSobolev (u : protoDomD (ouDensityD d)) :
    Integrable (fun x => ((u : Lp ℝ 2 (densityMeasureD (ouDensityD d))) x)^2 *
      Real.log (((u : Lp ℝ 2 (densityMeasureD (ouDensityD d))) x)^2))
        (densityMeasureD (ouDensityD d)) ∧
    entropy (densityMeasureD (ouDensityD d))
      (fun x => ((u : Lp ℝ 2 (densityMeasureD (ouDensityD d))) x)^2) ≤
        4 * (densityProtoD (ouDensityD d)).energy.E u u := by
  let f := repD (ouDensityD d) u
  have hf : ErrorCalculus.IsC1BoundedD f := rep_isC1BoundedD _ u
  have hu : protoOfFunctionD (ouDensityD d) f hf = u := by
    apply Subtype.ext
    apply Lp.ext
    exact (hf.memLp _ 2).coeFn_toLp.trans (coeFn_repD _ u).symm
  have he : (ouStructureD d).energy.E (ouDOfFunction f hf) (ouDOfFunction f hf) =
      (densityProtoD (ouDensityD d)).energy.E u u := by
    unfold ouDOfFunction
    rw [hu, ouD_inclusion_energy]
    rfl
  have hv : (ouDOfFunction f hf : Lp ℝ 2 (densityMeasureD (ouDensityD d))) = u :=
    congrArg Subtype.val hu
  have ht := tendsto_mollifyD_L2_gaussian hf
  rw [hv] at ht
  apply entropy_le_of_tendsto_L2 ht
    (fun n => (ouStructureD_logSobolev_C2b (isC2BoundedD_mollifyD hf n)).1)
    (fun n => (ouStructureD_logSobolev_C2b (isC2BoundedD_mollifyD hf n)).2)
  rw [← he]
  exact (tendsto_energy_mollifyD hf).const_mul 4

/-- Gross's inequality on the entire closed finite-dimensional OU form domain. -/
theorem ouStructureD_hasLogSobolev (d : ℕ) : (ouStructureD d).HasLogSobolev 4 :=
  (densityProtoD (ouDensityD d)).closure_hasLogSobolev
    (protoFormD_isClosable (ouDensityD d)) ouProtoD_logSobolev

end ErrorCalculus
