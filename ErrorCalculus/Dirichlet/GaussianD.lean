import ErrorCalculus.Dirichlet.OrnsteinUhlenbeckD
import Mathlib.Probability.Independence.Integration

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus

/-- The explicit density used by OU is the product Gaussian measure. -/
theorem ouDensityD_measure (d : ℕ) :
    densityMeasureD (ouDensityD d) = Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [densityMeasureD, withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_ouDensityD d).restrict
      (ae_of_all _ fun x => (SmoothDensityD.pos (ρ := ouDensityD d) x).le)]
  change ENNReal.ofReal (∫ x in Set.univ.pi s, ∏ i, gaussianPDFReal 0 1 (x i)
    ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg fun x => gaussianPDFReal_nonneg _ _ _)]
  apply Finset.prod_congr rfl
  intro i _
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).restrict
    (ae_of_all _ fun x => gaussianPDFReal_nonneg _ _ _)

variable {d : ℕ}

/-- Every coordinate belongs to L² of the explicit Gaussian density. -/
theorem ou_memLp_coordinateD (i : Fin d) :
    MemLp (fun x : Fin d → ℝ => x i) 2 (densityMeasureD (ouDensityD d)) := by
  rw [ouDensityD_measure]
  exact (memLp_id_gaussianReal' 2 (by norm_num)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i)

def ouCoordinateLpD (i : Fin d) : Lp ℝ 2 (densityMeasureD (ouDensityD d)) :=
  (ou_memLp_coordinateD i).toLp _

theorem coeFn_ouCoordinateLpD (i : Fin d) :
    ouCoordinateLpD i =ᵐ[densityMeasureD (ouDensityD d)] fun x => x i :=
  (ou_memLp_coordinateD i).coeFn_toLp

theorem integral_ou_coordinateD (i : Fin d) :
    (∫ x, x i ∂densityMeasureD (ouDensityD d)) = 0 := by
  rw [ouDensityD_measure, integral_eval, integral_id_gaussianReal]

theorem integral_ou_coordinate_sqD (i : Fin d) :
    (∫ x, (x i)^2 ∂densityMeasureD (ouDensityD d)) = 1 := by
  rw [ouDensityD_measure]
  have he := integral_comp_eval (μ := fun _ : Fin d => gaussianReal 0 1)
    (i := i) (f := fun x : ℝ => x^2) (by fun_prop)
  rw [he]
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] using h

/-- Orthonormality of the Gaussian coordinate system, including the mixed moments. -/
theorem integral_ou_coordinate_mulD (i j : Fin d) :
    (∫ x, x i * x j ∂densityMeasureD (ouDensityD d)) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa only [ite_true, ← pow_two] using integral_ou_coordinate_sqD i
  · rw [if_neg hij, ouDensityD_measure]
    have h := (iIndepFun_pi (μ := fun _ : Fin d => gaussianReal 0 1)
      (X := fun _ => id) (fun _ => measurable_id.aemeasurable)).indepFun hij
    simpa only [id_eq, integral_eval, integral_id_gaussianReal, mul_zero] using
      h.integral_fun_mul_eq_mul_integral
        (measurable_pi_apply i).aestronglyMeasurable
        (measurable_pi_apply j).aestronglyMeasurable

theorem inner_ouCoordinateLpD (i j : Fin d) :
    inner ℝ (ouCoordinateLpD i) (ouCoordinateLpD j) = if i = j then 1 else 0 := by
  rw [L2.inner_def]
  convert integral_ou_coordinate_mulD i j using 1
  apply integral_congr_ae
  filter_upwards [coeFn_ouCoordinateLpD i, coeFn_ouCoordinateLpD j] with x hi hj
  rw [hi, hj, real_inner_comm]
  rfl

/-- The one-dimensional Gaussian logarithmic derivative, proved directly. -/
theorem hasDerivAt_ouDensity (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  convert! ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹) using 1
  dsimp
  ring

/-- The partial derivative of the finite-dimensional Gaussian density. -/
theorem partial_ouDensityD (i : Fin d) (x : Fin d → ℝ) :
    fderiv ℝ (ouDensityD d) x (Pi.single i 1) = -x i * ouDensityD d x := by
  have hf (j : Fin d) : HasFDerivAt (fun y : Fin d → ℝ => gaussianPDFReal 0 1 (y j))
      ((-x j * gaussianPDFReal 0 1 (x j)) • (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ)) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (hasDerivAt_ouDensity (x j)).comp_hasFDerivAt x
        (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ).hasFDerivAt
  have h := (HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ => hf j)).fderiv
  change fderiv ℝ (fun y => ∏ j, gaussianPDFReal 0 1 (y j)) x (Pi.single i 1) = _
  rw [h]
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, mul_one, ouDensityD]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    ring
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

end ErrorCalculus
