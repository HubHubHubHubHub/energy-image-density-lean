import GeometricMeasure.Current.WeakConvergence
import GeometricMeasure.Current.Mass

/-! Covector mass for independent domain and target dimensions. -/
noncomputable section
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal Topology

namespace GeometricMeasure
variable {d : ℕ} {m : ℕ}

def measureCovectorFunctional
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m))) :
    TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d)))
      (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (⊤ : ℕ∞) →L[ℝ] ℝ :=
  TestFunction.integralAgainstBilinCLM
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ))
    M.variation (polarDensity M)

theorem measureCovectorFunctional_eq_measureOneCurrent
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d))) :
    measureCovectorFunctional M = measureOneCurrent M := rfl

theorem measureCovectorFunctional_apply
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ω : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d)))
      (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (⊤ : ℕ∞)) :
    measureCovectorFunctional M ω = ∫ x, ω x (polarDensity M x) ∂M.variation :=
  TestFunction.integralAgainstBilinCLM_eq_integral
    ((integrable_polarDensity M).locallyIntegrable.locallyIntegrableOn _)

theorem measureCovectorFunctional_mass_le
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (U : Set (EuclideanSpace ℝ (Fin d))) :
    testFunctionalMassOn (measureCovectorFunctional M) U ≤ M.variation U := by
  apply testFunctionalMassOn_le
  intro ω hs hn
  have hbound : |measureCovectorFunctional M ω| ≤ ∫ x, ‖ω x‖ ∂M.variation := by
    rw [measureCovectorFunctional_apply, ← Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_ae (integrable_vectorMeasurePairing M
      (ω : BoundedCovectorField d m)).norm
      (ω.integrable (locallyIntegrableOn_const (1 : ℝ))).norm
    filter_upwards [norm_polarDensity_ae M] with x hx
    simpa [hx] using (ω x).le_opNorm (polarDensity M x)
  exact (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hbound)).trans
    (ofReal_integral_norm_currentTest_le M.variation ω hs hn)

theorem measureCovectorFunctional_mass_eq_variation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    testFunctionalMassOn (measureCovectorFunctional M) U = M.variation U := by
  apply testFunctionalMassOn_eq_of_paired_density M.variation (measureCovectorFunctional M)
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ))
    (fun v w => v.le_opNorm w) (integrable_polarDensity M) (norm_polarDensity_ae M)
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).integrable_comp_iff.mpr
      (integrable_polarDensity M))
    (q := fun x => InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m)) (polarDensity M x))
    _ _ (measureCovectorFunctional_apply M) hU (measureCovectorFunctional_mass_le M U)
  · filter_upwards [norm_polarDensity_ae M] with x hx
    simp [hx]
  · filter_upwards [norm_polarDensity_ae M] with x hx
    simp [InnerProductSpace.toDual_apply_apply, hx]

theorem variation_le_liminf_of_covectorTest_tendsto
    (Ms : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (hconv : ∀ ω, Tendsto (fun n => measureCovectorFunctional (Ms n) ω)
      atTop (𝓝 (measureCovectorFunctional M ω)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    M.variation U ≤ Filter.liminf (fun n => (Ms n).variation U) atTop := by
  simpa only [measureCovectorFunctional_mass_eq_variation _ hU] using
    testFunctionalMassOn_le_liminf (fun n => measureCovectorFunctional (Ms n))
      (measureCovectorFunctional M) hconv U

theorem variation_le_liminf_of_currentTest_tendsto
    (Ms : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (hconv : ∀ ω : OneFormCurrentTest d,
      Tendsto (fun n => measureOneCurrent (Ms n) ω) atTop (𝓝 (measureOneCurrent M ω)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    M.variation U ≤ Filter.liminf (fun n => (Ms n).variation U) atTop :=
  variation_le_liminf_of_covectorTest_tendsto Ms M hconv hU

theorem variation_le_liminf_of_weaklyTendsto
    (Ms : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (hM : VectorMeasureWeaklyTendsto Ms M)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    M.variation U ≤ Filter.liminf (fun n => (Ms n).variation U) atTop := by
  apply variation_le_liminf_of_covectorTest_tendsto Ms M _ hU
  intro ω
  simpa [measureCovectorFunctional_apply, vectorMeasurePairing] using
    hM (ω : BoundedCovectorField d m)

end GeometricMeasure

