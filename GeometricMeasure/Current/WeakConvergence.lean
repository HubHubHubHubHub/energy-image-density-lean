import GeometricMeasure.VectorMeasure.WeakConvergence
import GeometricMeasure.Current.MeasureCurrent

/-! Weak convergence through bounded covector fields and positive coordinates. -/
noncomputable section
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ} {m : ℕ}

theorem vectorMeasurePairing_currentTest
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (ω : OneFormCurrentTest d) :
    vectorMeasurePairing M (ω : BoundedCovectorField d d) = measureOneCurrent M ω :=
  (measureOneCurrent_apply M ω).symm

/-- Lower semicontinuity of the test supremum, on every set. -/
theorem testFunctionalMassOn_le_liminf
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ts : ℕ → TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞) →L[ℝ] ℝ)
    (T : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞) →L[ℝ] ℝ)
    (hconv : ∀ ω, Tendsto (fun n => Ts n ω) atTop (𝓝 (T ω)))
    (U : Set (EuclideanSpace ℝ (Fin d))) :
    testFunctionalMassOn T U ≤
      Filter.liminf (fun n => testFunctionalMassOn (Ts n) U) atTop := by
  apply testFunctionalMassOn_le
  intro ω hs hn
  have h := (ENNReal.continuous_ofReal.tendsto (T ω)).comp (hconv ω)
  rw [← h.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall
    (fun n => ofReal_apply_le_testFunctionalMassOn (Ts n) U ω hs hn))

end GeometricMeasure
