import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Smooth covector tests, boundary and the mass defined by a supremum of tests. -/

noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace GeometricMeasure

abbrev ScalarCurrentTest (d : ℕ) :=
  TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) ℝ (⊤ : ℕ∞)

abbrev OneFormCurrentTest (d : ℕ) :=
  TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d)))
    (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (⊤ : ℕ∞)

variable {d : ℕ}

def currentTestDerivative : ScalarCurrentTest d →L[ℝ] OneFormCurrentTest d :=
  TestFunction.fderivCLM ℝ (⊤ : ℕ∞) (⊤ : ℕ∞)

theorem currentTestDerivative_apply (φ : ScalarCurrentTest d) :
    (currentTestDerivative φ : EuclideanSpace ℝ (Fin d) →
      (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) = fderiv ℝ φ :=
  TestFunction.fderivCLM_apply_of_le φ (by simp)

def oneCurrentBoundary (T : OneFormCurrentTest d →L[ℝ] ℝ) :
    ScalarCurrentTest d →L[ℝ] ℝ := T.comp currentTestDerivative

theorem oneCurrentBoundary_apply (T : OneFormCurrentTest d →L[ℝ] ℝ)
    (φ : ScalarCurrentTest d) :
    oneCurrentBoundary T φ = T (currentTestDerivative φ) := rfl

def testFunctionalMassOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d)))
      F (⊤ : ℕ∞) →L[ℝ] ℝ) (U : Set (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ⨆ (ω : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞))
    (_ : tsupport (ω : EuclideanSpace ℝ (Fin d) → F) ⊆ U)
    (_ : ∀ x, ‖ω x‖ ≤ 1), ENNReal.ofReal (T ω)

def IsNormalOneCurrent (T : OneFormCurrentTest d →L[ℝ] ℝ) : Prop :=
  testFunctionalMassOn T Set.univ < ⊤ ∧
    testFunctionalMassOn (oneCurrentBoundary T) Set.univ < ⊤

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (T : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d)))
  F (⊤ : ℕ∞) →L[ℝ] ℝ) (U : Set (EuclideanSpace ℝ (Fin d)))

theorem ofReal_apply_le_testFunctionalMassOn
    (ω : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞))
    (hs : tsupport (ω : EuclideanSpace ℝ (Fin d) → F) ⊆ U)
    (hn : ∀ x, ‖ω x‖ ≤ 1) : ENNReal.ofReal (T ω) ≤ testFunctionalMassOn T U :=
  le_iSup_of_le ω (le_iSup_of_le hs (le_iSup_of_le hn le_rfl))

theorem testFunctionalMassOn_le {r : ℝ≥0∞}
    (h : ∀ ω : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞),
      tsupport (ω : EuclideanSpace ℝ (Fin d) → F) ⊆ U →
      (∀ x, ‖ω x‖ ≤ 1) → ENNReal.ofReal (T ω) ≤ r) :
    testFunctionalMassOn T U ≤ r :=
  iSup_le fun ω => iSup_le fun hs => iSup_le fun hn => h ω hs hn

theorem testFunctionalMassOn_mono {V : Set (EuclideanSpace ℝ (Fin d))}
    (hUV : U ⊆ V) : testFunctionalMassOn T U ≤ testFunctionalMassOn T V :=
  testFunctionalMassOn_le T U fun ω hs hn =>
    ofReal_apply_le_testFunctionalMassOn T V ω (hs.trans hUV) hn

theorem testFunctionalMassOn_zero :
    testFunctionalMassOn (0 : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d)))
      F (⊤ : ℕ∞) →L[ℝ] ℝ) U = 0 := by
  simp [testFunctionalMassOn]

end GeometricMeasure
