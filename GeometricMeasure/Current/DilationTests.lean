import GeometricMeasure.VectorMeasure.DilationGeometry
import GeometricMeasure.Current.Tests
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! Affine dilations and pullbacks of compactly supported smooth tests. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped ENNReal Topology

namespace GeometricMeasure
variable {d : ℕ}

def dilationHomeomorph (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) :
    EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d) :=
  (Homeomorph.addRight (-x₀)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr))

theorem dilationHomeomorph_apply (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0)
    (x : EuclideanSpace ℝ (Fin d)) :
    dilationHomeomorph x₀ r hr x = dilationEquiv x₀ r hr x := rfl

theorem contDiff_dilationEquiv (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (dilationEquiv x₀ r hr) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => r⁻¹ • (x - x₀))
  exact (contDiff_id.sub contDiff_const).const_smul _

theorem fderiv_dilationEquiv (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0)
    (x : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (dilationEquiv x₀ r hr) x =
      r⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
  exact (((hasFDerivAt_id x).sub_const x₀).const_smul r⁻¹).fderiv

def dilationTest {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) :
    TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞) →ₗ[ℝ]
      TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞) where
  toFun φ := {
    toFun := fun x => φ (dilationEquiv x₀ r hr x)
    contDiff' := φ.contDiff.comp (contDiff_dilationEquiv x₀ r hr)
    hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (dilationHomeomorph x₀ r hr)
    tsupport_subset' := subset_univ _ }
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl

theorem dilationTest_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0)
    (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞))
    (x : EuclideanSpace ℝ (Fin d)) :
    dilationTest x₀ r hr φ x = φ (dilationEquiv x₀ r hr x) := rfl

theorem tsupport_dilationTest {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0)
    (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞)) :
    tsupport (dilationTest x₀ r hr φ : EuclideanSpace ℝ (Fin d) → F) =
      (dilationEquiv x₀ r hr) ⁻¹' tsupport (φ : EuclideanSpace ℝ (Fin d) → F) :=
  tsupport_comp_eq_preimage φ (dilationHomeomorph x₀ r hr)

theorem currentTestDerivative_dilationTest (x₀ : EuclideanSpace ℝ (Fin d))
    (r : ℝ) (hr : r ≠ 0) (φ : ScalarCurrentTest d) :
    currentTestDerivative (dilationTest x₀ r hr φ) =
      r⁻¹ • dilationTest x₀ r hr (currentTestDerivative φ) := by
  apply TestFunction.ext
  intro x
  change fderiv ℝ (fun y => φ (r⁻¹ • (y - x₀))) x =
    r⁻¹ • fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (r⁻¹ • (x - x₀))
  rw [fderiv_comp_sub (f := fun y => φ (r⁻¹ • y)), fderiv_comp_smul]

def dilationPullbackOneForm (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) :
    OneFormCurrentTest d →ₗ[ℝ] OneFormCurrentTest d :=
  r⁻¹ • dilationTest x₀ r hr

end GeometricMeasure
