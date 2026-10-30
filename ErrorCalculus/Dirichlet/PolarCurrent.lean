import ErrorCalculus.Dirichlet.EIDVectorChain
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Polar Current

## Main results
Finite one-currents in polar form. The norm of the direction is the Euclidean norm, even though the
underlying coordinate space carries the Pi norm. Normality uses a difference of two finite positive
measures.
-/
noncomputable section
open scoped ContDiff
open MeasureTheory Filter
namespace ErrorCalculus

/-- Euclidean length of a coordinate vector. -/
def polarNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ‖ErrorStructure.euclideanEquiv n x‖

theorem polarNorm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ polarNorm x := norm_nonneg _

@[simp] theorem polarNorm_eq_zero {n : ℕ} {x : Fin n → ℝ} :
    polarNorm x = 0 ↔ x = 0 := by simp [polarNorm]

theorem polarNorm_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    polarNorm (c • x) = |c| * polarNorm x := by
  simp [polarNorm, norm_smul, Real.norm_eq_abs]

theorem continuous_polarNorm (n : ℕ) : Continuous (polarNorm (n := n)) :=
  (ErrorStructure.euclideanEquiv n).continuous.norm

/-- In Mathlib 4.32.1, smoothness and analyticity have distinct orders.
The smooth tests in normality must use ∞, not the outer top (analytic order). -/
theorem smoothOrder_ne_analyticOrder : (∞ : WithTop ℕ∞) ≠ ⊤ := by simp

/-- A finite one-current: its mass and a measurable Euclidean unit direction.
No assumption about a distributional boundary is part of this structure. -/
structure PolarCurrent (n : ℕ) where
  mass : Measure (Fin n → ℝ)
  finite_mass : IsFiniteMeasure mass
  direction : (Fin n → ℝ) → (Fin n → ℝ)
  measurable_direction : Measurable direction
  norm_direction : ∀ᵐ y ∂mass, polarNorm (direction y) = 1

attribute [instance] PolarCurrent.finite_mass

namespace PolarCurrent
variable {n : ℕ}

/-- Action on a one-form. Bounded measurable coefficients ensure integrability;
the integral also gives a total definition for arbitrary coefficients. -/
def action (T : PolarCurrent n) (h : Fin n → (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ y, ∑ j, h j y * T.direction y j ∂T.mass

/-- Distributional boundary evaluated on a smooth scalar test. -/
def boundary (T : PolarCurrent n) (φ : (Fin n → ℝ) → ℝ) : ℝ :=
  T.action (fun j y => fderiv ℝ φ y (Pi.single j 1))

/--
Normality means that the boundary on smooth compactly supported tests equals the negative of a
finite signed measure σ = σ⁺ − σ⁻, the distributional divergence.

For the `ErrorStructure` current formed from Γ(f_j, g), E = (1/2)∫Γ gives divergence 2 f_*(Ag μ) and
boundary −2 f_*(Ag μ), when g belongs to the generator domain. The BH current in
`DprBridge.BH1991ChainCurrents` instead uses Γ/2 and centered tests: its divergence is f_*(Ag m) −
(∫ Ag dm) δ₀, with the opposite boundary. The Dirac correction is the centering in
Eriksson-Bique–Murugan, Section 4.2, Remark 4.12.
-/
def IsNormal (T : PolarCurrent n) : Prop :=
  ∃ σp σm : Measure (Fin n → ℝ), IsFiniteMeasure σp ∧ IsFiniteMeasure σm ∧
    ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      T.boundary φ = -(∫ y, φ y ∂σp) + ∫ y, φ y ∂σm

end PolarCurrent
end ErrorCalculus
