import ErrorCalculus.Dirichlet.FiniteEnergyDual
import Mathlib.Tactic
import ErrorCalculus.Dirichlet.WhiteNoiseHilbert.Basic
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Potentials, equilibrium distributions and capacity duality

This file contains the definitions and results of the development of
`ErrorCalculus.Dirichlet.FiniteEnergyPotential` that the main statements of the library (the head
theorems listed in the README of the repository) use, together with the basic API of their
definitions and the other results of the sections they belong to.
`ErrorCalculus.Dirichlet.FiniteEnergyPotential` imports it and continues the development.

## Main definitions

* `Capacity.DirichletForm.potential`: Fukushima 1980, § 3.2, (3.2.2) (p. 69), α = 1, and BH 1991,
  ch. I § 9.1, proposition 9.1.3 a) (p. 62): the potential U₁T of a finite-energy distribution
  (Riesz representation).
* `Capacity.DirichletForm.IsPosOn`: Positivity of T "on G" (on v ≥ 0 a.e. on G).

## Main statements

* `Capacity.DirichletForm.norm_potential`: The form norm of a potential equals the dual norm of its
  functional.
* `Capacity.DirichletForm.potential_toDual`: Taking the potential of the Riesz functional associated
  with u recovers u.
* `Capacity.DirichletForm.potential_mem_posCone`: Fukushima 1980, § 3.2, Theorem 3.2.1, (i) ⇔ (iv)
  and (iv) ⇒ u ≥ 0 (p. 69), in Hilbert-space form: the potential of a positive distribution is
  nonnegative.
* `Capacity.DirichletForm.toDual_mem_dualPos_iff`: The Riesz functional of u is positive exactly
  when u pairs nonnegatively with the positive cone.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace ErrorCalculus.Capacity
namespace DirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (D : DirichletForm μ)

/-! ## B. Potentials, positivity, equilibrium distribution (Fukushima § 3.2–3.3) -/

section Potentials

/--
Fukushima 1980, § 3.2, (3.2.2) (p. 69), α = 1, and BH 1991, ch. I § 9.1, proposition 9.1.3 a) (p.
62): the potential U₁T of a finite-energy distribution (Riesz representation).

The potential of T ∈ 𝔻': the unique u ∈ 𝔻 such that (u, v)_𝔻 = ⟨v, T⟩ for every v ∈ 𝔻.
-/
def potential (T : D.Dual) : D.Space := (InnerProductSpace.toDual ℝ D.Space).symm T

/-- The potential of T pairs with every form element v to give T(v). -/
theorem inner_potential (T : D.Dual) (v : D.Space) : ⟪D.potential T, v⟫_ℝ = T v :=
  InnerProductSpace.toDual_symm_apply

/-- The form norm of a potential equals the dual norm of its functional. -/
theorem norm_potential (T : D.Dual) : ‖D.potential T‖ = ‖T‖ :=
  LinearIsometryEquiv.norm_map _ _

/--
Fukushima 1980, § 3.2, (3.2.2) (p. 69): uniqueness of the potential.

If (u, v)_𝔻 = ⟨v, T⟩ for every v, then u is the potential of T.
-/
theorem eq_potential {T : D.Dual} {u : D.Space} (h : ∀ v, ⟪u, v⟫_ℝ = T v) : u = D.potential T :=
  ext_inner_right ℝ fun v => by rw [h, inner_potential]

/-- Taking the potential of the Riesz functional associated with u recovers u. -/
theorem potential_toDual (u : D.Space) :
    D.potential (InnerProductSpace.toDual ℝ D.Space u) = u :=
  (InnerProductSpace.toDual ℝ D.Space).symm_apply_apply u

/-- u = u ∨ 0 + u ∧ 0 in 𝔻. -/
theorem supS_add_infS_zero (u : D.Space) : D.supS u 0 + D.infS u 0 = u := by
  apply D.toLp_injective
  rw [map_add, D.toLp_supS, D.toLp_infS, map_zero, add_comm, inf_add_sup, add_zero]

/--
Fukushima 1980, § 3.2, Theorem 3.2.1, (iv) ⇒ u ≥ 0 (proof, p. 69); argument using BH Lemma 8.1.2.1
(p. 52) in place of minimization on 𝓛_u.

If ℰ₁(u, v) ≥ 0 for every v ∈ 𝔻⁺, then u ∈ 𝔻⁺.
-/
theorem mem_posCone_of_inner_nonneg {u : D.Space} (hu : ∀ v ∈ D.posCone, 0 ≤ ⟪u, v⟫_ℝ) :
    u ∈ D.posCone := by
  set s := D.supS u 0 with hs
  set i := D.infS u 0 with hi
  have hsi : s + i = u := D.supS_add_infS_zero u
  have hl : ‖s‖ ^ 2 + ‖i‖ ^ 2 ≤ ‖u‖ ^ 2 + ‖(0 : D.Space)‖ ^ 2 := D.bh_8_1_2_1 u 0
  have hneg : -i ∈ D.posCone := by
    show 0 ≤ D.toLp (-i)
    rw [map_neg, hi, D.toLp_infS, map_zero, neg_nonneg]
    exact inf_le_right
  have h1 := hu _ hneg
  have hu2 : ‖u‖ ^ 2 = ‖s‖ ^ 2 + 2 * ⟪s, i⟫_ℝ + ‖i‖ ^ 2 := by
    rw [← hsi]
    exact norm_add_sq_real s i
  have hui : ⟪u, -i⟫_ℝ = -(⟪s, i⟫_ℝ + ‖i‖ ^ 2) := by
    rw [inner_neg_right, ← hsi, inner_add_left, real_inner_self_eq_norm_sq]
  rw [hui] at h1
  rw [norm_zero] at hl
  have hi2 : ‖i‖ ^ 2 ≤ 0 := by nlinarith
  have hi0 : i = 0 := norm_eq_zero.1 (by nlinarith [norm_nonneg i])
  have hinf : D.toLp u ⊓ 0 = 0 := by
    have h := congrArg D.toLp hi0
    rw [hi, D.toLp_infS, map_zero] at h
    exact h
  exact inf_eq_right.1 hinf

/--
Fukushima 1980, § 3.2, Theorem 3.2.1, (i) ⇔ (iv) and (iv) ⇒ u ≥ 0 (p. 69), in Hilbert-space form:
the potential of a positive distribution is nonnegative.

The potential of T ∈ 𝔻'⁺ belongs to 𝔻⁺.
-/
theorem potential_mem_posCone {T : D.Dual} (hT : T ∈ D.dualPos) : D.potential T ∈ D.posCone :=
  D.mem_posCone_of_inner_nonneg fun v hv => by rw [inner_potential]; exact hT v hv

/--
The Riesz functional of u is positive exactly when u pairs nonnegatively with the positive cone.
-/
theorem toDual_mem_dualPos_iff (u : D.Space) :
    InnerProductSpace.toDual ℝ D.Space u ∈ D.dualPos ↔ ∀ v ∈ D.posCone, 0 ≤ ⟪u, v⟫_ℝ := by
  simp only [dualPos, Set.mem_setOf_eq, InnerProductSpace.toDual_apply_apply]

/-- Positivity of T "on G" (on v ≥ 0 a.e. on G). -/
def IsPosOn (G : Set Ω) (T : D.Dual) : Prop :=
  ∀ v : D.Space, (∀ᵐ ω ∂μ, ω ∈ G → 0 ≤ D.toLp v ω) → 0 ≤ T v

end Potentials

end DirichletForm
end ErrorCalculus.Capacity
