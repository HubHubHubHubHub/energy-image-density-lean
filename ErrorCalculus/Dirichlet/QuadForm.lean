import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Sequences

/-!
# Quadratic forms on linear domains

## Main results
A symmetric nonnegative bilinear form on a linear domain defines an energy seminorm and a Hilbert
completion, including the quotient by null vectors. The canonical energy map need not be injective.
The energy inequalities yield limits for form-Cauchy sequences; closedness and closability are
expressed sequentially. In a complete ambient space, closedness is equivalent to sequential
completeness for the form norm.
-/

noncomputable section
open Filter Topology
namespace ErrorCalculus

/-- a symmetric nonnegative bilinear form on a linear domain. -/
structure QuadForm (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  dom : Submodule ℝ H
  E : dom →ₗ[ℝ] dom →ₗ[ℝ] ℝ
  symm : ∀ u v, E u v = E v u
  nonneg : ∀ u, 0 ≤ E u u

namespace QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (Q : QuadForm H)

/-- domain equipped with the energy seminorm (a type synonym). -/
def EnergySpace : Type _ := Q.dom
instance : AddCommGroup Q.EnergySpace := inferInstanceAs (AddCommGroup Q.dom)
instance : Module ℝ Q.EnergySpace := inferInstanceAs (Module ℝ Q.dom)

/-- The positive semidefinite inner product attached to the form. -/
@[implicit_reducible] def energyCore : PreInnerProductSpace.Core ℝ Q.EnergySpace where
  inner := fun x y => Q.E x y
  conj_inner_symm x y := by simpa using Q.symm y x
  re_inner_nonneg := Q.nonneg
  add_left x y z := by
    change Q.E ((show Q.dom from x) + (show Q.dom from y)) z = _
    rw [map_add, LinearMap.add_apply]
  smul_left x y r := by
    change Q.E (r • (show Q.dom from x)) y = r * Q.E x y
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

instance energySeminormed : SeminormedAddCommGroup Q.EnergySpace :=
  letI := Q.energyCore
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)
instance energyNormed : NormedSpace ℝ Q.EnergySpace :=
  letI := Q.energyCore
  InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ)
instance energyInner : InnerProductSpace ℝ Q.EnergySpace :=
  InnerProductSpace.ofCore Q.energyCore

/-- The Hilbert completion of the energy seminorm, including its null quotient. -/
abbrev EnergyHilbert := UniformSpace.Completion Q.EnergySpace

/-- algebraic identification with the energy-domain type synonym. -/
def toEnergy : Q.dom ≃ₗ[ℝ] Q.EnergySpace where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- canonical energy map; no injectivity is asserted. -/
def j : Q.dom →ₗ[ℝ] Q.EnergyHilbert :=
  (UniformSpace.Completion.toComplₗᵢ : Q.EnergySpace →ₗᵢ[ℝ] Q.EnergyHilbert).toLinearMap.comp
    Q.toEnergy.toLinearMap

@[simp] theorem inner_j (u v : Q.dom) : inner ℝ (Q.j u) (Q.j v) = Q.E u v :=
  UniformSpace.Completion.inner_coe (𝕜 := ℝ) (Q.toEnergy u) (Q.toEnergy v)

/-- The energy seminorm. -/
def seminorm (u : Q.dom) : ℝ := Real.sqrt (Q.E u u)

@[simp] theorem norm_j (u : Q.dom) : ‖Q.j u‖ = Q.seminorm u := by
  rw [norm_eq_sqrt_real_inner, Q.inner_j]; rfl

/-- Cauchy--Schwarz, including null energy vectors. -/
theorem cauchy_schwarz (u v : Q.dom) : |Q.E u v| ≤ Q.seminorm u * Q.seminorm v := by
  simpa only [← Q.inner_j, ← Q.norm_j, Real.norm_eq_abs] using
    norm_inner_le_norm (𝕜 := ℝ) (Q.j u) (Q.j v)

/-- The energy triangle inequality. -/
theorem seminorm_add (u v : Q.dom) : Q.seminorm (u + v) ≤ Q.seminorm u + Q.seminorm v := by
  simpa only [← Q.norm_j, map_add] using norm_add_le (Q.j u) (Q.j v)

/-- reverse triangle inequality. -/
theorem seminorm_sub (u v : Q.dom) : |Q.seminorm u - Q.seminorm v| ≤ Q.seminorm (u - v) := by
  simpa only [← Q.norm_j, map_sub] using abs_norm_sub_norm_le (Q.j u) (Q.j v)

/-- absolute homogeneity. -/
theorem seminorm_smul (c : ℝ) (u : Q.dom) : Q.seminorm (c • u) = |c| * Q.seminorm u := by
  simp only [← Q.norm_j, map_smul, norm_smul, Real.norm_eq_abs]

/-- an injective graph map realizes the form norm on its domain. -/
def graphMap : Q.dom →ₗ[ℝ] H × Q.EnergyHilbert := Q.dom.subtype.prod Q.j

/-- a sequence is form-Cauchy when both ambient and energy coordinates are Cauchy. -/
def IsCauchy (u : ℕ → Q.dom) : Prop :=
  CauchySeq (fun n => (u n : H)) ∧ CauchySeq (fun n => Q.j (u n))

/-- equivalence with the explicit epsilon definition in the paper. -/
theorem isCauchy_iff (u : ℕ → Q.dom) : Q.IsCauchy u ↔
    CauchySeq (fun n => (u n : H)) ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, Q.seminorm (u m - u n) < ε := by
  simp only [IsCauchy, Metric.cauchySeq_iff, dist_eq_norm, ← map_sub, Q.norm_j]

/-- convergence of the energy seminorm of a form-Cauchy sequence. -/
theorem exists_seminorm_limit {u : ℕ → Q.dom} (hu : Q.IsCauchy u) :
    ∃ a : ℝ, Tendsto (fun n => Q.seminorm (u n)) atTop (𝓝 a) := by
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hu.2
  exact ⟨‖a‖, by simpa only [Q.norm_j] using ha.norm⟩

/-- convergence of mixed energies. -/
theorem exists_energy_limit {u v : ℕ → Q.dom} (hu : Q.IsCauchy u) (hv : Q.IsCauchy v) :
    ∃ a : ℝ, Tendsto (fun n => Q.E (u n) (v n)) atTop (𝓝 a) := by
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hu.2
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hv.2
  exact ⟨inner ℝ a b, by simpa only [Q.inner_j] using ha.inner (𝕜 := ℝ) hb⟩

/-- convergence of diagonal energies. -/
theorem exists_diagonal_limit {u : ℕ → Q.dom} (hu : Q.IsCauchy u) :
    ∃ a : ℝ, Tendsto (fun n => Q.E (u n) (u n)) atTop (𝓝 a) :=
  Q.exists_energy_limit hu hu

/-- closedness in the precise sequential sense. -/
def IsClosed : Prop := ∀ (u : ℕ → Q.dom), Q.IsCauchy u →
  ∀ v : H, Tendsto (fun n => (u n : H)) atTop (𝓝 v) →
    ∃ hv : v ∈ Q.dom, Tendsto (fun n => Q.E (u n - ⟨v, hv⟩) (u n - ⟨v, hv⟩)) atTop (𝓝 0)

/-- closability tests sequences converging to zero in the ambient space. -/
def IsClosable : Prop := ∀ (u : ℕ → Q.dom), Q.IsCauchy u →
  Tendsto (fun n => (u n : H)) atTop (𝓝 0) →
    Tendsto (fun n => Q.E (u n) (u n)) atTop (𝓝 0)

/-- Every closed form is closable. -/
theorem IsClosed.isClosable (h : Q.IsClosed) : Q.IsClosable := by
  intro u hu h0
  obtain ⟨hv, he⟩ := h u hu 0 h0
  have hz : (⟨0, hv⟩ : Q.dom) = 0 := rfl
  simpa only [hz, sub_zero] using he

/-- closedness is sequential completeness for the form norm. -/
theorem isClosed_iff_complete [CompleteSpace H] : Q.IsClosed ↔
    ∀ u : ℕ → Q.dom, Q.IsCauchy u → ∃ v : Q.dom,
      Tendsto (fun n => (u n : H)) atTop (𝓝 (v : H)) ∧
      Tendsto (fun n => Q.E (u n - v) (u n - v)) atTop (𝓝 0) := by
  constructor
  · intro h u hu
    obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hu.1
    obtain ⟨hd, he⟩ := h u hu v hv
    exact ⟨⟨v, hd⟩, hv, he⟩
  · intro h u hu v hv
    obtain ⟨w, hw, he⟩ := h u hu
    have heq := tendsto_nhds_unique hv hw
    subst v
    exact ⟨w.property, he⟩

/-- energy convergence to zero is convergence of the energy coordinate. -/
theorem energy_tendsto_zero_iff {u : ℕ → Q.dom} :
    Tendsto (fun n => Q.E (u n) (u n)) atTop (𝓝 0) ↔
      Tendsto (fun n => Q.j (u n)) atTop (𝓝 0) := by
  constructor
  · intro h
    have hh := h.sqrt
    rw [Real.sqrt_zero] at hh
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Q.norm_j, seminorm] using hh
  · intro h
    simpa only [Q.inner_j, inner_zero_left] using h.inner (𝕜 := ℝ) h

end QuadForm
end ErrorCalculus
