import ErrorCalculus.Dirichlet.Calculus
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Module
import Mathlib.Tactic.FunProp

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- The quadratic polynomial identity in L¹. -/
theorem gamma_polynomial (u v : S.dom) (t : ℝ) :
    S.Γ (u + t • v) (u + t • v) =
      S.Γ u u + (2*t) • S.Γ u v + t^2 • S.Γ v v := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    S.Γ_symm v u, smul_add, smul_smul]
  module

/-- positivity of every real quadratic perturbation, almost surely for each parameter. -/
theorem gamma_polynomial_nonneg (u v : S.dom) (t : ℝ) :
    ∀ᵐ ω ∂μ, 0 ≤ S.Γ u u ω + (2*t) * S.Γ u v ω + t^2 * S.Γ v v ω := by
  have hp := S.Γ_nonneg (u + t • v)
  rw [S.gamma_polynomial u v t] at hp
  filter_upwards [hp, Lp.coeFn_add (S.Γ u u + (2*t) • S.Γ u v) (t^2 • S.Γ v v),
    Lp.coeFn_add (S.Γ u u) ((2*t) • S.Γ u v),
    Lp.coeFn_smul (2*t) (S.Γ u v), Lp.coeFn_smul (t^2) (S.Γ v v)] with ω hp h1 h2 h3 h4
  simpa only [h1, h2, h3, h4, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using hp

/-- almost sure Cauchy--Schwarz, using only a countable intersection over rationals. -/
theorem gamma_cauchy_schwarz (u v : S.dom) :
    ∀ᵐ ω ∂μ, (S.Γ u v ω)^2 ≤ S.Γ u u ω * S.Γ v v ω := by
  have hq : ∀ᵐ ω ∂μ, ∀ t : ℚ,
      0 ≤ S.Γ u u ω + (2*(t:ℝ)) * S.Γ u v ω + (t:ℝ)^2 * S.Γ v v ω :=
    ae_all_iff.mpr fun t => S.gamma_polynomial_nonneg u v t
  filter_upwards [hq] with ω hω
  have hr : ∀ t : ℝ, 0 ≤ S.Γ u u ω + (2*t) * S.Γ u v ω + t^2 * S.Γ v v ω := by
    intro t
    exact Rat.denseRange_cast.induction_on t (isClosed_le continuous_const (by fun_prop)) hω
  have hd := discrim_le_zero (a := S.Γ v v ω) (b := 2*S.Γ u v ω) (c := S.Γ u u ω)
    (fun t => by nlinarith [hr t])
  dsimp [discrim] at hd
  nlinarith

end ErrorCalculus.ErrorStructure
