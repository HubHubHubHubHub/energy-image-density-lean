import ErrorCalculus.Dirichlet.ErrorStructure
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Module
import Mathlib.Tactic.FunProp

/-!
# Cauchy–Schwarz bounds for the carré du champ

This file contains the definitions and results of the development of
`ErrorCalculus.Dirichlet.ExtensionGammaBounds` that the main statements of the library (the head
theorems listed in the README of the repository) use. `ErrorCalculus.Dirichlet.ExtensionGammaBounds`
imports it and continues the development.

## Main definitions

* `ErrorData.sqrtGamma`: The square root as an L² class.

## Main statements

* `ErrorData.norm_gamma_le_energy`: The carré du champ is bounded for the energy seminorm in both
  arguments.
-/
noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorData
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorData Ω μ)

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



/-- absolute-value form of pointwise Cauchy--Schwarz. -/
theorem gamma_abs_le (u v : S.dom) :
    ∀ᵐ ω ∂μ, |S.Γ u v ω| ≤ Real.sqrt (S.Γ u u ω) * Real.sqrt (S.Γ v v ω) := by
  filter_upwards [S.gamma_cauchy_schwarz u v, S.Γ_nonneg u, S.Γ_nonneg v] with ω hc hu hv
  have h := Real.sq_sqrt hu
  have h' := Real.sq_sqrt hv
  have hn := Real.sqrt_nonneg (S.Γ u u ω)
  have hn' := Real.sqrt_nonneg (S.Γ v v ω)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hn hn')).mp
  simpa [mul_pow, h, h'] using hc

/-- Square roots of nonnegative L¹ diagonals belong to L². -/
theorem sqrtGamma_memLp (u : S.dom) : MemLp (fun ω => Real.sqrt (S.Γ u u ω)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_sqrt.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))).mpr
  apply (L1.integrable_coeFn (S.Γ u u)).congr
  filter_upwards [S.Γ_nonneg u] with ω hω
  exact (Real.sq_sqrt hω).symm

/-- The square root as an L² class. -/
def sqrtGamma (u : S.dom) : Lp ℝ 2 μ := (S.sqrtGamma_memLp u).toLp _

theorem coeFn_sqrtGamma (u : S.dom) :
    ⇑(S.sqrtGamma u) =ᵐ[μ] fun ω => Real.sqrt (S.Γ u u ω) :=
  (S.sqrtGamma_memLp u).coeFn_toLp

theorem norm_sqrtGamma_sq (u : S.dom) : ‖S.sqrtGamma u‖^2 = 2 * S.energy.E u u := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, energy_apply]
  have he : (∫ ω, inner ℝ (S.sqrtGamma u ω) (S.sqrtGamma u ω) ∂μ) = ∫ ω, S.Γ u u ω ∂μ := by
    apply integral_congr_ae
    filter_upwards [S.coeFn_sqrtGamma u, S.Γ_nonneg u] with ω he hp
    rw [he, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hp]
  rw [he]
  ring

theorem norm_sqrtGamma (u : S.dom) :
    ‖S.sqrtGamma u‖ = Real.sqrt 2 * S.energy.seminorm u := by
  rw [← Real.sqrt_sq (norm_nonneg _), S.norm_sqrtGamma_sq, Real.sqrt_mul (by norm_num)]
  rfl

/-- Hölder's inequality applied to pointwise Cauchy--Schwarz. -/
theorem norm_gamma_le (u v : S.dom) : ‖S.Γ u v‖ ≤ ‖S.sqrtGamma u‖ * ‖S.sqrtGamma v‖ := by
  calc
    ‖S.Γ u v‖ = ∫ ω, ‖S.Γ u v ω‖ ∂μ := L1.norm_eq_integral_norm _
    _ ≤ ∫ ω, S.sqrtGamma u ω * S.sqrtGamma v ω ∂μ := by
      apply integral_mono_ae (L1.integrable_coeFn _).norm
        ((Lp.memLp (S.sqrtGamma u)).integrable_mul (Lp.memLp (S.sqrtGamma v)))
      filter_upwards [S.coeFn_sqrtGamma u, S.coeFn_sqrtGamma v, S.gamma_abs_le u v] with ω hu hv hc
      simpa only [Pi.mul_apply, Real.norm_eq_abs, hu, hv] using hc
    _ = inner ℝ (S.sqrtGamma u) (S.sqrtGamma v) := by
      rw [L2.inner_def]
      simp only [RCLike.inner_apply, conj_trivial, mul_comm]
    _ ≤ ‖S.sqrtGamma u‖ * ‖S.sqrtGamma v‖ := real_inner_le_norm _ _

/-- The carré du champ is bounded for the energy seminorm in both arguments. -/
theorem norm_gamma_le_energy (u v : S.dom) :
    ‖S.Γ u v‖ ≤ 2 * S.energy.seminorm u * S.energy.seminorm v := by
  have h := S.norm_gamma_le u v
  rw [S.norm_sqrtGamma, S.norm_sqrtGamma] at h
  convert h using 1
  calc
    2 * S.energy.seminorm u * S.energy.seminorm v =
        (Real.sqrt 2)^2 * S.energy.seminorm u * S.energy.seminorm v := by rw [Real.sq_sqrt (by norm_num)]
    _ = _ := by ring

end ErrorCalculus.ErrorData
