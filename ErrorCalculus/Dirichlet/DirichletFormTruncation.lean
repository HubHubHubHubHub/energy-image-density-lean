import ErrorCalculus.Dirichlet.FiniteEnergyExamples
import ErrorCalculus.Dirichlet.DensityDomainEquality
import ErrorCalculus.Dirichlet.WhiteNoiseHilbert
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Tactic

/-!
# Truncation convergence in a Dirichlet form

## Main results
Symmetric truncations of a domain element converge in the form norm and in energy.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity.DirichletForm

section Truncation
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (D : DirichletForm μ)

/-- The clamp t ↦ (−n) ∨ (t ∧ n) is a normal contraction (1-Lipschitz). -/
theorem lipschitzWith_trunc (n : ℕ) :
    LipschitzWith 1 (fun t : ℝ => max (min t (n : ℝ)) (-(n : ℝ))) :=
  (LipschitzWith.id.min_const _).max_const _

/-- The clamp fixes 0. -/
theorem trunc_zero (n : ℕ) : max (min (0 : ℝ) (n : ℝ)) (-(n : ℝ)) = 0 := by
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [min_eq_left h0, max_eq_left (by linarith)]

/--
((−n) ∨ (t ∧ n) − t)² ≤ t²: domination of the clamping error, for dominated convergence in L².
-/
theorem trunc_sub_sq_le (n : ℕ) (t : ℝ) :
    (max (min t (n : ℝ)) (-(n : ℝ)) - t) ^ 2 ≤ t ^ 2 := by
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases le_or_gt t n with h1 | h1 <;> rcases le_or_gt (-(n : ℝ)) t with h2 | h2
  · rw [min_eq_left h1, max_eq_left h2, sub_self]
    nlinarith [sq_nonneg t]
  · rw [min_eq_left h1, max_eq_right h2.le]
    nlinarith
  · rw [min_eq_right h1.le, max_eq_left (by linarith)]
    nlinarith
  · linarith

/-- For n ≥ |t|, the clamp leaves t unchanged. -/
theorem eventually_trunc_eq (t : ℝ) :
    ∀ᶠ n : ℕ in atTop, max (min t (n : ℝ)) (-(n : ℝ)) = t := by
  obtain ⟨N, hN⟩ := exists_nat_ge |t|
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h := abs_le.1 (hN.trans hn')
  rw [min_eq_left h.2, max_eq_left h.1]

/--
BH 1991, ch. I § 9.2, end of the proof of proposition 9.2.1 (p. 63): "f ∧ n converges … also in 𝔻",
asserted without proof by BH, is proved here. The clamps (−n) ∨ (x ∧ n) converge to x in 𝔻
(bounded by ‖x‖, convergent in L² and hence weakly, with nonincreasing norm).
-/
theorem tendsto_contract_trunc (x : D.Space) :
    Tendsto (fun n : ℕ => D.contract (lipschitzWith_trunc n)
      (trunc_zero n) x) atTop (𝓝 x) := by
  have hb : ∀ n : ℕ, ‖D.contract (lipschitzWith_trunc n)
      (trunc_zero n) x‖ ≤ ‖x‖ := fun n => D.norm_contract_le _ _ x
  have key : ∀ n : ℕ, ‖D.toLp (D.contract (lipschitzWith_trunc n)
      (trunc_zero n) x) - D.toLp x‖ ^ 2 =
      ∫ ω, (max (min (D.toLp x ω) (n : ℝ)) (-(n : ℝ)) - D.toLp x ω) ^ 2 ∂μ := by
    intro n
    rw [← ErrorCalculus.l2_integral_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (D.toLp (D.contract (lipschitzWith_trunc n)
        (trunc_zero n) x)) (D.toLp x),
      D.coe_contractLp (lipschitzWith_trunc n) (trunc_zero n) x]
      with ω h1 h2
    rw [h1, Pi.sub_apply, toLp_contract, h2, Real.norm_eq_abs, sq_abs]
  have hint : Tendsto (fun n : ℕ =>
      ∫ ω, (max (min (D.toLp x ω) (n : ℝ)) (-(n : ℝ)) - D.toLp x ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun (n : ℕ) ω => (max (min (D.toLp x ω) (n : ℝ)) (-(n : ℝ)) - D.toLp x ω) ^ 2)
      (f := fun _ => (0 : ℝ)) (fun ω => D.toLp x ω ^ 2)
      (fun n => ((((lipschitzWith_trunc n).continuous.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable (D.toLp x))).sub (Lp.aestronglyMeasurable (D.toLp x))).pow 2))
      (Lp.memLp (D.toLp x)).integrable_sq
      (fun n => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact trunc_sub_sq_le n _)
      (ae_of_all _ fun ω => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_trunc_eq (D.toLp x ω)] with n hn
        rw [hn, sub_self]
        simp)
    simpa using h
  have hL : Tendsto (fun n : ℕ => D.toLp (D.contract (lipschitzWith_trunc n)
      (trunc_zero n) x)) atTop (𝓝 (D.toLp x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq := (hint.congr fun n => (key n).symm).sqrt
    simpa using hsq
  have hi : Tendsto (fun n : ℕ => ⟪x, D.contract (lipschitzWith_trunc n)
      (trunc_zero n) x⟫_ℝ) atTop (𝓝 (‖x‖ ^ 2)) := by
    have h := D.tendsto_apply_of_bounded hb hL (InnerProductSpace.toDual ℝ D.Space x)
    simp only [InnerProductSpace.toDual_apply_apply] at h
    rwa [real_inner_self_eq_norm_sq] at h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hup : Tendsto (fun n : ℕ => 2 * ‖x‖ ^ 2 - 2 * ⟪x, D.contract (lipschitzWith_trunc n)
      (trunc_zero n) x⟫_ℝ) atTop (𝓝 0) := by
    have h := (hi.const_mul 2).const_sub (2 * ‖x‖ ^ 2)
    simpa using h
  have hsq : Tendsto (fun n : ℕ => ‖D.contract (lipschitzWith_trunc n)
      (trunc_zero n) x - x‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hup
    rw [norm_sub_sq_real, real_inner_comm]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hb n) 2
    linarith
  simpa using hsq.sqrt

end Truncation

end ErrorCalculus.Capacity.DirichletForm
