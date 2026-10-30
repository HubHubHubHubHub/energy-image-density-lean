import ErrorCalculus.Dirichlet.ExtensionGammaBounds

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorData
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorData Ω μ)

/-- Bilinearity on representatives, with the null sets made explicit. -/
theorem gamma_sub_left_ae (u v z : S.dom) :
    ⇑(S.Γ (u-v) z) =ᵐ[μ] fun ω => S.Γ u z ω - S.Γ v z ω := by
  rw [map_sub, LinearMap.sub_apply]
  exact Lp.coeFn_sub _ _

/-- The scalar cancellation in (3), including the zero square-root case. -/
theorem sqrt_le_of_le_mul_sqrt {x b : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b)
    (h : x ≤ b * Real.sqrt x) : Real.sqrt x ≤ b := by
  by_cases hz : Real.sqrt x = 0
  · simpa only [hz] using hb
  · have hp : 0 < Real.sqrt x := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith [Real.sq_sqrt hx]

/-- Pointwise chain-rule control for a single finite sum. -/
theorem chain_sqrt_bound {k : ℕ} (u : Fin k → S.dom) (w : S.dom) (a : Fin k → Ω → ℝ)
    (hw : ⇑(S.Γ w w) =ᵐ[μ] fun ω => ∑ i, a i ω * S.Γ (u i) w ω) :
    ∀ᵐ ω ∂μ, Real.sqrt (S.Γ w w ω) ≤
      ∑ i, |a i ω| * Real.sqrt (S.Γ (u i) (u i) ω) := by
  filter_upwards [hw, S.gamma_sum_abs_le u w a, S.Γ_nonneg w] with ω he hb hp
  apply sqrt_le_of_le_mul_sqrt hp (Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
  nth_rw 1 [he]
  exact (le_abs_self _).trans hb

/-- expansion of the difference of two chain-rule identities. -/
theorem chain_difference_identity {k : ℕ} (u v : Fin k → S.dom) (w z : S.dom)
    (a b : Fin k → Ω → ℝ)
    (hw : ⇑(S.Γ w (w-z)) =ᵐ[μ] fun ω => ∑ i, a i ω * S.Γ (u i) (w-z) ω)
    (hz : ⇑(S.Γ z (w-z)) =ᵐ[μ] fun ω => ∑ i, b i ω * S.Γ (v i) (w-z) ω) :
    ⇑(S.Γ (w-z) (w-z)) =ᵐ[μ] fun ω =>
      (∑ i, a i ω * S.Γ (u i-v i) (w-z) ω) +
      ∑ i, (a i ω-b i ω) * S.Γ (v i) (w-z) ω := by
  filter_upwards [hw, hz, S.gamma_sub_left_ae w z (w-z),
    ae_all_iff.mpr (fun i => S.gamma_sub_left_ae (u i) (v i) (w-z))] with ω hw hz hd hi
  rw [hd, hw, hz, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hi i]
  ring

/-- The sharp Euclidean estimate from CS_k; no matrix positivity is used. -/
theorem chain_difference_sqrt_bound {k : ℕ} (u v : Fin k → S.dom) (w z : S.dom)
    (a b : Fin k → Ω → ℝ)
    (hw : ⇑(S.Γ w (w-z)) =ᵐ[μ] fun ω => ∑ i, a i ω * S.Γ (u i) (w-z) ω)
    (hz : ⇑(S.Γ z (w-z)) =ᵐ[μ] fun ω => ∑ i, b i ω * S.Γ (v i) (w-z) ω) :
    ∀ᵐ ω ∂μ, Real.sqrt (S.Γ (w-z) (w-z) ω) ≤
      Real.sqrt (∑ i, (a i ω)^2) * Real.sqrt (∑ i, S.Γ (u i-v i) (u i-v i) ω) +
      Real.sqrt (∑ i, (a i ω-b i ω)^2) * Real.sqrt (∑ i, S.Γ (v i) (v i) ω) := by
  filter_upwards [S.chain_difference_identity u v w z a b hw hz,
    S.gamma_sum_cauchy_schwarz (fun i => u i-v i) (w-z) a,
    S.gamma_sum_cauchy_schwarz v (w-z) (fun i ω => a i ω-b i ω),
    S.Γ_nonneg (w-z)] with ω he h1 h2 hp
  apply sqrt_le_of_le_mul_sqrt hp (by positivity)
  nth_rw 1 [he]
  rw [add_mul]
  exact add_le_add ((le_abs_self _).trans h1) ((le_abs_self _).trans h2)

/-- Coordinate version, convenient for L² norm estimates. -/
theorem chain_difference_sqrt_sum_bound {k : ℕ} (u v : Fin k → S.dom) (w z : S.dom)
    (a b : Fin k → Ω → ℝ)
    (hw : ⇑(S.Γ w (w-z)) =ᵐ[μ] fun ω => ∑ i, a i ω * S.Γ (u i) (w-z) ω)
    (hz : ⇑(S.Γ z (w-z)) =ᵐ[μ] fun ω => ∑ i, b i ω * S.Γ (v i) (w-z) ω) :
    ∀ᵐ ω ∂μ, Real.sqrt (S.Γ (w-z) (w-z) ω) ≤
      (∑ i, |a i ω| * Real.sqrt (S.Γ (u i-v i) (u i-v i) ω)) +
      ∑ i, |a i ω-b i ω| * Real.sqrt (S.Γ (v i) (v i) ω) := by
  filter_upwards [S.chain_difference_identity u v w z a b hw hz,
    S.gamma_sum_abs_le (fun i => u i-v i) (w-z) a,
    S.gamma_sum_abs_le v (w-z) (fun i ω => a i ω-b i ω), S.Γ_nonneg (w-z)] with ω he h1 h2 hp
  apply sqrt_le_of_le_mul_sqrt hp
    (add_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      (Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)))
  nth_rw 1 [he]
  rw [add_mul]
  exact add_le_add ((le_abs_self _).trans h1) ((le_abs_self _).trans h2)

end ErrorCalculus.ErrorData
