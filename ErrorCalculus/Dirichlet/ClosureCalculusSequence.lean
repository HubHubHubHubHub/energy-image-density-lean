import ErrorCalculus.Dirichlet.ClosureCalculusBounds
import ErrorCalculus.Dirichlet.ExtensionLp
import ErrorCalculus.Dirichlet.ExtensionGamma

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Splitting a product difference into a class difference and a coefficient difference. -/
theorem boundedMul_difference {p : ℝ≥0∞} (a b : Ω → ℝ) (ha : MemLp a ∞ μ)
    (hb : MemLp b ∞ μ) (f g : Lp ℝ p μ) :
    boundedMul a ha f - boundedMul b hb g =
      boundedMul a ha (f-g) + boundedMul (a-b) (ha.sub hb) g := by
  apply Lp.ext
  filter_upwards [coeFn_boundedMul a ha f, coeFn_boundedMul b hb g,
    coeFn_boundedMul a ha (f-g), coeFn_boundedMul (a-b) (ha.sub hb) g,
    Lp.coeFn_sub f g, Lp.coeFn_sub (boundedMul a ha f) (boundedMul b hb g),
    Lp.coeFn_add (boundedMul a ha (f-g)) (boundedMul (a-b) (ha.sub hb) g)] with ω h1 h2 h3 h4 h5 h6 h7
  simp only [h1, h2, h3, h4, h5, h6, h7, Pi.add_apply, Pi.sub_apply]
  ring

/-- Three-coefficient estimate used for the moving L² weight in (3). -/
theorem boundedMul_coefficient_difference_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a b c : Ω → ℝ) (ha : MemLp a ∞ μ) (hb : MemLp b ∞ μ) (hc : MemLp c ∞ μ)
    (f g : Lp ℝ p μ) {C : ℝ}
    (hCa : ∀ᵐ ω ∂μ, |a ω| ≤ C) (hCb : ∀ᵐ ω ∂μ, |b ω| ≤ C) :
    ‖boundedMul (a-b) (ha.sub hb) f‖ ≤ 2*C*‖f-g‖ +
      ‖boundedMul (a-c) (ha.sub hc) g‖ + ‖boundedMul (b-c) (hb.sub hc) g‖ := by
  have he : boundedMul (a-b) (ha.sub hb) f = boundedMul (a-b) (ha.sub hb) (f-g) +
      (boundedMul (a-c) (ha.sub hc) g - boundedMul (b-c) (hb.sub hc) g) := by
    apply Lp.ext
    filter_upwards [coeFn_boundedMul (a-b) (ha.sub hb) f,
      coeFn_boundedMul (a-b) (ha.sub hb) (f-g), coeFn_boundedMul (a-c) (ha.sub hc) g,
      coeFn_boundedMul (b-c) (hb.sub hc) g, Lp.coeFn_sub f g,
      Lp.coeFn_sub (boundedMul (a-c) (ha.sub hc) g) (boundedMul (b-c) (hb.sub hc) g),
      Lp.coeFn_add (boundedMul (a-b) (ha.sub hb) (f-g))
        (boundedMul (a-c) (ha.sub hc) g - boundedMul (b-c) (hb.sub hc) g)] with ω h1 h2 h3 h4 h5 h6 h7
    simp only [h1, h2, h3, h4, h5, h6, h7, Pi.add_apply, Pi.sub_apply]
    ring
  have hab : ∀ᵐ ω ∂μ, |(a-b) ω| ≤ 2*C := by
    filter_upwards [hCa, hCb] with ω ha hb
    exact (abs_sub _ _).trans (by linarith)
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add (norm_boundedMul_le _ _ _ hab)
    (norm_sub_le _ _)).trans_eq (by ring))

namespace ErrorData
variable [IsProbabilityMeasure μ] (S : ErrorData Ω μ)

/-- L² estimate for differences of two finite chain rules. -/
theorem chain_difference_norm_bound {k : ℕ} (u v : Fin k → S.dom) (w z : S.dom)
    (a b : Fin k → Ω → ℝ) (ha : ∀ i, MemLp (a i) ∞ μ) (hb : ∀ i, MemLp (b i) ∞ μ)
    {C : ℝ} (hCa : ∀ i, ∀ᵐ ω ∂μ, |a i ω| ≤ C)
    (hw : ⇑(S.Γ w (w-z)) =ᵐ[μ] fun ω => ∑ i, a i ω * S.Γ (u i) (w-z) ω)
    (hz : ⇑(S.Γ z (w-z)) =ᵐ[μ] fun ω => ∑ i, b i ω * S.Γ (v i) (w-z) ω) :
    ‖S.sqrtGamma (w-z)‖ ≤ ∑ i, (C * ‖S.sqrtGamma (u i-v i)‖ +
      ‖boundedMul (a i-b i) ((ha i).sub (hb i)) (S.sqrtGamma (v i))‖) := by
  have hnorm (f : Lp ℝ 2 μ) : ‖|f|‖ = ‖f‖ := by
    apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le <;>
      filter_upwards [Lp.coeFn_abs f] with ω hω <;> simp [hω, Real.norm_eq_abs]
  let A i := boundedMul (a i) (ha i) (S.sqrtGamma (u i-v i))
  let B i := boundedMul (a i-b i) ((ha i).sub (hb i)) (S.sqrtGamma (v i))
  have hA i : ⇑|A i| =ᵐ[μ] fun ω => |a i ω| * Real.sqrt (S.Γ (u i-v i) (u i-v i) ω) := by
    filter_upwards [Lp.coeFn_abs (A i), coeFn_boundedMul (a i) (ha i) (S.sqrtGamma (u i-v i)),
      S.coeFn_sqrtGamma (u i-v i)] with ω hab hm hs
    simp only [hab, A, hm, hs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hB i : ⇑|B i| =ᵐ[μ] fun ω => |a i ω-b i ω| * Real.sqrt (S.Γ (v i) (v i) ω) := by
    filter_upwards [Lp.coeFn_abs (B i), coeFn_boundedMul (a i-b i) ((ha i).sub (hb i)) (S.sqrtGamma (v i)),
      S.coeFn_sqrtGamma (v i)] with ω hab hm hs
    simp only [hab, B, hm, hs, Pi.sub_apply, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ ‖(∑ i, |A i|) + ∑ i, |B i|‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [S.coeFn_sqrtGamma (w-z), S.chain_difference_sqrt_sum_bound u v w z a b hw hz,
        Lp.coeFn_add (∑ i, |A i|) (∑ i, |B i|), lp_coeFn_sum Finset.univ (fun i => |A i|),
        lp_coeFn_sum Finset.univ (fun i => |B i|), ae_all_iff.mpr hA, ae_all_iff.mpr hB] with ω hs hbound hadd hsumA hsumB hA hB
      simp only [hs, hadd, Pi.add_apply, hsumA, hsumB, hA, hB, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hbound.trans (le_abs_self _)
    _ ≤ (∑ i, ‖A i‖) + ∑ i, ‖B i‖ := by
      apply (norm_add_le _ _).trans
      simpa only [hnorm] using add_le_add (norm_sum_le Finset.univ (fun i => |A i|))
        (norm_sum_le Finset.univ (fun i => |B i|))
    _ ≤ _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      exact add_le_add (norm_boundedMul_le (a i) (ha i) (S.sqrtGamma (u i-v i)) (hCa i)) (le_refl ‖B i‖)


/-- dominated coefficient convergence makes the composed sequence form-Cauchy. -/
theorem chain_isCauchy {k : ℕ} (u : Fin k → ℕ → S.dom) (w : ℕ → S.dom)
    (a : Fin k → ℕ → Ω → ℝ) (c : Fin k → Ω → ℝ)
    (ha : ∀ i n, MemLp (a i n) ∞ μ) (hc : ∀ i, MemLp (c i) ∞ μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hCa : ∀ i n, ∀ᵐ ω ∂μ, |a i n ω| ≤ C) (hCc : ∀ i, ∀ᵐ ω ∂μ, |c i ω| ≤ C)
    (hat : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun n => a i n ω) atTop (𝓝 (c i ω)))
    (hu : ∀ i, S.energy.IsCauchy (u i))
    (hw : CauchySeq (fun n => (w n : Lp ℝ 2 μ)))
    (hchain : ∀ n v, ⇑(S.Γ (w n) v) =ᵐ[μ] fun ω => ∑ i, a i n ω * S.Γ (u i n) v ω) :
    S.energy.IsCauchy w := by
  choose g hg using fun i => S.exists_sqrtGamma_limit (hu i)
  let e i n := boundedMul (a i n-c i) ((ha i n).sub (hc i)) (g i)
  have he i : Tendsto (e i) atTop (𝓝 0) := by
    apply boundedMul_tendsto_zero_two _ _ _ (C := 2*C) (mul_nonneg (by norm_num) hC)
    · intro n
      filter_upwards [hCa i n, hCc i] with ω h1 h2
      exact (abs_sub _ _).trans (by linarith)
    · filter_upwards [hat i] with ω ht
      have hh := ht.sub_const (c i ω)
      simp only [sub_self] at hh
      exact hh
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hd i : Tendsto (fun n : ℕ × ℕ => ‖S.sqrtGamma (u i n.1-u i n.2)‖) atTop (𝓝 0) := by
    have ht := (cauchySeq_iff_tendsto_dist_atTop_0.mp (hu i).2).const_mul (Real.sqrt 2)
    simp only [mul_zero, dist_eq_norm, ← map_sub, S.energy.norm_j, ← S.norm_sqrtGamma] at ht
    exact ht
  have hupper : Tendsto (fun n : ℕ × ℕ => ∑ i,
      (C * ‖S.sqrtGamma (u i n.1-u i n.2)‖ +
        (2*C*‖S.sqrtGamma (u i n.2)-g i‖ + ‖e i n.1‖ + ‖e i n.2‖))) atTop (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ (fun i _ =>
      ((hd i).const_mul C).add
        ((((tendsto_iff_norm_sub_tendsto_zero.mp (hg i).2).comp hsnd).const_mul (2*C)).add
          ((he i).norm.comp hfst) |>.add ((he i).norm.comp hsnd)))
    simp only [mul_zero, norm_zero, add_zero, Finset.sum_const_zero] at hh
    exact hh
  have hroot : Tendsto (fun n : ℕ × ℕ => ‖S.sqrtGamma (w n.1-w n.2)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) _ hupper
    intro n
    apply (S.chain_difference_norm_bound (fun i => u i n.1) (fun i => u i n.2)
      (w n.1) (w n.2) (fun i => a i n.1) (fun i => a i n.2)
      (fun i => ha i n.1) (fun i => ha i n.2) (fun i => hCa i n.1)
      (hchain n.1 _) (hchain n.2 _)).trans
    apply Finset.sum_le_sum
    intro i _
    exact add_le_add le_rfl (boundedMul_coefficient_difference_le (a i n.1) (a i n.2) (c i)
      (ha i n.1) (ha i n.2) (hc i) (S.sqrtGamma (u i n.2)) (g i) (hCa i n.1) (hCa i n.2))
  refine ⟨hw, cauchySeq_iff_tendsto_dist_atTop_0.mpr ?_⟩
  apply squeeze_zero (fun _ => dist_nonneg) _ hroot
  intro n
  rw [dist_eq_norm, ← map_sub, S.energy.norm_j, S.norm_sqrtGamma]
  exact le_mul_of_one_le_left (Real.sqrt_nonneg _) (by norm_num)

end ErrorData
end ErrorCalculus
