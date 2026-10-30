import ErrorCalculus.Dirichlet.ClosureCalculusSequence

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A finite Lipschitz composition respects L² convergence of its coordinates. -/
theorem composition_norm_sub_le {k : ℕ} (u v : Fin k → Lp ℝ 2 μ)
    {F : (Fin k → ℝ) → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (w z : Lp ℝ 2 μ)
    (hw : ⇑w =ᵐ[μ] fun ω => F (fun i => u i ω))
    (hz : ⇑z =ᵐ[μ] fun ω => F (fun i => v i ω)) :
    ‖w-z‖ ≤ L * ∑ i, ‖u i-v i‖ := by
  have hg : ⇑(∑ i, |u i-v i|) =ᵐ[μ] fun ω => ∑ i, |u i ω-v i ω| := by
    filter_upwards [lp_coeFn_sum Finset.univ (fun i => |u i-v i|),
      ae_all_iff.mpr (fun i => Lp.coeFn_abs (u i-v i)),
      ae_all_iff.mpr (fun i => Lp.coeFn_sub (u i) (v i))] with ω hs ha hd
    simp only [hs, ha, hd, Pi.sub_apply]
  have he : ‖w-z‖ ≤ L * ‖∑ i, |u i-v i|‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hw, hz, Lp.coeFn_sub w z, hg] with ω hw hz hd hg
    have hsum : 0 ≤ ∑ i, |u i ω-v i ω| := Finset.sum_nonneg fun i _ => abs_nonneg _
    simp only [hd, Pi.sub_apply, hw, hz, hg, Real.norm_eq_abs, abs_of_nonneg hsum]
    apply (hF.dist_le_mul (fun i => u i ω) (fun i => v i ω)).trans
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).mpr
    intro i
    exact Finset.single_le_sum (fun j _ => abs_nonneg (u j ω-v j ω)) (Finset.mem_univ i)
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
  simpa only [norm_abs_eq_norm] using norm_sum_le Finset.univ (fun i => |u i-v i|)

theorem composition_tendsto {k : ℕ} (u : Fin k → ℕ → Lp ℝ 2 μ) (v : Fin k → Lp ℝ 2 μ)
    {F : (Fin k → ℝ) → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (w : ℕ → Lp ℝ 2 μ) (z : Lp ℝ 2 μ)
    (hw : ∀ n, ⇑(w n) =ᵐ[μ] fun ω => F (fun i => u i n ω))
    (hz : ⇑z =ᵐ[μ] fun ω => F (fun i => v i ω))
    (hu : ∀ i, Tendsto (u i) atTop (𝓝 (v i))) : Tendsto w atTop (𝓝 z) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (tendsto_finsetSum Finset.univ
    (fun i _ => tendsto_iff_norm_sub_tendsto_zero.mp (hu i))).const_mul (L:ℝ)
  simp only [Finset.sum_const_zero, mul_zero] at ht
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => composition_norm_sub_le (fun i => u i n) v hF (w n) z (hw n) hz) ht

/-- Uniform bound for each derivative coefficient in the finite-coordinate convention. -/
theorem fderiv_coefficient_bound {k : ℕ} {F : (Fin k → ℝ) → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L F) (x : Fin k → ℝ) (i : Fin k) :
    |fderiv ℝ F x (Pi.single i 1)| ≤ L := by
  have h := (fderiv ℝ F x).le_opNorm (Pi.single i 1)
  have hn := norm_fderiv_le_of_lipschitz ℝ hL (x₀ := x)
  have hs : ‖(Pi.single i 1 : Fin k → ℝ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  simpa only [Real.norm_eq_abs, mul_one] using h.trans
    (mul_le_mul hn hs (norm_nonneg _) L.coe_nonneg)

/-- Derivative coefficients evaluated at an L² tuple are essentially bounded. -/
theorem fderiv_coefficient_memLp {k : ℕ} (u : Fin k → Lp ℝ 2 μ)
    {F : (Fin k → ℝ) → ℝ} {L : ℝ≥0} (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) (i : Fin k) :
    MemLp (fun ω => fderiv ℝ F (fun j => u j ω) (Pi.single i 1)) ∞ μ := by
  have ht : Continuous (fun x => fderiv ℝ F x (Pi.single i 1)) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  apply memLp_top_of_bound (ht.comp_aestronglyMeasurable (MemLp.of_eval (fun j => Lp.memLp (u j))).1) (L:ℝ)
  exact ae_of_all _ (fun ω => fderiv_coefficient_bound hL _ i)

/-- bounded a.e.-convergent coefficients can multiply strongly convergent L¹ classes. -/
theorem boundedMul_tendsto_one (a : ℕ → Ω → ℝ) (c : Ω → ℝ)
    (ha : ∀ n, MemLp (a n) ∞ μ) (hc : MemLp c ∞ μ)
    (f : ℕ → Lp ℝ 1 μ) (g : Lp ℝ 1 μ) {C : ℝ}
    (hCa : ∀ n, ∀ᵐ ω ∂μ, |a n ω| ≤ C) (hCc : ∀ᵐ ω ∂μ, |c ω| ≤ C)
    (hat : ∀ᵐ ω ∂μ, Tendsto (fun n => a n ω) atTop (𝓝 (c ω)))
    (hfg : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => boundedMul (a n) (ha n) (f n)) atTop (𝓝 (boundedMul c hc g)) := by
  have he : Tendsto (fun n => boundedMul (a n-c) ((ha n).sub hc) g) atTop (𝓝 0) := by
    apply boundedMul_tendsto_zero_one (C := 2*C)
    · intro n
      filter_upwards [hCa n, hCc] with ω h1 h2
      exact (abs_sub _ _).trans (by linarith)
    · filter_upwards [hat] with ω ht
      have hh := ht.sub_const (c ω)
      simp only [sub_self] at hh
      exact hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := ((tendsto_iff_norm_sub_tendsto_zero.mp hfg).const_mul C).add he.norm
  simp only [mul_zero, norm_zero, add_zero] at ht
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro n
  rw [boundedMul_difference]
  exact (norm_add_le _ _).trans (add_le_add (norm_boundedMul_le (a n) (ha n) (f n-g) (hCa n)) le_rfl)

end ErrorCalculus
