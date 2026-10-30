import ErrorCalculus.Dirichlet.WienerIBP

noncomputable section
open MeasureTheory Filter Topology

namespace ErrorCalculus

/-- Compact smooth cylindrical tests above any fixed coordinate are total in L². -/
theorem cylTests_total (i : ℕ) (w : Lp ℝ 2 wienerCoord)
    (hw : ∀ K, i < K → ∀ (ψ : (Fin K → ℝ) → ℝ) (hψ : ContDiff ℝ 1 ψ)
      (hc : HasCompactSupport ψ), inner ℝ w (wienerTest ψ hψ hc) = 0) : w = 0 := by
  have hK (K : ℕ) (hi : i < K) (v : Lp ℝ 2 (densityMeasureD (ouDensityD K))) :
      inner ℝ w (cylLp K 2 v) = 0 := by
    have hd := Lp.dense_hasCompactSupport_contDiff (μ := densityMeasureD (ouDensityD K))
      (E := Fin K → ℝ) (F := ℝ) (p := 2) (by norm_num)
    have hclosed : IsClosed {v : Lp ℝ 2 (densityMeasureD (ouDensityD K)) |
        inner ℝ w (cylLp K 2 v) = 0} :=
      isClosed_eq (continuous_const.inner (cylLp K 2).continuous) continuous_const
    apply closure_minimal (t := {v | inner ℝ w (cylLp K 2 v) = 0}) ?_ hclosed (hd v)
    rintro v ⟨ψ, hv, hc, hψ⟩
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have he : (protoOfFunctionD (ouDensityD K) ψ
        (isC1Bounded_of_hasCompactSupportD hψ1 hc) : Lp ℝ 2 _) = v :=
      Lp.ext (((isC1Bounded_of_hasCompactSupportD hψ1 hc).memLp _ 2).coeFn_toLp.trans hv.symm)
    rw [← he]
    exact hw K hi ψ hψ1 hc
  apply cylinder_dense.eq_zero_of_inner_left ℝ
  intro v hv
  obtain ⟨K, u, rfl⟩ := Set.mem_iUnion.mp hv
  rw [← cylLp_comp (le_max_left K (i+1)) 2]
  exact hK (max K (i+1)) (lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_right _ _)) _

/-- The energy Cauchy property controls each coordinate derivative. -/
theorem cauchySeq_wienerPartial (i : ℕ) {F : ℕ → wienerDom}
    (hF : wienerProto.energy.IsCauchy F) : CauchySeq (fun n => wienerPartial i (F n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := (wienerProto.energy.isCauchy_iff F).mp hF |>.2 (ε/2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm, ← map_sub]
  calc
    _ ≤ 2 * wienerProto.energy.seminorm (F m - F n) := wienerPartial_norm_le i _
    _ < 2 * (ε/2) := mul_lt_mul_of_pos_left (hN m hm n hn) (by norm_num)
    _ = ε := by ring

/-- IBP identifies every possible derivative limit with zero. -/
theorem wienerPartial_limit_zero (i : ℕ) {F : ℕ → wienerDom} {w : Lp ℝ 2 wienerCoord}
    (hF : Tendsto (fun n => (F n : Lp ℝ 2 wienerCoord)) atTop (𝓝 0))
    (hw : Tendsto (fun n => wienerPartial i (F n)) atTop (𝓝 w)) : w = 0 := by
  apply cylTests_total i w
  intro K hi ψ hψ hc
  have hl := hw.inner (𝕜 := ℝ) (tendsto_const_nhds (x := wienerTest ψ hψ hc))
  have hr := (hF.inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := cylLp K 2 (testChiLpD (ouDensityD K) ⟨i,hi⟩ ψ hψ hc)))).neg
  simp only [inner_zero_left, neg_zero] at hr
  have he : (fun n => inner ℝ (wienerPartial i (F n)) (wienerTest ψ hψ hc)) =
      fun n => - inner ℝ (F n : Lp ℝ 2 wienerCoord)
        (cylLp K 2 (testChiLpD (ouDensityD K) ⟨i,hi⟩ ψ hψ hc)) := by
    funext n
    exact inner_wienerPartial_test (F n) ⟨i,hi⟩ hψ hc
  rw [← he] at hr
  exact tendsto_nhds_unique hl hr

theorem tendsto_wienerPartial_zero (i : ℕ) {F : ℕ → wienerDom}
    (hF : wienerProto.energy.IsCauchy F)
    (h0 : Tendsto (fun n => (F n : Lp ℝ 2 wienerCoord)) atTop (𝓝 0)) :
    Tendsto (fun n => wienerPartial i (F n)) atTop (𝓝 0) := by
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (cauchySeq_wienerPartial i hF)
  rwa [wienerPartial_limit_zero i h0 hw] at hw

/-- Every fixed finite-coordinate energy tends to zero. -/
theorem tendsto_partialEnergy_zero {F : ℕ → wienerDom}
    (h : ∀ i, Tendsto (fun n => wienerPartial i (F n)) atTop (𝓝 0)) (K : ℕ) :
    Tendsto (fun n => partialEnergy K (F n)) atTop (𝓝 0) := by
  have hs := tendsto_finsetSum (Finset.range K) (fun i _ => (h i).norm.pow 2)
  simpa [partialEnergy] using hs.const_mul (1/2:ℝ)

/-- The finite-support tail argument, separate from the integration-by-parts step. -/
theorem wienerEnergy_tendsto_zero_of_partials {F : ℕ → wienerDom}
    (hF : wienerProto.energy.IsCauchy F)
    (h : ∀ i, Tendsto (fun n => wienerPartial i (F n)) atTop (𝓝 0)) :
    Tendsto (fun n => wienerProto.energy.E (F n) (F n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have he : 0 < ε/2 := by positivity
  obtain ⟨N, hN⟩ := (wienerProto.energy.isCauchy_iff F).mp hF |>.2
    (Real.sqrt (ε/2)) (Real.sqrt_pos.mpr he)
  let K := level (F N)
  have hp := (tendsto_partialEnergy_zero h K).eventually (gt_mem_nhds he)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hp
  refine ⟨max N M, fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (le_max_right _ _).trans hn
  have hs := sqrt_tail_sub_le K (F n) (F N)
  rw [tail_eq_zero_of_level (F N) (le_refl _), Real.sqrt_zero, add_zero] at hs
  have ht : Real.sqrt (tail K (F n)) < Real.sqrt (ε/2) :=
    lt_of_le_of_lt hs (hN n hnN N le_rfl)
  have ht' : tail K (F n) < ε/2 := (Real.sqrt_lt_sqrt_iff (tail_nonneg K (F n))).mp ht
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (wienerProto.energy.nonneg (F n))]
  have hm := hM n hnM
  change wienerProto.energy.E (F n) (F n) - partialEnergy K (F n) < ε/2 at ht'
  linarith

/-- closability of the cylindrical Wiener-coordinate Ornstein–Uhlenbeck form. -/
theorem wienerProto_isClosable : wienerProto.energy.IsClosable := by
  intro F hF h0
  exact wienerEnergy_tendsto_zero_of_partials hF (fun i => tendsto_wienerPartial_zero i hF h0)

end ErrorCalculus
