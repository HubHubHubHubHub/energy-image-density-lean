import ErrorCalculus.Dirichlet.WienerStructure
import ErrorCalculus.Dirichlet.DensityDCoordinates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ErrorCalculus

/-- Bounded smooth approximants to the identity, with derivative bounded by one. -/
def wienerCut (n : ℕ) (x : ℝ) : ℝ := (n+1:ℝ) * Real.sin (x/(n+1:ℝ))

theorem wienerCut_deriv (n : ℕ) (x : ℝ) : deriv (wienerCut n) x = Real.cos (x/(n+1:ℝ)) := by
  have hn : (n+1:ℝ) ≠ 0 := by positivity
  have h := (((hasDerivAt_id x).div_const (n+1:ℝ)).sin).const_mul (n+1:ℝ)
  change deriv (fun y => (n+1:ℝ) * Real.sin (id y/(n+1:ℝ))) x = _
  rw [h.deriv]
  dsimp only [id_eq]
  field_simp

theorem wienerCut_bounded (n : ℕ) : IsC1Bounded (wienerCut n) := by
  refine ⟨by unfold wienerCut; fun_prop, ⟨n+1, fun x => ?_⟩, ⟨1, fun x => ?_⟩⟩
  · dsimp [wienerCut]
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < n+1)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)).trans_eq (mul_one _)
  · rw [wienerCut_deriv, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _

theorem wienerCut_abs_le (n : ℕ) (x : ℝ) : |wienerCut n x| ≤ |x| := by
  have hn : (0:ℝ) < n+1 := by positivity
  dsimp [wienerCut]
  rw [abs_mul, abs_of_pos hn]
  calc
    _ ≤ (n+1:ℝ) * |x/(n+1:ℝ)| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs hn.le
    _ = |x| := by rw [abs_div, abs_of_pos hn]; field_simp

theorem wienerCut_tendsto (x : ℝ) : Tendsto (fun n => wienerCut n x) atTop (𝓝 x) := by
  have ht : Tendsto (fun n : ℕ => x/(n+1:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  have h := (tendsto_const_nhds (x := x)).mul (Real.continuous_sinc.continuousAt.tendsto.comp ht)
  simp only [Real.sinc_zero, mul_one] at h
  convert h using 1
  funext n
  simp only [Function.comp_apply]
  by_cases hx : x = 0
  · simp [hx, wienerCut]
  · rw [Real.sinc_of_ne_zero (div_ne_zero hx (by positivity))]
    unfold wienerCut
    field_simp

theorem wienerCos_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => Real.cos (x/(n+1:ℝ))) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => x/(n+1:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  simpa only [Function.comp_def, Real.cos_zero] using Real.continuous_cos.continuousAt.tendsto.comp ht

theorem wienerCoordinate_memLp (i : ℕ) : MemLp (fun x : ℕ → ℝ => x i) 2 wienerCoord :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) i)

/-- The i-th Gaussian coordinate, as an actual L² class. -/
def wienerCoordinate (i : ℕ) : Lp ℝ 2 wienerCoord := (wienerCoordinate_memLp i).toLp _

theorem coeFn_wienerCoordinate (i : ℕ) :
    ⇑(wienerCoordinate i) =ᵐ[wienerCoord] fun x => x i := (wienerCoordinate_memLp i).coeFn_toLp

/-- A cylindrical approximant at the explicit level i+1. -/
def wienerApprox (i n : ℕ) : wienerDom :=
  cylProto (i+1) (protoOfFunctionD _ (fun x => wienerCut n (x ⟨i, Nat.lt_succ_self i⟩))
    ((wienerCut_bounded n).coordinateD ⟨i, Nat.lt_succ_self i⟩))

theorem coeFn_wienerApprox (i n : ℕ) :
    ⇑(wienerApprox i n : Lp ℝ 2 wienerCoord) =ᵐ[wienerCoord] fun x => wienerCut n (x i) :=
  (coeFn_cylLp (i+1) 2 _).trans ((restrictN_preserving (i+1)).quasiMeasurePreserving.ae_eq_comp
    (((wienerCut_bounded n).coordinateD ⟨i, Nat.lt_succ_self i⟩).memLp _ 2).coeFn_toLp)

/-- Dominated convergence of the values uses the integrable Gaussian coordinate. -/
theorem wienerApprox_tendsto (i : ℕ) :
    Tendsto (fun n => (wienerApprox i n : Lp ℝ 2 wienerCoord)) atTop (𝓝 (wienerCoordinate i)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply lp_two_tendsto_zero_of_dominated _ ((2:ℝ) • wienerCoordinate i)
  · intro n
    filter_upwards [Lp.coeFn_sub (wienerApprox i n : Lp ℝ 2 wienerCoord) (wienerCoordinate i),
      coeFn_wienerApprox i n, coeFn_wienerCoordinate i, Lp.coeFn_smul (2:ℝ) (wienerCoordinate i)]
      with x hd hf hg hs
    simp only [hd, hf, hg, hs, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact (abs_sub _ _).trans (by linarith [wienerCut_abs_le n (x i)])
  · filter_upwards [ae_all_iff.mpr (fun n : ℕ => Lp.coeFn_sub
      (wienerApprox i n : Lp ℝ 2 wienerCoord) (wienerCoordinate i)),
      ae_all_iff.mpr (coeFn_wienerApprox i), coeFn_wienerCoordinate i] with x hd hf hg
    simp only [hd, hf, hg, Pi.sub_apply]
    simpa using (wienerCut_tendsto (x i)).sub_const (x i)

/-- The bounded derivative class of the approximant. -/
def wienerCos (i n : ℕ) : Lp ℝ 2 wienerCoord :=
  (MemLp.of_bound ((Real.continuous_cos.comp (continuous_apply i |>.div_const (n+1:ℝ))).aestronglyMeasurable)
    1 (ae_of_all _ fun _ => Real.abs_cos_le_one _)).toLp _

theorem coeFn_wienerCos (i n : ℕ) :
    ⇑(wienerCos i n) =ᵐ[wienerCoord] fun x => Real.cos (x i/(n+1:ℝ)) := MemLp.coeFn_toLp _

theorem wienerCos_tendsto_Lp (i : ℕ) :
    Tendsto (wienerCos i) atTop (𝓝 (Lp.const 2 wienerCoord 1)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply lp_two_tendsto_zero_of_dominated _ (Lp.const 2 wienerCoord 2)
  · intro n
    filter_upwards [Lp.coeFn_sub (wienerCos i n) (Lp.const 2 wienerCoord 1), coeFn_wienerCos i n,
      Lp.coeFn_const 2 wienerCoord (1:ℝ), Lp.coeFn_const 2 wienerCoord (2:ℝ)] with x hd hf h1 h2
    simp only [hd, hf, h1, h2, Pi.sub_apply, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), Function.const_apply]
    exact (abs_sub _ _).trans (by simpa only [abs_one] using (show |Real.cos (x i/(n+1:ℝ))| + 1 ≤ 2 by linarith [Real.abs_cos_le_one (x i/(n+1:ℝ))]))
  · filter_upwards [ae_all_iff.mpr (fun n => Lp.coeFn_sub (wienerCos i n) (Lp.const 2 wienerCoord 1)),
      ae_all_iff.mpr (coeFn_wienerCos i), Lp.coeFn_const 2 wienerCoord (1:ℝ)] with x hd hf h1
    simp only [hd, hf, h1, Pi.sub_apply]
    simpa using (wienerCos_tendsto (x i)).sub_const 1

/-- All partials of a coordinate approximant, including indices outside its level. -/
theorem wienerPartial_approx (i n k : ℕ) :
    wienerPartial k (wienerApprox i n) = if k = i then wienerCos i n else 0 := by
  classical
  by_cases hk : k < i+1
  · rw [wienerApprox, wienerPartial_cyl (⟨k,hk⟩ : Fin (i+1))]
    apply Lp.ext
    have hg := coeFn_gradD (ouDensityD (i+1)) ⟨k,hk⟩
      (protoOfFunctionD _ _ ((wienerCut_bounded n).coordinateD ⟨i, Nat.lt_succ_self i⟩))
    filter_upwards [coeFn_cylLp (i+1) 2 _,
      (restrictN_preserving (i+1)).quasiMeasurePreserving.ae_eq_comp hg,
      coeFn_wienerCos i n, Lp.coeFn_zero ℝ 2 wienerCoord] with x hc hg hcos hz
    rw [hc, hg]
    change fderiv ℝ (repD _ _) _ _ = _
    rw [rep_protoOfFunctionD, fderiv_coordinateD (wienerCut_bounded n).differentiable, wienerCut_deriv]
    by_cases he : k = i
    · subst k
      simp [hcos, restrictN]
    · simp [he, Fin.ext_iff, Ne.symm he]
  · rw [wienerApprox, wienerPartial_cyl_ge (Nat.le_of_not_gt hk)]
    have he : k ≠ i := by omega
    simp [he]

/-- Energy differences of coordinate approximants have only one nonzero partial. -/
theorem wienerApprox_energy_sub (i n m : ℕ) :
    wienerProto.energy.E (wienerApprox i n - wienerApprox i m) (wienerApprox i n - wienerApprox i m) =
      (1/2:ℝ) * ‖wienerCos i n - wienerCos i m‖^2 := by
  classical
  have he := wienerEnergy_cyl_eq_sum (i+1)
    (protoOfFunctionD _ _ ((wienerCut_bounded n).coordinateD ⟨i, Nat.lt_succ_self i⟩) -
     protoOfFunctionD _ _ ((wienerCut_bounded m).coordinateD ⟨i, Nat.lt_succ_self i⟩))
  simp only [map_sub] at he
  change wienerProto.energy.E (wienerApprox i n - wienerApprox i m) (wienerApprox i n - wienerApprox i m) =
    (1/2:ℝ) * ∑ k ∈ Finset.range (i+1), ‖wienerPartial k (wienerApprox i n) - wienerPartial k (wienerApprox i m)‖^2 at he
  calc
    _ = _ := he
    _ = _ := by
      congr 1
      simp only [wienerPartial_approx]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        simp [hk]
      · simp

/-- The approximants are Cauchy for the form norm. -/
theorem wienerApprox_isCauchy (i : ℕ) : wienerProto.energy.IsCauchy (wienerApprox i) := by
  rw [wienerProto.energy.isCauchy_iff]
  refine ⟨(wienerApprox_tendsto i).cauchySeq, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (wienerCos_tendsto_Lp i).cauchySeq ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  have hd := hN m hm n hn
  rw [dist_eq_norm] at hd
  change Real.sqrt (wienerProto.energy.E (wienerApprox i m - wienerApprox i n)
    (wienerApprox i m - wienerApprox i n)) < ε
  rw [wienerApprox_energy_sub]
  apply lt_of_le_of_lt _ hd
  calc
    _ ≤ Real.sqrt (‖wienerCos i m - wienerCos i n‖^2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖wienerCos i m - wienerCos i n‖])
    _ = _ := Real.sqrt_sq (norm_nonneg _)

/-- Every Gaussian coordinate belongs to the closed Wiener domain. -/
theorem wienerCoordinate_mem (i : ℕ) : wienerCoordinate i ∈ wienerStructure.dom :=
  (wienerProto.energy.mem_closureDom_iff _).mpr
    ⟨wienerApprox i, wienerApprox_isCauchy i, wienerApprox_tendsto i⟩

/-- Coordinates as elements of the closed domain. -/
def wienerX (i : ℕ) : wienerStructure.dom := ⟨wienerCoordinate i, wienerCoordinate_mem i⟩

/-- Mixed finite-coordinate Γ identity, used to identify the coordinate cross terms. -/
theorem wienerGamma_eq_sum_partial_mul (N : ℕ) (u v : protoDomD (ouDensityD N)) :
    ⇑(wienerGamma (cylProto N u) (cylProto N v)) =ᵐ[wienerCoord]
      fun x => ∑ k : Fin N, wienerPartial k.val (cylProto N u) x *
        wienerPartial k.val (cylProto N v) x := by
  rw [wienerGamma_cyl]
  have hp (u : protoDomD (ouDensityD N)) : ∀ᵐ x ∂wienerCoord, ∀ k : Fin N,
      wienerPartial k.val (cylProto N u) x = partialRep _ k u (restrictN N x) := by
    apply ae_all_iff.mpr
    intro k
    rw [wienerPartial_cyl]
    exact (coeFn_cylLp N 2 _).trans
      ((restrictN_preserving N).quasiMeasurePreserving.ae_eq_comp (coeFn_gradD _ k u))
  filter_upwards [coeFn_cylLp N 1 (gammaD _ u v),
    (restrictN_preserving N).quasiMeasurePreserving.ae (coeFn_gammaD _ u v), hp u, hp v]
    with x ha hb hu hv
  rw [ha, Function.comp_apply, hb]
  apply Finset.sum_congr rfl
  intro k _
  rw [hu k, hv k]
  rfl

theorem coeFn_wienerPartial_approx (i n k : ℕ) :
    ⇑(wienerPartial k (wienerApprox i n)) =ᵐ[wienerCoord]
      fun x => if k = i then Real.cos (x i/(n+1:ℝ)) else 0 := by
  rw [wienerPartial_approx]
  split_ifs
  · exact coeFn_wienerCos i n
  · exact Lp.coeFn_zero ℝ 2 wienerCoord

/-- The mixed error of the bounded approximants. -/
theorem wienerApprox_gamma (i j n : ℕ) :
    ⇑(wienerProto.Γ (wienerApprox i n) (wienerApprox j n)) =ᵐ[wienerCoord]
      fun x => if i = j then Real.cos (x i/(n+1:ℝ)) * Real.cos (x j/(n+1:ℝ)) else 0 := by
  classical
  obtain ⟨N, hN, u, hu⟩ := exists_common_level_above ![wienerApprox i n, wienerApprox j n]
    (max (i+1) (j+1))
  have hi : i < N := lt_of_lt_of_le (Nat.lt_succ_self i) ((le_max_left _ _).trans hN)
  have hu0 : cylProto N (u 0) = wienerApprox i n := hu 0
  have hu1 : cylProto N (u 1) = wienerApprox j n := hu 1
  have hg := wienerGamma_eq_sum_partial_mul N (u 0) (u 1)
  rw [hu0, hu1] at hg
  filter_upwards [hg, ae_all_iff.mpr (fun k : Fin N => coeFn_wienerPartial_approx i n k.val),
    ae_all_iff.mpr (fun k : Fin N => coeFn_wienerPartial_approx j n k.val)] with x hx hxi hxj
  change wienerGamma _ _ x = _
  rw [hx]
  simp only [hxi, hxj]
  rw [Finset.sum_eq_single (⟨i,hi⟩ : Fin N)]
  · simp
  · intro k _ hk
    have hki : k.val ≠ i := fun h => hk (Fin.ext h)
    simp [hki]
  · simp

/-- The Γ approximants converge in L¹ to the Kronecker constant. -/
theorem wienerApprox_gamma_tendsto (i j : ℕ) :
    Tendsto (fun n => wienerProto.Γ (wienerApprox i n) (wienerApprox j n)) atTop
      (𝓝 (Lp.const 1 wienerCoord (if i = j then 1 else 0))) := by
  classical
  let a (n : ℕ) (x : ℕ → ℝ) : ℝ :=
    if i = j then Real.cos (x i/(n+1:ℝ)) * Real.cos (x j/(n+1:ℝ)) else 0
  let c : (ℕ → ℝ) → ℝ := fun _ => if i = j then 1 else 0
  have hba (n : ℕ) (x : ℕ → ℝ) : |a n x| ≤ 1 := by
    dsimp [a]
    split_ifs
    · rw [abs_mul]
      exact (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans_eq (mul_one _)
    · norm_num
  have hbc (x : ℕ → ℝ) : |c x| ≤ 1 := by dsimp [c]; split_ifs <;> norm_num
  have ha (n : ℕ) : MemLp (a n) ∞ wienerCoord := by
    apply memLp_top_of_bound (C := 1) ?_ (ae_of_all _ (hba n))
    have hm : Continuous (a n) := by dsimp [a]; split_ifs <;> fun_prop
    exact hm.aestronglyMeasurable
  have hc : MemLp c ∞ wienerCoord := memLp_const _
  have he : ∀ n, wienerProto.Γ (wienerApprox i n) (wienerApprox j n) -
      Lp.const 1 wienerCoord (if i = j then 1 else 0) =
      boundedMul (a n-c) ((ha n).sub hc) (Lp.const 1 wienerCoord 1) := by
    intro n
    apply Lp.ext
    filter_upwards [wienerApprox_gamma i j n,
      Lp.coeFn_sub (wienerProto.Γ (wienerApprox i n) (wienerApprox j n))
        (Lp.const 1 wienerCoord (if i = j then 1 else 0)),
      Lp.coeFn_const 1 wienerCoord (if i = j then (1:ℝ) else 0),
      coeFn_boundedMul (a n-c) ((ha n).sub hc) (Lp.const 1 wienerCoord 1),
      Lp.coeFn_const 1 wienerCoord (1:ℝ)] with x hg hd hk hm h1
    simp only [hd, hg, hk, hm, h1, Pi.sub_apply, Function.const_apply, mul_one]
    rfl
  apply tendsto_sub_nhds_zero_iff.mp
  simp_rw [he]
  apply boundedMul_tendsto_zero_one (C := 2)
  · intro n
    exact ae_of_all _ fun x => (abs_sub _ _).trans (by linarith [hba n x, hbc x])
  · filter_upwards [] with x
    dsimp [a,c]
    split_ifs
    · simpa using ((wienerCos_tendsto (x i)).mul (wienerCos_tendsto (x j))).sub_const 1
    · simp

/-- The coordinate carré du champ is exactly the Kronecker delta as an L¹ class. -/
theorem wienerStructure_Γ_coordinate (i j : ℕ) :
    wienerStructure.Γ (wienerX i) (wienerX j) = Lp.const 1 wienerCoord (if i = j then 1 else 0) := by
  have h := wienerProto.toErrorData.closureGamma_characterization wienerProto_isClosable
    (a := wienerX i) (b := wienerX j)
    ⟨wienerApprox_isCauchy i, wienerApprox_tendsto i⟩
    ⟨wienerApprox_isCauchy j, wienerApprox_tendsto j⟩
  exact tendsto_nhds_unique h (wienerApprox_gamma_tendsto i j)

theorem wienerStructure_Γ_coordinate_ae (i j : ℕ) :
    ⇑(wienerStructure.Γ (wienerX i) (wienerX j)) =ᵐ[wienerCoord]
      fun _ => if i = j then 1 else 0 := by
  rw [wienerStructure_Γ_coordinate]
  exact Lp.coeFn_const _ _ _

end ErrorCalculus
