import ErrorCalculus.Dirichlet.WienerGamma

noncomputable section
open MeasureTheory Filter

namespace ErrorCalculus

/-- Coordinate gradients at two common descriptions agree after pullback. -/
theorem wienerPartial_level_indep {N M i : ℕ} (hi : i < N) (hi' : i < M)
    (u : protoDomD (ouDensityD N)) (v : protoDomD (ouDensityD M))
    (hu : cylProto N u = cylProto M v) :
    cylLp N 2 (gradD _ ⟨i, hi⟩ u) = cylLp M 2 (gradD _ ⟨i, hi'⟩ v) := by
  have hN : N ≤ max N M := le_max_left _ _
  have hM : M ≤ max N M := le_max_right _ _
  rw [← cylLp_comp hN 2, ← gradD_liftProto,
    ← cylLp_comp hM 2, ← gradD_liftProto,
    cylRep_common_unique u v hu hN hM]
  rfl

/-- An L² coordinate derivative, chosen at a level containing the coordinate. -/
def wienerPartialValue (i : ℕ) (F : wienerDom) : Lp ℝ 2 wienerCoord :=
  cylLp (max (i+1) (level F)) 2
    (gradD _ ⟨i, lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_left _ _)⟩
      (cylRepAt F (le_max_right _ _)))

theorem wienerPartialValue_at (i : ℕ) (F : wienerDom) {N : ℕ} (hi : i < N)
    (u : protoDomD (ouDensityD N)) (hu : cylProto N u = F) :
    wienerPartialValue i F = cylLp N 2 (gradD _ ⟨i, hi⟩ u) :=
  wienerPartial_level_indep _ hi _ u ((cylRepAt_spec F _).trans hu.symm)

@[simp] theorem wienerPartialValue_cyl {N : ℕ} (i : Fin N) (u : protoDomD (ouDensityD N)) :
    wienerPartialValue i.val (cylProto N u) = cylLp N 2 (gradD _ i u) :=
  wienerPartialValue_at i.val _ i.isLt u rfl

theorem wienerPartialValue_add (i : ℕ) (F G : wienerDom) :
    wienerPartialValue i (F + G) = wienerPartialValue i F + wienerPartialValue i G := by
  obtain ⟨N, hN, u, hu⟩ := exists_common_level_above ![F, G] (i+1)
  have hi : i < N := lt_of_lt_of_le (Nat.lt_succ_self i) hN
  have hu0 : cylProto N (u 0) = F := hu 0
  have hu1 : cylProto N (u 1) = G := hu 1
  rw [← hu0, ← hu1, ← map_add]
  rw [wienerPartialValue_at i _ hi (u 0 + u 1) rfl,
    wienerPartialValue_at i _ hi (u 0) rfl, wienerPartialValue_at i _ hi (u 1) rfl,
    map_add, map_add]

theorem wienerPartialValue_smul (i : ℕ) (c : ℝ) (F : wienerDom) :
    wienerPartialValue i (c • F) = c • wienerPartialValue i F := by
  let N := max (i+1) (level F)
  have hi : i < N := lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_left _ _)
  let u := cylRepAt F (show level F ≤ N from le_max_right _ _)
  have hu : cylProto N u = F := cylRepAt_spec F _
  rw [← hu, ← map_smul]
  rw [wienerPartialValue_at i _ hi (c • u) rfl, wienerPartialValue_at i _ hi u rfl,
    map_smul, map_smul]

/-- a linear L²-valued derivative for each coordinate. -/
def wienerPartial (i : ℕ) : wienerDom →ₗ[ℝ] Lp ℝ 2 wienerCoord where
  toFun := wienerPartialValue i
  map_add' := wienerPartialValue_add i
  map_smul' := wienerPartialValue_smul i

theorem wienerPartial_cyl {N : ℕ} (i : Fin N) (u : protoDomD (ouDensityD N)) :
    wienerPartial i.val (cylProto N u) = cylLp N 2 (gradD _ i u) :=
  wienerPartialValue_cyl i u

theorem wienerPartial_cyl_ge {N i : ℕ} (hi : N ≤ i) (u : protoDomD (ouDensityD N)) :
    wienerPartial i (cylProto N u) = 0 := by
  have h : N ≤ i+1 := hi.trans (Nat.le_succ i)
  rw [← cylProto_lift h u, wienerPartial_cyl (⟨i, Nat.lt_succ_self i⟩ : Fin (i+1)),
    gradD_liftProto_ge h _ hi, map_zero]

/-- Pointwise sum of squares, at any finite level representing F. -/
theorem wienerGamma_eq_sum_partial_sq (N : ℕ) (u : protoDomD (ouDensityD N)) :
    ⇑(wienerGamma (cylProto N u) (cylProto N u)) =ᵐ[wienerCoord]
      fun x => ∑ i : Fin N, (wienerPartial i.val (cylProto N u) x)^2 := by
  rw [wienerGamma_cyl]
  have hp : ∀ᵐ x ∂wienerCoord, ∀ i : Fin N,
      wienerPartial i.val (cylProto N u) x = partialRep _ i u (restrictN N x) := by
    apply ae_all_iff.mpr
    intro i
    rw [wienerPartial_cyl]
    exact (coeFn_cylLp N 2 _).trans
      ((restrictN_preserving N).quasiMeasurePreserving.ae_eq_comp (coeFn_gradD _ i u))
  filter_upwards [coeFn_cylLp N 1 (gammaD _ u u),
    (restrictN_preserving N).quasiMeasurePreserving.ae (coeFn_gammaD _ u u), hp] with x ha hb hc
  rw [ha, Function.comp_apply, hb]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc i, pow_two]
  rfl

theorem wienerPartial_norm_le (i : ℕ) (F : wienerDom) :
    ‖wienerPartial i F‖ ≤ 2 * Real.sqrt (wienerData.energy.E F F) := by
  let N := max (i+1) (level F)
  have hi : i < N := lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_left _ _)
  let u := cylRepAt F (show level F ≤ N from le_max_right _ _)
  have hu : cylProto N u = F := cylRepAt_spec F _
  change ‖wienerPartialValue i F‖ ≤ _
  rw [wienerPartialValue_at i F hi u hu, (cylLp N 2).norm_map,
    wienerData_energy_at F F u u hu hu]
  exact grad_norm_le_seminormD _ ⟨i, hi⟩ u

end ErrorCalculus
