import ErrorCalculus.Dirichlet.WienerDomain

noncomputable section
open MeasureTheory Filter

namespace ErrorCalculus

/-- two descriptions of the same cylinders give the same L¹ class. -/
theorem wienerGamma_level_indep {N M : ℕ}
    (u v : protoDomD (ouDensityD N)) (u' v' : protoDomD (ouDensityD M))
    (hu : cylProto N u = cylProto M u') (hv : cylProto N v = cylProto M v') :
    cylLp N 1 (gammaD _ u v) = cylLp M 1 (gammaD _ u' v') := by
  let K := max N M
  have hN : N ≤ K := le_max_left _ _
  have hM : M ≤ K := le_max_right _ _
  rw [← cylLp_comp hN 1, ← gammaD_comp_projLE,
    ← cylLp_comp hM 1, ← gammaD_comp_projLE,
    cylRep_common_unique u u' hu hN hM, cylRep_common_unique v v' hv hN hM]

/-- Carré du champ at a chosen common level; the next theorem removes the choice. -/
def wienerGamma (F G : wienerDom) : Lp ℝ 1 wienerCoord :=
  cylLp (max (level F) (level G)) 1
    (gammaD _ (cylRepAt F (le_max_left _ _)) (cylRepAt G (le_max_right _ _)))

theorem wienerGamma_at (F G : wienerDom) {N : ℕ} (u v : protoDomD (ouDensityD N))
    (hu : cylProto N u = F) (hv : cylProto N v = G) :
    wienerGamma F G = cylLp N 1 (gammaD _ u v) :=
  wienerGamma_level_indep _ _ u v
    ((cylRepAt_spec F _).trans hu.symm) ((cylRepAt_spec G _).trans hv.symm)

@[simp] theorem wienerGamma_cyl (N : ℕ) (u v : protoDomD (ouDensityD N)) :
    wienerGamma (cylProto N u) (cylProto N v) = cylLp N 1 (gammaD _ u v) :=
  wienerGamma_at _ _ u v rfl rfl

theorem wienerGamma_symm (F G : wienerDom) : wienerGamma F G = wienerGamma G F := by
  obtain ⟨N, u, v, w, rfl, rfl, _⟩ := exists_common_level_three F G G
  rw [wienerGamma_cyl, wienerGamma_cyl]
  exact congrArg (cylLp N 1) ((protoDataD (ouDensityD N)).Γ_symm u v)

theorem wienerGamma_add_right (F G H : wienerDom) :
    wienerGamma F (G + H) = wienerGamma F G + wienerGamma F H := by
  obtain ⟨N, u, v, w, rfl, rfl, rfl⟩ := exists_common_level_three F G H
  rw [← map_add, wienerGamma_cyl, wienerGamma_cyl, wienerGamma_cyl, map_add, map_add]

theorem wienerGamma_smul_right (c : ℝ) (F G : wienerDom) :
    wienerGamma F (c • G) = c • wienerGamma F G := by
  obtain ⟨N, u, v, w, rfl, rfl, _⟩ := exists_common_level_three F G G
  rw [← map_smul, wienerGamma_cyl, wienerGamma_cyl, map_smul, map_smul]

/-- Bilinear bundling on the actual increasing union domain. -/
def wienerGammaBilinear : wienerDom →ₗ[ℝ] wienerDom →ₗ[ℝ] Lp ℝ 1 wienerCoord where
  toFun F :=
    { toFun := wienerGamma F
      map_add' := wienerGamma_add_right F
      map_smul' := fun c G => wienerGamma_smul_right c F G }
  map_add' F G := by
    ext H : 1
    change wienerGamma (F + G) H = wienerGamma F H + wienerGamma G H
    rw [wienerGamma_symm (F + G), wienerGamma_add_right,
      wienerGamma_symm H F, wienerGamma_symm H G]
  map_smul' c F := by
    ext G : 1
    change wienerGamma (c • F) G = c • wienerGamma F G
    rw [wienerGamma_symm (c • F), wienerGamma_smul_right, wienerGamma_symm G F]

theorem wienerGamma_nonneg (F : wienerDom) : 0 ≤ᵐ[wienerCoord] ⇑(wienerGamma F F) := by
  obtain ⟨N, u, rfl⟩ := exists_cylRep F
  rw [wienerGamma_cyl]
  filter_upwards [coeFn_cylLp N 1 (gammaD _ u u),
    (restrictN_preserving N).quasiMeasurePreserving.ae ((protoDataD _).Γ_nonneg u)] with x hx hp
  exact hx ▸ hp

/-- The cylindrical algebraic error data, before density and calculus. -/
def wienerData : ErrorData (ℕ → ℝ) wienerCoord where
  dom := wienerDom
  Γ := wienerGammaBilinear
  Γ_symm := wienerGamma_symm
  Γ_nonneg := wienerGamma_nonneg

/-- Energy agrees with OU at every common finite level. -/
theorem wienerData_energy_cyl (N : ℕ) (u v : protoDomD (ouDensityD N)) :
    wienerData.energy.E (cylProto N u) (cylProto N v) = (protoFormD (ouDensityD N)).E u v := by
  change (1/2:ℝ) * (∫ x, wienerGamma (cylProto N u) (cylProto N v) x ∂_) =
    (1/2:ℝ) * (∫ x, gammaD _ u v x ∂_)
  rw [wienerGamma_cyl, integral_cylLp]

theorem wienerData_energy_at (F G : wienerDom) {N : ℕ} (u v : protoDomD (ouDensityD N))
    (hu : cylProto N u = F) (hv : cylProto N v = G) :
    wienerData.energy.E F G = (protoFormD (ouDensityD N)).E u v := by
  rw [← hu, ← hv, wienerData_energy_cyl]

end ErrorCalculus
