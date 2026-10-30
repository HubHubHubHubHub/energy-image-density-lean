import ErrorCalculus.Dirichlet.WienerClosable

noncomputable section
open MeasureTheory Filter Topology

namespace ErrorCalculus

/-- The closed OU error structure on Wiener coordinates. -/
def wienerStructure : ErrorStructure (ℕ → ℝ) wienerCoord :=
  wienerProto.closure wienerProto_isClosable

@[simp] theorem wienerStructure_dom : wienerStructure.dom = wienerProto.energy.closureDom := rfl

@[simp] theorem wienerStructure_energy :
    wienerStructure.energy = wienerProto.energy.closure wienerProto_isClosable :=
  wienerProto.closure_energy wienerProto_isClosable

/-- Canonical embedding of the cylindrical pre-domain in the closed domain. -/
def wienerInclusion : wienerDom →ₗ[ℝ] wienerStructure.dom := wienerProto.energy.inclusion

@[simp] theorem coe_wienerInclusion (F : wienerDom) :
    (wienerInclusion F : Lp ℝ 2 wienerCoord) = F := rfl

theorem wienerStructure_Γ_extends (F G : wienerDom) :
    wienerStructure.Γ (wienerInclusion F) (wienerInclusion G) = wienerProto.Γ F G :=
  wienerProto.closure_Γ_extends wienerProto_isClosable F G

theorem wienerStructure_dom_cyl (N : ℕ) (u : protoDomD (ouDensityD N)) :
    cylLp N 2 (u : Lp ℝ 2 _) ∈ wienerStructure.dom :=
  (wienerInclusion (cylProto N u)).property

/-- Mixed carré du champ on every finite-dimensional pre-domain. -/
theorem wienerStructure_Γ_cyl (N : ℕ) (u v : protoDomD (ouDensityD N)) :
    wienerStructure.Γ (wienerInclusion (cylProto N u)) (wienerInclusion (cylProto N v)) =
      cylLp N 1 (gammaD _ u v) := by
  rw [wienerStructure_Γ_extends, wienerProto_gamma_cyl]

theorem wienerStructure_energy_cyl (N : ℕ) (u v : protoDomD (ouDensityD N)) :
    wienerStructure.energy.E (wienerInclusion (cylProto N u)) (wienerInclusion (cylProto N v)) =
      (protoFormD (ouDensityD N)).E u v := by
  change (1/2:ℝ) * (∫ x, wienerStructure.Γ _ _ x ∂wienerCoord) = _
  rw [wienerStructure_Γ_cyl, integral_cylLp]
  rfl

/-- Cylindrical lifting preserves approaching sequences, including their energy Cauchy property. -/
theorem cylProto_approaches (N : ℕ) {u : ℕ → protoDomD (ouDensityD N)}
    {v : Lp ℝ 2 (densityMeasureD (ouDensityD N))} (hu : (protoFormD _).Approaches u v) :
    wienerProto.energy.Approaches (fun n => cylProto N (u n)) (cylLp N 2 v) := by
  have ht := (cylLp N 2).continuous.continuousAt.tendsto.comp hu.2
  refine ⟨?_, ht⟩
  rw [wienerProto.energy.isCauchy_iff]
  refine ⟨ht.cauchySeq, ?_⟩
  intro ε hε
  obtain ⟨M, hM⟩ := ((protoFormD _).isCauchy_iff u).mp hu.1 |>.2 ε hε
  refine ⟨M, fun m hm n hn => ?_⟩
  change Real.sqrt (wienerProto.energy.E (cylProto N (u m) - cylProto N (u n))
    (cylProto N (u m) - cylProto N (u n))) < ε
  rw [← map_sub, wienerProto_energy_cyl]
  exact hM m hm n hn

/-- The embedding also contains the entire closed finite-dimensional OU domain. -/
theorem cylLp_mem_wienerStructure (N : ℕ) (u : (ouStructureD N).dom) :
    cylLp N 2 (u : Lp ℝ 2 _) ∈ wienerStructure.dom := by
  obtain ⟨v, hv⟩ := ((protoFormD (ouDensityD N)).mem_closureDom_iff u).mp u.property
  exact (wienerProto.energy.mem_closureDom_iff _).mpr ⟨_, cylProto_approaches N hv⟩

/-- L²-isometric linear embedding of OU_N into the Wiener closed domain. -/
def wienerOU (N : ℕ) : (ouStructureD N).dom →ₗ[ℝ] wienerStructure.dom :=
  LinearMap.codRestrict wienerStructure.dom
    ((cylLp N 2).toLinearMap.comp (ouStructureD N).dom.subtype) (cylLp_mem_wienerStructure N)

@[simp] theorem coe_wienerOU (N : ℕ) (u : (ouStructureD N).dom) :
    (wienerOU N u : Lp ℝ 2 wienerCoord) = cylLp N 2 (u : Lp ℝ 2 _) := rfl

theorem wienerOU_injective (N : ℕ) : Function.Injective (wienerOU N) := by
  intro u v h
  exact Subtype.ext ((cylLp N 2).injective (congrArg Subtype.val h))

/-- Exact mixed Γ preservation on the full closed OU domain. -/
theorem wienerOU_Γ (N : ℕ) (u v : (ouStructureD N).dom) :
    wienerStructure.Γ (wienerOU N u) (wienerOU N v) = cylLp N 1 ((ouStructureD N).Γ u v) := by
  obtain ⟨un, hun⟩ := ((protoFormD (ouDensityD N)).mem_closureDom_iff u).mp u.property
  obtain ⟨vn, hvn⟩ := ((protoFormD (ouDensityD N)).mem_closureDom_iff v).mp v.property
  have hW := wienerProto.toErrorData.closureGamma_characterization wienerProto_isClosable
    (b := wienerOU N v) (a := wienerOU N u) (cylProto_approaches N hun) (cylProto_approaches N hvn)
  have hN := (protoDataD (ouDensityD N)).closureGamma_characterization
    (protoFormD_isClosable (ouDensityD N)) hun hvn
  have hT := (cylLp N 1).continuous.continuousAt.tendsto.comp hN
  apply tendsto_nhds_unique hW
  convert hT using 1
  · funext n
    exact wienerProto_gamma_cyl N (un n) (vn n)
  · rfl

theorem wienerOU_energy (N : ℕ) (u v : (ouStructureD N).dom) :
    wienerStructure.energy.E (wienerOU N u) (wienerOU N v) = (ouStructureD N).energy.E u v := by
  change (1/2:ℝ) * (∫ x, wienerStructure.Γ _ _ x ∂wienerCoord) = _
  rw [wienerOU_Γ, integral_cylLp]
  rfl

end ErrorCalculus
