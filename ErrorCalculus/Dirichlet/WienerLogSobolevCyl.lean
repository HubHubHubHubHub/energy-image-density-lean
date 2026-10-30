import ErrorCalculus.Dirichlet.LogSobolev
import ErrorCalculus.Dirichlet.WienerStructure

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace ErrorCalculus

/-- Conditional Wiener LSI: integrability and the bound on the cylindrical pre-domain
suffice. No finite-dimensional logarithmic Sobolev theorem is assumed implicitly. -/
theorem wienerStructure_hasLogSobolev_of_proto
    (h : ∀ u : wienerDom,
      Integrable (fun x => ((u : Lp ℝ 2 wienerCoord) x)^2 *
        Real.log (((u : Lp ℝ 2 wienerCoord) x)^2)) wienerCoord ∧
      entropy wienerCoord (fun x => ((u : Lp ℝ 2 wienerCoord) x)^2) ≤
        4 * wienerProto.energy.E u u) :
    wienerStructure.HasLogSobolev 4 :=
  wienerProto.closure_hasLogSobolev wienerProto_isClosable h

/-- Conditional Wiener LSI from all finite-dimensional OU cylinders.
The hypothesis explicitly includes integrability, since real entropy uses a total integral. -/
theorem wienerStructure_hasLogSobolev_of_cyl
    (h : ∀ (N : ℕ) (u : (ouStructureD N).dom),
      Integrable (fun x => ((wienerOU N u : Lp ℝ 2 wienerCoord) x)^2 *
        Real.log (((wienerOU N u : Lp ℝ 2 wienerCoord) x)^2)) wienerCoord ∧
      entropy wienerCoord (fun x => ((wienerOU N u : Lp ℝ 2 wienerCoord) x)^2) ≤
        4 * wienerStructure.energy.E (wienerOU N u) (wienerOU N u)) :
    wienerStructure.HasLogSobolev 4 := by
  apply wienerStructure_hasLogSobolev_of_proto
  intro F
  obtain ⟨N, u, rfl⟩ := exists_cylRep F
  let v : (ouStructureD N).dom := (protoFormD (ouDensityD N)).inclusion u
  have hv : wienerOU N v = wienerInclusion (cylProto N u) := Subtype.ext rfl
  have hh := h N v
  rw [hv] at hh
  refine ⟨hh.1, ?_⟩
  have he : wienerStructure.energy.E (wienerInclusion (cylProto N u))
      (wienerInclusion (cylProto N u)) =
      wienerProto.energy.E (cylProto N u) (cylProto N u) := by
    change (1/2:ℝ) * (∫ x, wienerStructure.Γ _ _ x ∂wienerCoord) = _
    rw [wienerStructure_Γ_extends]
    rfl
  rw [he] at hh
  exact hh.2

end ErrorCalculus
