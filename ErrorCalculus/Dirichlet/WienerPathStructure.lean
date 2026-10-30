import ErrorCalculus.Dirichlet.TransportStructure
import ErrorCalculus.Dirichlet.WienerStructure
import Foundations.CameronMartinPath.Transport

noncomputable section
open MeasureTheory Filter Topology Foundations
namespace ErrorCalculus

/--
The Gaussian path map recovers the Wiener coordinates almost everywhere, after cancelling
reindexing.
-/
theorem gaussianPathMap_wienerNatCoordinate_ae :
    ∀ᵐ ω ∂wienerMeasure, gaussianPathMap (wienerNatCoordinate ω) = ω := by
  filter_upwards [schauderMap_schauderCoordinate_ae] with ω hω
  simpa only [gaussianPathMap, wienerNatCoordinate, Function.comp_apply,
    MeasurableEquiv.apply_symm_apply] using hω

/-- The concrete mod-zero isomorphism from Gaussian coordinates to Wiener paths. -/
def wienerPathIso : MeasureIsoModZero wienerCoord wienerMeasure where
  forward := gaussianPathMap
  backward := wienerNatCoordinate
  forward_preserving := measurePreserving_gaussianPathMap
  backward_preserving := measurePreserving_wienerNatCoordinate
  backward_forward := wienerNatCoordinate_gaussianPathMap_ae
  forward_backward := gaussianPathMap_wienerNatCoordinate_ae

/-- The Ornstein--Uhlenbeck error structure on continuous Wiener paths. -/
def wienerPathStructure : ErrorStructure PathSpace wienerMeasure :=
  wienerStructure.transport wienerPathIso

theorem wienerPathStructure_dom_iff (f : Lp ℝ 2 wienerMeasure) :
    f ∈ wienerPathStructure.dom ↔ wienerPathIso.lp 2 f ∈ wienerStructure.dom := Iff.rfl

theorem wienerPathStructure_energy (u v : wienerPathStructure.dom) :
    wienerPathStructure.energy.E u v = wienerStructure.energy.E
      (wienerStructure.transportDomMap wienerPathIso u)
      (wienerStructure.transportDomMap wienerPathIso v) :=
  wienerStructure.transport_energy wienerPathIso u v

theorem wienerPathStructure_Γ (u v : wienerPathStructure.dom) :
    wienerPathStructure.Γ u v = (wienerPathIso.lp 1).symm
      (wienerStructure.Γ (wienerStructure.transportDomMap wienerPathIso u)
        (wienerStructure.transportDomMap wienerPathIso v)) := rfl

end ErrorCalculus
