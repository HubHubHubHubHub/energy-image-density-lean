import Foundations.Wiener.Coordinates
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory

namespace Foundations

/-- Pullback by an almost surely identity map acts as the identity on L² classes. -/
theorem lp_compMeasurePreserving_eq_self {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → Ω} (hf : MeasurePreserving f P P) (heq : ∀ᵐ ω ∂P, f ω = ω)
    (u : Lp ℝ 2 P) : Lp.compMeasurePreserving f hf u = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving u hf, heq] with ω hω hfω
  exact hω.trans (congrArg u hfω)

/-- The two pullbacks on L² are inverse, on Gaussian coordinates. -/
theorem wiener_pullback_coordinates (u : Lp ℝ 2 schauderGaussianMeasure) :
    Lp.compMeasurePreserving schauderMap measurePreserving_schauderMap
      (Lp.compMeasurePreserving schauderCoordinate measurePreserving_schauderCoordinate u) = u := by
  rw [← Lp.compMeasurePreserving_comp_apply]
  exact lp_compMeasurePreserving_eq_self _ wienerCoordinateEquiv.2.2.1 u

/-- The two pullbacks on L² are inverse, on Wiener paths. -/
theorem wiener_pullback_paths (u : Lp ℝ 2 wienerMeasure) :
    Lp.compMeasurePreserving schauderCoordinate measurePreserving_schauderCoordinate
      (Lp.compMeasurePreserving schauderMap measurePreserving_schauderMap u) = u := by
  rw [← Lp.compMeasurePreserving_comp_apply]
  exact lp_compMeasurePreserving_eq_self _ schauderMap_schauderCoordinate_ae u

/-- The explicit mod-zero isomorphism induces a linear isometric equivalence of real L² spaces. -/
noncomputable def wienerL2Equiv :
    Lp ℝ 2 wienerMeasure ≃ₗᵢ[ℝ] Lp ℝ 2 schauderGaussianMeasure :=
  LinearIsometryEquiv.ofLinearIsometry
    (Lp.compMeasurePreservingₗᵢ ℝ schauderMap measurePreserving_schauderMap)
    (Lp.compMeasurePreservingₗ ℝ schauderCoordinate measurePreserving_schauderCoordinate)
    (by ext u : 1; exact wiener_pullback_coordinates u)
    (by ext u : 1; exact wiener_pullback_paths u)

/-- On representatives, the forward equivalence is composition with the Schauder map. -/
theorem coe_wienerL2Equiv (u : Lp ℝ 2 wienerMeasure) :
    wienerL2Equiv u =ᵐ[schauderGaussianMeasure] u ∘ schauderMap :=
  Lp.coeFn_compMeasurePreserving u measurePreserving_schauderMap

/-- On representatives, the inverse equivalence is composition with the coordinate map. -/
theorem coe_wienerL2Equiv_symm (u : Lp ℝ 2 schauderGaussianMeasure) :
    wienerL2Equiv.symm u =ᵐ[wienerMeasure] u ∘ schauderCoordinate :=
  Lp.coeFn_compMeasurePreserving u measurePreserving_schauderCoordinate

end Foundations
