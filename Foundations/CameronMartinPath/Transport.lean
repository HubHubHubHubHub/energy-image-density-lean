import Foundations.WienerPath.Integral

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter Topology
namespace Foundations

/-- Push a density forward when it is the pullback of a density on the target. -/
theorem map_withDensity_of_ae_comp {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {S : Ω → E} (hS : Measurable S) {d : Ω → ENNReal} {D : E → ENNReal}
    (hD : AEMeasurable D (P.map S)) (he : d =ᵐ[P] fun x => D (S x)) :
    (P.withDensity d).map S = (P.map S).withDensity D := by
  ext A hA
  rw [Measure.map_apply hS hA,withDensity_apply _ (hS hA),withDensity_apply _ hA,
    ← lintegral_indicator hA,lintegral_map' (hD.indicator hA) hS.aemeasurable,
    ← lintegral_indicator (hS hA)]
  apply lintegral_congr_ae
  filter_upwards [he] with x hx
  by_cases h : S x ∈ A <;> simp [Set.indicator,h,hx]

theorem schauderPartial_add (N : ℕ) (x y : SchauderIndex → ℝ) :
    schauderPartial N (x+y) = schauderPartial N x + schauderPartial N y := by
  simp [schauderPartial,Pi.add_apply,add_smul,Finset.sum_add_distrib]

theorem schauderGoodSet_add {x y : SchauderIndex → ℝ}
    (hx : x ∈ schauderGoodSet) (hy : y ∈ schauderGoodSet) : x+y ∈ schauderGoodSet := by
  apply (mem_schauderGoodSet_iff _).mpr
  exact ⟨schauderMap x+schauderMap y,by
    simpa only [schauderPartial_add] using (tendsto_schauderPartial hx).add (tendsto_schauderPartial hy)⟩

theorem schauderMap_add {x y : SchauderIndex → ℝ}
    (hx : x ∈ schauderGoodSet) (hy : y ∈ schauderGoodSet) :
    schauderMap (x+y) = schauderMap x+schauderMap y :=
  tendsto_nhds_unique (tendsto_schauderPartial (schauderGoodSet_add hx hy))
    (by simpa only [schauderPartial_add] using
      (tendsto_schauderPartial hx).add (tendsto_schauderPartial hy))

def gaussianPathMap : (ℕ → ℝ) → PathSpace := schauderMap ∘ schauderReindex
def wienerNatCoordinate : PathSpace → (ℕ → ℝ) := schauderReindex.symm ∘ schauderCoordinate

theorem measurePreserving_gaussianPathMap :
    MeasurePreserving gaussianPathMap gaussianInf wienerMeasure :=
  measurePreserving_schauderMap.comp measurePreserving_schauderReindex

theorem measurePreserving_wienerNatCoordinate :
    MeasurePreserving wienerNatCoordinate wienerMeasure gaussianInf :=
  measurePreserving_schauderReindex_symm.comp measurePreserving_schauderCoordinate

theorem wienerNatCoordinate_gaussianPathMap_ae :
    ∀ᵐ x ∂gaussianInf, wienerNatCoordinate (gaussianPathMap x) = x := by
  filter_upwards [measurePreserving_schauderReindex.quasiMeasurePreserving.ae
    ae_mem_schauderGoodSet] with x hx
  simp only [wienerNatCoordinate,gaussianPathMap,Function.comp_def,
    schauderCoordinate_schauderMap hx,MeasurableEquiv.symm_apply_apply]

def cameronMartinPathCoefficients (g : HaarL2) : CameronMartinSpace :=
  schauderCoefficientReindex (haarBasis.repr g)

@[simp] theorem norm_cameronMartinPathCoefficients (g : HaarL2) :
    ‖cameronMartinPathCoefficients g‖ = ‖g‖ := by
  simp [cameronMartinPathCoefficients]

theorem coe_wienerIntegralPath_nat (g : HaarL2) :
    wienerIntegralPath g =ᵐ[wienerMeasure] fun ω =>
      wienerIntegral (cameronMartinPathCoefficients g) (wienerNatCoordinate ω) := by
  filter_upwards [coe_wienerIntegralPath g,
    measurePreserving_schauderCoordinate.quasiMeasurePreserving.ae
      (coe_wienerIntegralSchauder (haarBasis.repr g))] with ω h1 h2
  exact h1.trans h2

theorem gaussianPathMap_add_ae (g : HaarL2) : ∀ᵐ x ∂gaussianInf,
    gaussianPathMap (x+(cameronMartinPathCoefficients g : ℕ → ℝ)) =
      gaussianPathMap x+cameronMartinPath g := by
  filter_upwards [measurePreserving_schauderReindex.quasiMeasurePreserving.ae
    ae_mem_schauderGoodSet] with x hx
  have he : schauderReindex (x+(cameronMartinPathCoefficients g : ℕ → ℝ)) =
      schauderReindex x+schauderCoordinate (cameronMartinPath g) := by
    funext i
    simp [cameronMartinPathCoefficients,schauderCoordinate_cameronMartinPath]
  change schauderMap _ = schauderMap _ + _
  rw [he,schauderMap_add hx (cameronMartinPath_mem_schauderGoodSet g),
    schauderMap_coordinate_cameronMartinPath]

end Foundations
