import ErrorCalculus.Dirichlet.WienerPathStructure
import ErrorCalculus.Dirichlet.WienerPathFirstChaos
import Foundations.WienerPath.Indicator

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology Foundations
open scoped InnerProductSpace NNReal
namespace ErrorCalculus

/--
The pullback of a path Wiener integral agrees with the corresponding coordinate Wiener integral.
-/
theorem transportL2_wienerIntegralPath (g : HaarL2) :
    wienerPathIso.lp 2 (wienerIntegralPath g) =
      wienerIntegral (cameronMartinPathCoefficients g) := by
  have h : wienerIntegralPath g = (wienerPathIso.lp 2).symm
      (wienerIntegral (cameronMartinPathCoefficients g)) :=
    Lp.ext ((coe_wienerIntegralPath_nat g).trans (wienerPathIso.coe_lp_symm 2 _).symm)
  rw [h, LinearIsometryEquiv.apply_symm_apply]

/-- Every deterministic path integral belongs to the transported domain. -/
theorem wienerIntegralPath_mem_dom (g : HaarL2) :
    wienerIntegralPath g ∈ wienerPathStructure.dom := by
  rw [wienerPathStructure_dom_iff, transportL2_wienerIntegralPath]
  exact wienerIntegral_mem_wienerStructure_dom _

def wienerIntegralPathDom (g : HaarL2) : wienerPathStructure.dom :=
  ⟨wienerIntegralPath g, wienerIntegralPath_mem_dom g⟩

theorem transportDomMap_wienerIntegralPath (g : HaarL2) :
    wienerStructure.transportDomMap wienerPathIso (wienerIntegralPathDom g) =
      wienerIntegralDom (cameronMartinPathCoefficients g) :=
  Subtype.ext (transportL2_wienerIntegralPath g)

theorem inner_cameronMartinPathCoefficients (g h : HaarL2) :
    ⟪cameronMartinPathCoefficients g, cameronMartinPathCoefficients h⟫_ℝ = ⟪g,h⟫_ℝ := by
  unfold cameronMartinPathCoefficients
  rw [schauderCoefficientReindex.inner_map_map, haarBasis.repr.inner_map_map]

/-- Γ of two path integrals is their deterministic L² scalar product. -/
theorem wienerPathStructure_Γ_wienerIntegralPath (g h : HaarL2) :
    wienerPathStructure.Γ (wienerIntegralPathDom g) (wienerIntegralPathDom h) =
      Lp.const 1 wienerMeasure ⟪g,h⟫_ℝ := by
  rw [wienerPathStructure_Γ, transportDomMap_wienerIntegralPath,
    transportDomMap_wienerIntegralPath, wienerStructure_Γ_wienerIntegral,
    inner_cameronMartinPathCoefficients, MeasureIsoModZero.lp_symm_const]

theorem wienerPathStructure_energy_wienerIntegralPath (g h : HaarL2) :
    wienerPathStructure.energy.E (wienerIntegralPathDom g) (wienerIntegralPathDom h) =
      (1/2 : ℝ) * ⟪g,h⟫_ℝ := by
  rw [wienerPathStructure_energy, transportDomMap_wienerIntegralPath,
    transportDomMap_wienerIntegralPath, wienerStructure_energy_wienerIntegral,
    inner_cameronMartinPathCoefficients]

/-- The canonical process is the integral of the interval indicator. -/
theorem canonicalProcess_mem_wienerPathStructure_dom (t : WienerTime) :
    canonicalProcessLp t ∈ wienerPathStructure.dom := by
  rw [← wienerIntegralPath_indicator]
  exact wienerIntegralPath_mem_dom _

def canonicalProcessDom (t : WienerTime) : wienerPathStructure.dom :=
  ⟨canonicalProcessLp t, canonicalProcess_mem_wienerPathStructure_dom t⟩

theorem canonicalProcessDom_eq_integral (t : WienerTime) :
    canonicalProcessDom t = wienerIntegralPathDom (haarIndicator t) :=
  Subtype.ext (wienerIntegralPath_indicator t).symm

/-- Scalar product of two initial-interval indicators, including the endpoints. -/
theorem inner_haarIndicator_haarIndicator (s t : WienerTime) :
    ⟪haarIndicator s, haarIndicator t⟫_ℝ = min (s : ℝ≥0) (t : ℝ≥0) := by
  rw [haarIndicator, haarIndicator, L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]
  rw [Set.Ico_inter_Ico, max_self, measureReal_restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr (Set.Ico_subset_Ico le_rfl (by
      exact le_trans (min_le_left _ _) (by exact_mod_cast s.property.2)))]
  simp [Real.volume_real_Ico]

/-- The Brownian carré du champ is the constant min(s,t). -/
theorem wienerPathStructure_Γ_canonicalProcess (s t : WienerTime) :
    wienerPathStructure.Γ (canonicalProcessDom s) (canonicalProcessDom t) =
      Lp.const 1 wienerMeasure (min (s : ℝ≥0) (t : ℝ≥0) : ℝ) := by
  rw [canonicalProcessDom_eq_integral, canonicalProcessDom_eq_integral,
    wienerPathStructure_Γ_wienerIntegralPath, inner_haarIndicator_haarIndicator]
  simp only [NNReal.coe_min]

theorem wienerPathStructure_Γ_canonicalProcess_ae (s t : WienerTime) :
    ⇑(wienerPathStructure.Γ (canonicalProcessDom s) (canonicalProcessDom t))
      =ᵐ[wienerMeasure] fun _ => (min (s : ℝ≥0) (t : ℝ≥0) : ℝ) := by
  rw [wienerPathStructure_Γ_canonicalProcess]
  exact Lp.coeFn_const _ _ _

theorem wienerPathStructure_energy_canonicalProcess (t : WienerTime) :
    wienerPathStructure.energy.E (canonicalProcessDom t) (canonicalProcessDom t) =
      (t : ℝ≥0) / 2 := by
  rw [canonicalProcessDom_eq_integral, wienerPathStructure_energy_wienerIntegralPath,
    inner_haarIndicator_haarIndicator, min_self]
  ring

end ErrorCalculus
