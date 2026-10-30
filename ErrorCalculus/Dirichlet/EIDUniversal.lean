import ErrorCalculus.Dirichlet.EnergyImageDensity
import ErrorCalculus.Dirichlet.LipschitzEID
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- Exact predicate is scalar energy image density at one domain element. -/
theorem hasEID_of_errorStructure (u : S.dom) : S.HasEID u := by
  unfold HasEID
  rw [← S.energyMeasure_map_eq (S.coeFn_representative u)]
  exact S.energyImage_absolutelyContinuous u

/-- The law restricted to the positive-energy set is absolutely continuous. -/
theorem map_restrict_gamma_pos_absolutelyContinuous (u : S.dom) :
    (μ.restrict {ω | 0 < S.Γ u u ω}).map (u : Lp ℝ 2 μ) ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hzero
  rw [Measure.map_apply (Lp.stronglyMeasurable (u : Lp ℝ 2 μ)).measurable hA,
    Measure.restrict_apply ((Lp.stronglyMeasurable (u : Lp ℝ 2 μ)).measurable hA)]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [S.gamma_eq_zero_on_null u hA hzero] with ω hω hmem
  exact (ne_of_gt hmem.2) (hω hmem.1)

/-- Transport Lebesgue-a.e. statements to the actual L² representative wherever Γ is nonzero. -/
theorem ae_on_gamma_ne_zero_of_ae_volume (u : S.dom) {p : ℝ → Prop}
    (hp : ∀ᵐ x ∂volume, p x) :
    ∀ᵐ ω ∂μ, S.Γ u u ω ≠ 0 → p ((u : Lp ℝ 2 μ) ω) := by
  filter_upwards [(S.hasEID_of_errorStructure u).ae_of_ae_volume S hp,
    S.coeFn_representative u] with ω hω hr hn
  rw [hr]
  exact hω hn

/-- A canonical Radon--Nikodym density for the restricted law. -/
theorem withDensity_rnDeriv_gamma_pos (u : S.dom) :
    volume.withDensity
      (((μ.restrict {ω | 0 < S.Γ u u ω}).map (u : Lp ℝ 2 μ)).rnDeriv volume) =
        (μ.restrict {ω | 0 < S.Γ u u ω}).map (u : Lp ℝ 2 μ) :=
  Measure.withDensity_rnDeriv_eq _ _ (S.map_restrict_gamma_pos_absolutelyContinuous u)

theorem exists_density_of_gamma_pos (u : S.dom) :
    ∃ ρ : ℝ → ℝ≥0∞, Measurable ρ ∧ volume.withDensity ρ =
      (μ.restrict {ω | 0 < S.Γ u u ω}).map (u : Lp ℝ 2 μ) :=
  ⟨_, Measure.measurable_rnDeriv _ _, S.withDensity_rnDeriv_gamma_pos u⟩

end ErrorCalculus.ErrorStructure
