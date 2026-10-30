import ErrorCalculus.Dirichlet.Calculus
import ErrorCalculus.Dirichlet.ExtensionGammaBounds
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- a measurable representative of an L² domain element. -/
def representative (u : S.dom) : Ω → ℝ :=
  (Lp.aestronglyMeasurable (u : Lp ℝ 2 μ)).aemeasurable.mk _

theorem measurable_representative (u : S.dom) : Measurable (S.representative u) :=
  (Lp.aestronglyMeasurable (u : Lp ℝ 2 μ)).aemeasurable.measurable_mk

theorem coeFn_representative (u : S.dom) :
    ⇑(u : Lp ℝ 2 μ) =ᵐ[μ] S.representative u :=
  (Lp.aestronglyMeasurable (u : Lp ℝ 2 μ)).aemeasurable.ae_eq_mk

/-- The energy measure, with density Γ[u,u] (without the factor 1/2). -/
def energyMeasure (u : S.dom) : Measure Ω :=
  μ.withDensity (fun ω => ENNReal.ofReal (S.Γ u u ω))

theorem energyMeasure_absolutelyContinuous (u : S.dom) : S.energyMeasure u ≪ μ :=
  withDensity_absolutelyContinuous _ _

instance energyMeasure_finite (u : S.dom) : IsFiniteMeasure (S.energyMeasure u) :=
  isFiniteMeasure_withDensity
    ((hasFiniteIntegral_iff_ofReal (S.Γ_nonneg u)).mp
      (L1.integrable_coeFn (S.Γ u u)).hasFiniteIntegral).ne

/-- scalar energy image density, formulated with a measurable representative. -/
def HasEID (u : S.dom) : Prop :=
  (S.energyMeasure u).map (S.representative u) ≪ volume

/-- B.Transfer any Lebesgue-a.e. property off the zero-energy set. -/
theorem HasEID.ae_of_ae_volume {u : S.dom} (h : S.HasEID u) {p : ℝ → Prop}
    (hp : ∀ᵐ y ∂volume, p y) :
    ∀ᵐ ω ∂μ, S.Γ u u ω ≠ 0 → p (S.representative u ω) := by
  have hm := ae_of_ae_map (S.measurable_representative u).aemeasurable (h.ae_le hp)
  have hd := (ae_withDensity_iff'
    (Lp.aestronglyMeasurable (S.Γ u u)).aemeasurable.ennreal_ofReal).mp hm
  filter_upwards [hd, S.Γ_nonneg u] with ω hd hn hz
  apply hd
  exact (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne hn (Ne.symm hz))).ne'

/-- The image measure is independent of the measurable representative. -/
theorem energyMeasure_map_eq {u : S.dom} {f : Ω → ℝ}
    (hf : f =ᵐ[μ] S.representative u) :
    (S.energyMeasure u).map f = (S.energyMeasure u).map (S.representative u) :=
  Measure.map_congr ((S.energyMeasure_absolutelyContinuous u).ae_le hf)

/-- A zero diagonal forces every mixed carré du champ to vanish there. -/
theorem gamma_eq_zero_of_diag_eq_zero (u v : S.dom) :
    ∀ᵐ ω ∂μ, S.Γ u u ω = 0 → S.Γ u v ω = 0 := by
  filter_upwards [S.toErrorData.gamma_cauchy_schwarz u v] with ω h hz
  rw [hz, zero_mul] at h
  nlinarith [sq_nonneg (S.Γ u v ω)]

end ErrorCalculus.ErrorStructure
