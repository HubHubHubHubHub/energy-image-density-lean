import ErrorCalculus.Dirichlet.LipschitzCalculus
import ErrorCalculus.Dirichlet.DirichletProperty
import Foundations.EnergyImageDensity.Lipschitz
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
namespace ErrorCalculus

/-- push forward a density pulled back along a measurable map. -/
theorem eid_map_withDensity_comp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {g : Ω → ℝ} (hg : Measurable g)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (fun x => f (g x))).map g = (μ.map g).withDensity f := by
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs,
    setLIntegral_map hs hf hg]

/-- a finite absolutely continuous measure has a real-valued measurable density. -/
theorem eid_withDensity_rnDeriv_toReal (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν ≪ volume) :
    volume.withDensity (fun x => ENNReal.ofReal ((ν.rnDeriv volume x).toReal)) = ν := by
  refine (withDensity_congr_ae ?_).trans (ν.withDensity_rnDeriv_eq volume hν)
  filter_upwards [ν.rnDeriv_lt_top volume] with x hx
  exact ENNReal.ofReal_toReal (ne_of_lt hx)

/--
For a finite measure ν absolutely continuous with respect to Lebesgue measure and a Lipschitz real
function F, the image under F of (F′)² ν is absolutely continuous.
-/
theorem eid_map_sq_deriv_absolutelyContinuous (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν ≪ volume) {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) :
    (ν.withDensity (fun x => ENNReal.ofReal ((deriv F x)^2))).map F ≪ volume := by
  have hr : Measurable (fun x => (ν.rnDeriv volume x).toReal) :=
    (ν.measurable_rnDeriv volume).ennreal_toReal
  rw [← eid_withDensity_rnDeriv_toReal ν hν,
    ← withDensity_mul volume hr.ennreal_ofReal ((measurable_deriv F).pow_const 2).ennreal_ofReal]
  have he : (fun x => ENNReal.ofReal ((ν.rnDeriv volume x).toReal)) *
      (fun x => ENNReal.ofReal ((deriv F x)^2)) =
      (fun x => ENNReal.ofReal ((deriv F x)^2 * (ν.rnDeriv volume x).toReal)) := by
    funext x
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    exact mul_comm _ _
  rw [he]
  exact Foundations.LipschitzWith.map_withDensity_sq_deriv_mul_absolutelyContinuous hF hr

namespace ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- The composed energy measure is obtained by multiplying by F'(u)². -/
theorem energyMeasure_lipschitz_comp {u : S.dom} (hu : S.HasEID u)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (w : S.dom)
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun x => F (S.representative u x)) :
    S.energyMeasure w = (S.energyMeasure u).withDensity
      (fun x => ENNReal.ofReal ((deriv F (S.representative u x))^2)) := by
  unfold energyMeasure
  refine Eq.trans ?_ (withDensity_mul₀
    (Lp.aestronglyMeasurable (S.Γ u u)).aemeasurable.ennreal_ofReal
    (((measurable_deriv F).comp (S.measurable_representative u)).pow_const 2).ennreal_ofReal.aemeasurable)
  apply withDensity_congr_ae
  filter_upwards [S.lipschitz_calculus_diag hu hF w hw] with x hx
  simp only [hx, Pi.mul_apply]
  rw [ENNReal.ofReal_mul (sq_nonneg _)]
  exact mul_comm _ _

/-- energy image density is stable under every scalar Lipschitz composition. -/
theorem HasEID.lipschitz_comp {u : S.dom} (hu : S.HasEID u)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (w : S.dom)
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun x => F (S.representative u x)) : S.HasEID w := by
  have hr : (fun x => F (S.representative u x)) =ᵐ[μ] S.representative w :=
    hw.symm.trans (S.coeFn_representative w)
  unfold HasEID
  rw [← S.energyMeasure_map_eq hr, S.energyMeasure_lipschitz_comp hu hF w hw]
  change ((S.energyMeasure u).withDensity
    (fun x => ENNReal.ofReal ((deriv F (S.representative u x))^2))).map
      (F ∘ S.representative u) ≪ volume
  rw [← Measure.map_map hF.continuous.measurable (S.measurable_representative u),
    eid_map_withDensity_comp _ (S.measurable_representative u)
      ((measurable_deriv F).pow_const 2).ennreal_ofReal]
  exact eid_map_sq_deriv_absolutelyContinuous _ hu hF

/-- The same stability statement with the L² representative in the composition hypothesis. -/
theorem HasEID.lipschitz_comp_coe {u : S.dom} (hu : S.HasEID u)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (w : S.dom)
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun x => F ((u : Lp ℝ 2 μ) x)) : S.HasEID w :=
  hu.lipschitz_comp S hF w (hw.trans ((S.coeFn_representative u).fun_comp F))

/-- absolute value preserves EID. -/
theorem HasEID.abs {u : S.dom} (hu : S.HasEID u) :
    S.HasEID ⟨|(u : Lp ℝ 2 μ)|, S.abs_mem_dom hu⟩ :=
  hu.lipschitz_comp_coe S (show LipschitzWith 1 (fun x : ℝ => |x|) from
    lipschitzWith_one_norm) _ (Lp.coeFn_abs _)

/-- The positive part preserves EID. -/
theorem HasEID.posPart {u : S.dom} (hu : S.HasEID u) :
    S.HasEID ⟨(u : Lp ℝ 2 μ) ⊔ 0, S.posPart_mem_dom hu⟩ := by
  apply hu.lipschitz_comp_coe S (LipschitzWith.id.max_const 0)
  filter_upwards [Lp.coeFn_sup (u : Lp ℝ 2 μ) 0, Lp.coeFn_zero ℝ 2 μ] with x hs hz
  simp only [hs, Pi.sup_apply, hz, Pi.zero_apply, id_eq]

/-- truncation above at an arbitrary real constant preserves EID. -/
theorem HasEID.min_const {u : S.dom} (hu : S.HasEID u) (c : ℝ) :
    S.HasEID ⟨(u : Lp ℝ 2 μ) ⊓ Lp.const 2 μ c, S.min_const_mem_dom u c⟩ := by
  apply hu.lipschitz_comp_coe S (LipschitzWith.id.min_const c)
  filter_upwards [Lp.coeFn_inf (u : Lp ℝ 2 μ) (Lp.const 2 μ c),
    Lp.coeFn_const (p := 2) (μ := μ) (c := c)] with x hi hc
  simp [hi]

/-- The Markov unit contraction preserves EID. -/
theorem HasEID.unitContraction {u : S.dom} (hu : S.HasEID u) :
    S.HasEID ⟨(0 ⊔ (u : Lp ℝ 2 μ)) ⊓ Lp.const 2 μ 1, S.unitContraction_mem_dom u⟩ := by
  apply hu.lipschitz_comp_coe S ((LipschitzWith.id.const_max 0).min_const 1)
  filter_upwards [Lp.coeFn_inf (0 ⊔ (u : Lp ℝ 2 μ)) (Lp.const 2 μ 1),
    Lp.coeFn_sup (0 : Lp ℝ 2 μ) u, Lp.coeFn_zero ℝ 2 μ,
    Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with x hi hs hz hc
  simp [hi, hs]

end ErrorStructure
end ErrorCalculus
