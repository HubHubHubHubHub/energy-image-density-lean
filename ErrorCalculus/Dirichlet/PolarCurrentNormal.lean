import ErrorCalculus.Dirichlet.PolarCurrentDensity

noncomputable section
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
namespace ErrorCalculus.PolarCurrent
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-- Represent an integrable divergence on the source by two finite image measures.
The hypothesis has the minus sign of distributional divergence. -/
theorem isNormal_of_source_density (T : PolarCurrent n) (X : Ω → (Fin n → ℝ))
    (hX : Measurable X) (a : Ω → ℝ) (ha : Measurable a) (hi : Integrable a μ)
    (hb : ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      T.boundary φ = -(∫ x, φ (X x) * a x ∂μ)) : T.IsNormal := by
  let ap : Ω → ℝ := fun x => max (a x) 0
  let am : Ω → ℝ := fun x => max (-a x) 0
  have hp : Integrable ap μ := hi.sup (integrable_zero _ _ _)
  have hm : Integrable am μ := hi.neg.sup (integrable_zero _ _ _)
  let μp := μ.withDensity (fun x => ENNReal.ofReal (ap x))
  let μm := μ.withDensity (fun x => ENNReal.ofReal (am x))
  haveI : IsFiniteMeasure μp := isFiniteMeasure_withDensity
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => le_max_right (a x) 0))).mp
      hp.hasFiniteIntegral).ne
  haveI : IsFiniteMeasure μm := isFiniteMeasure_withDensity
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => le_max_right (-a x) 0))).mp
      hm.hasFiniteIntegral).ne
  refine ⟨μp.map X, μm.map X, inferInstance, inferInstance, ?_⟩
  intro φ hφ hk
  rw [hb φ hφ hk]
  rw [integral_map hX.aemeasurable hφ.continuous.aestronglyMeasurable,
    integral_map hX.aemeasurable hφ.continuous.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul (μ := μ)
      (f := fun x => ENNReal.ofReal (max (a x) 0)) ((ha.max measurable_const).ennreal_ofReal)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul (μ := μ)
      (f := fun x => ENNReal.ofReal (max (-a x) 0)) ((ha.neg.max measurable_const).ennreal_ofReal)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (le_max_right _ (0 : ℝ)), smul_eq_mul]
  obtain ⟨C, hC⟩ := hk.exists_bound_of_continuous hφ.continuous
  have hip := hp.bdd_mul (hφ.continuous.measurable.comp hX).aestronglyMeasurable
    (ae_of_all _ (fun x => hC (X x)))
  have him := hm.bdd_mul (hφ.continuous.measurable.comp hX).aestronglyMeasurable
    (ae_of_all _ (fun x => hC (X x)))
  have he : (∫ x, φ (X x) * a x ∂μ) =
      (∫ x, ap x * φ (X x) ∂μ) - ∫ x, am x * φ (X x) ∂μ := by
    have hip' : Integrable (fun x => ap x * φ (X x)) μ := by simpa only [Function.comp_apply, mul_comm] using hip
    have him' : Integrable (fun x => am x * φ (X x)) μ := by simpa only [Function.comp_apply, mul_comm] using him
    rw [← integral_sub hip' him']
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp [ap, am]
    by_cases h : 0 ≤ a x
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    · rw [max_eq_right (le_of_not_ge h), max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]; ring
  rw [he]
  ring

end ErrorCalculus.PolarCurrent
