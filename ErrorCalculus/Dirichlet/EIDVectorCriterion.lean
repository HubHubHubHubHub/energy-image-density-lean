import ErrorCalculus.Dirichlet.EIDVectorWeights
import Foundations.AbsCont.Applications

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {d : ℕ}

theorem euclideanEquiv_single (i : Fin d) :
    euclideanEquiv d (Pi.single i 1) = EuclideanSpace.basisFun (Fin d) ℝ i := by
  rw [EuclideanSpace.basisFun_apply]
  rfl

/-- Transport the directional derivative, with no change in its normalization. -/
theorem fderiv_comp_euclideanEquiv {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Differentiable ℝ φ) (x : Fin d → ℝ) (i : Fin d) :
    fderiv ℝ (φ ∘ euclideanEquiv d) x (Pi.single i 1) =
      fderiv ℝ φ (euclideanEquiv d x) (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  rw [fderiv_comp x (hφ _) (euclideanEquiv d).differentiableAt,
    (euclideanEquiv d).fderiv]
  change fderiv ℝ φ _ (euclideanEquiv d (Pi.single i 1)) = _
  rw [euclideanEquiv_single]

omit [IsProbabilityMeasure μ] in
/-- The elementary L∞ × L¹ estimate used by both forms of the criterion. -/
theorem abs_integral_mul_L1_le (δ : Lp ℝ 1 μ) {f : Ω → ℝ} {C : ℝ}
    (hf : ∀ a, ‖f a‖ ≤ C) :
    |∫ a, f a * δ a ∂μ| ≤ ‖δ‖ * C := by
  have h := norm_integral_le_of_norm_le ((L1.integrable_coeFn δ).norm.const_mul C)
    (Eventually.of_forall fun a => show ‖f a * δ a‖ ≤ C * ‖δ a‖ from
      (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hf a) (norm_nonneg _)))
  rw [integral_const_mul, ← L1.norm_eq_integral_norm, Real.norm_eq_abs, mul_comm C] at h
  exact h

/--
Integration by parts against smooth compactly supported product tests, with integrable coordinate
weights, implies absolute continuity of the finite image measure on Euclidean space.
-/
theorem absolutelyContinuous_map_of_ibp (hd : 0 < d) (u : Fin d → S.dom)
    (δ : Fin d → Lp ℝ 1 μ)
    (hibp : ∀ i (φ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ a, fderiv ℝ φ (S.representativeVec u a) (Pi.single i 1) ∂μ) =
        ∫ a, φ (S.representativeVec u a) * δ i a ∂μ) :
    μ.map (S.toEuclidean u) ≪ volume := by
  apply Foundations.absolutelyContinuous_map_of_ibp hd (S.measurable_toEuclidean u)
    (C := fun i => ‖δ i‖) (fun i => norm_nonneg _)
  intro i φ hφ hk
  have H := hibp i (φ ∘ euclideanEquiv d) (hφ.comp (euclideanEquiv d).contDiff)
    (hk.comp_homeomorph (euclideanEquiv d).toHomeomorph)
  simp_rw [fderiv_comp_euclideanEquiv (hφ.differentiable (by simp))] at H
  change |∫ a, fderiv ℝ φ (euclideanEquiv d (S.representativeVec u a))
    (EuclideanSpace.basisFun (Fin d) ℝ i) ∂μ| ≤ _
  rw [H]
  exact abs_integral_mul_L1_le (δ i) (fun a => φ.norm_coe_le_norm _)

/-- an L¹ divergence, tested against every compact C¹ composition. -/
def HasDivergence (hd : 0 < d) (u : Fin d → S.dom)
    (w : Fin d → Fin d → Ω → ℝ) (δ : Fin d → Lp ℝ 1 μ) : Prop :=
  ∀ i (φ : (Fin d → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (hk : HasCompactSupport φ),
    (∫ a, ∑ j, w i j a * S.Γ (S.compactComp hd u φ hφ hk) (u j) a ∂μ) =
      ∫ a, φ (S.representativeVec u a) * δ i a ∂μ

/-- The exact supremum-norm estimate, with constant ‖δᵢ‖₁. -/
theorem abs_integral_fderiv_comp_le (hd : 0 < d) (u : Fin d → S.dom)
    {w : Fin d → Fin d → Ω → ℝ} (hw : S.MalliavinWeights u w)
    {δ : Fin d → Lp ℝ 1 μ} (hδ : S.HasDivergence hd u w δ)
    (i : Fin d) (φ : (Fin d → ℝ) →ᵇ ℝ)
    (hφ : ContDiff ℝ 1 φ) (hk : HasCompactSupport φ) :
    |∫ a, fderiv ℝ φ (S.representativeVec u a) (Pi.single i 1) ∂μ| ≤ ‖δ i‖ * ‖φ‖ := by
  rw [integral_congr_ae (S.fderiv_comp_eq_sum_weights_gamma hd u hw hφ hk
    (S.compactComp hd u φ hφ hk) (S.coeFn_compactComp hd u φ hφ hk) i), hδ i φ hφ hk]
  exact abs_integral_mul_L1_le (δ i) (fun a => φ.norm_coe_le_norm _)

/--
Bounded Malliavin weights yield absolute continuity through integration by parts on Euclidean space.
-/
theorem absolutelyContinuous_map_of_weights (hd : 0 < d) (u : Fin d → S.dom)
    {w : Fin d → Fin d → Ω → ℝ} (hw : S.MalliavinWeights u w)
    {δ : Fin d → Lp ℝ 1 μ} (hδ : S.HasDivergence hd u w δ) :
    μ.map (S.toEuclidean u) ≪ volume := by
  apply S.absolutelyContinuous_map_of_ibp hd u δ
  intro i φ hφ hk
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  exact (integral_congr_ae (S.fderiv_comp_eq_sum_weights_gamma hd u hw hφ1 hk
    (S.compactComp hd u φ hφ1 hk) (S.coeFn_compactComp hd u φ hφ1 hk) i)).trans
      (hδ i φ hφ1 hk)

omit [IsProbabilityMeasure μ] in
/-- Transport back to product Lebesgue measure, whose normalization agrees with volume. -/
theorem absolutelyContinuous_map_pi_of_euclidean {X : Ω → (Fin d → ℝ)}
    (hX : Measurable X) (h : μ.map (euclideanEquiv d ∘ X) ≪ volume) :
    μ.map X ≪ volume := by
  have H := h.map (euclideanEquiv d).symm.continuous.measurable
  have hv : (volume : Measure (EuclideanSpace ℝ (Fin d))).map (euclideanEquiv d).symm =
      volume := (PiLp.volume_preserving_ofLp (Fin d)).map_eq
  rw [hv, Measure.map_map (euclideanEquiv d).symm.continuous.measurable
    ((euclideanEquiv d).continuous.measurable.comp hX)] at H
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using H

/-- V.3(b), also available with product volume on the finite function space. -/
theorem absolutelyContinuous_map_representativeVec_of_weights (hd : 0 < d)
    (u : Fin d → S.dom) {w : Fin d → Fin d → Ω → ℝ} (hw : S.MalliavinWeights u w)
    {δ : Fin d → Lp ℝ 1 μ} (hδ : S.HasDivergence hd u w δ) :
    μ.map (S.representativeVec u) ≪ volume :=
  absolutelyContinuous_map_pi_of_euclidean (S.measurable_representativeVec u)
    (S.absolutelyContinuous_map_of_weights hd u hw hδ)

end ErrorCalculus.ErrorStructure
