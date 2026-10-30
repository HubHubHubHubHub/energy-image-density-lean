import ErrorCalculus.Dirichlet.EIDUniversal

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- Rademacher's exceptional set carries no energy after composition with u. -/
theorem ae_differentiableAt_on_gamma_ne_zero {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (u : S.dom) :
    ∀ᵐ ω ∂μ, S.Γ u u ω ≠ 0 → DifferentiableAt ℝ F ((u : Lp ℝ 2 μ) ω) :=
  S.ae_on_gamma_ne_zero_of_ae_volume u hF.ae_differentiableAt

/-- Lebesgue differentiation of the derivative convolution, transferred by scalar EID. -/
theorem ae_deriv_mollify_general {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (u : S.dom) :
    ∀ᵐ ω ∂μ, S.Γ u u ω = 0 ∨ Tendsto
      (fun k => deriv (mollifyLipschitz F k) ((u : Lp ℝ 2 μ) ω)) atTop
      (𝓝 (deriv F ((u : Lp ℝ 2 μ) ω))) := by
  filter_upwards [S.ae_on_gamma_ne_zero_of_ae_volume u
    (deriv_lipschitzMollify_tendsto_ae hF)] with ω hω
  exact or_iff_not_imp_left.mpr hω

/-- The scalar chain rule for every Lipschitz F. The suffix preserves C¹ interface. -/
theorem gamma_lipschitzComp_general {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (u : S.dom) :
    S.Γ (S.lipschitzComp hF u) (S.lipschitzComp hF u) =ᵐ[μ]
      fun ω => (deriv F ((u : Lp ℝ 2 μ) ω))^2 * S.Γ u u ω := by
  exact S.gamma_comp_of_deriv_tendsto
    (fun k => (mollifyLipschitz_contDiff hF k).of_le (by simp))
    (mollifyLipschitz_lipschitz hF) u (S.lipschitzComp hF u)
    (S.tendsto_lipschitzComp_mollify_L2 hF u) (S.ae_deriv_mollify_general hF u)

end ErrorCalculus.ErrorStructure
