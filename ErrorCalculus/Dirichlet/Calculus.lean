import ErrorCalculus.Dirichlet.ErrorStructure
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- Constant functions belong to the domain and have zero mixed carré du champ. -/
theorem constant_calculus (c : ℝ) : ∃ hc : Lp.const 2 μ c ∈ S.dom,
    ∀ v : S.dom, ⇑(S.Γ ⟨Lp.const 2 μ c, hc⟩ v) =ᵐ[μ] 0 := by
  obtain ⟨hc, he⟩ := S.calc 1 (by decide) (fun _ => 0) (fun _ => c) 0
    contDiff_const (LipschitzWith.const c) (Lp.const 2 μ c) (Lp.coeFn_const (p := 2) (μ := μ) (c := c))
  refine ⟨hc, fun v => ?_⟩
  filter_upwards [he v] with ω hω
  simpa using hω

/-- The canonical constant domain element. -/
def const (c : ℝ) : S.dom := ⟨Lp.const 2 μ c, (S.constant_calculus c).choose⟩

/-- Constants have zero mixed carré du champ, as L¹ classes. -/
theorem gamma_const (c : ℝ) (v : S.dom) : S.Γ (S.const c) v = 0 := by
  apply Lp.ext
  exact ((S.constant_calculus c).choose_spec v).trans (Lp.coeFn_zero ℝ 1 μ).symm

/-- The unit has zero mixed carré du champ almost surely. -/
theorem gamma_one (v : S.dom) : ⇑(S.Γ ⟨Lp.const 2 μ 1, S.one_mem⟩ v) =ᵐ[μ] 0 :=
  (S.constant_calculus 1).choose_spec v

/-- Constants have zero energy. -/
theorem energy_const (c : ℝ) : S.energy.E (S.const c) (S.const c) = 0 := by
  rw [ErrorData.energy_apply, S.gamma_const]
  rw [integral_congr_ae (Lp.coeFn_zero ℝ 1 μ)]
  simp

/-- The coordinate derivative in dimension one is the ordinary derivative. -/
theorem fderiv_fin_one {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (x : Fin 1 → ℝ) :
    fderiv ℝ (fun y : Fin 1 → ℝ => F (y 0)) x (Pi.single 0 1) = deriv F (x 0) := by
  let p : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hd := (hF.differentiable (by norm_num) (x 0)).hasDerivAt.comp_hasFDerivAt x p.hasFDerivAt
  change (fderiv ℝ (F ∘ p) x) (Pi.single 0 1) = deriv F (x 0)
  rw [hd.fderiv]
  simp [p]

/-- scalar C¹ Lipschitz chain rule, for any specified L² representative. -/
theorem chain_one {F : ℝ → ℝ} {L : ℝ≥0} (hF : ContDiff ℝ 1 F)
    (hL : LipschitzWith L F) (u : S.dom) (w : Lp ℝ 2 μ)
    (hw : ⇑w =ᵐ[μ] fun ω => F ((u : Lp ℝ 2 μ) ω)) :
    ∃ hd : w ∈ S.dom, ∀ v : S.dom,
      ⇑(S.Γ ⟨w, hd⟩ v) =ᵐ[μ] fun ω => deriv F ((u : Lp ℝ 2 μ) ω) * S.Γ u v ω := by
  let p : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  obtain ⟨hd, he⟩ := S.calc 1 (by decide) (fun _ => u) (fun x => F (p x))
    (L * ‖p‖₊) (hF.comp p.contDiff) (hL.comp p.lipschitz) w hw
  refine ⟨hd, fun v => ?_⟩
  simpa only [Fin.sum_univ_one, p, ContinuousLinearMap.proj_apply, fderiv_fin_one hF] using he v

/-- The diagonal scalar chain rule. -/
theorem chain_diagonal {F : ℝ → ℝ} {L : ℝ≥0} (hF : ContDiff ℝ 1 F)
    (hL : LipschitzWith L F) (u w : S.dom)
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun ω => F ((u : Lp ℝ 2 μ) ω)) :
    ⇑(S.Γ w w) =ᵐ[μ] fun ω => (deriv F ((u : Lp ℝ 2 μ) ω)) ^ 2 * S.Γ u u ω := by
  obtain ⟨hd, he⟩ := S.chain_one hF hL u w hw
  have h1 := he w
  have h2 := he u
  have hsym := S.Γ_symm u w
  filter_upwards [h1, h2] with ω hω hω'
  change S.Γ w w ω = _ at hω
  change S.Γ w u ω = _ at hω'
  rw [hω, hsym, hω']
  ring

/-- The exact L² energy contraction bound. -/
theorem energy_contraction {F : ℝ → ℝ} {L : ℝ≥0} (hF : ContDiff ℝ 1 F)
    (hL : LipschitzWith L F) (u w : S.dom)
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun ω => F ((u : Lp ℝ 2 μ) ω)) :
    S.energy.E w w ≤ (L : ℝ)^2 * S.energy.E u u := by
  have hchain := S.chain_diagonal hF hL u w hw
  have hle : ⇑(S.Γ w w) ≤ᵐ[μ] fun ω => (L : ℝ)^2 * S.Γ u u ω := by
    filter_upwards [hchain, S.Γ_nonneg u] with ω he hp
    rw [he]
    apply mul_le_mul_of_nonneg_right _ hp
    have hb := norm_deriv_le_of_lipschitz (𝕜 := ℝ) hL (x₀ := (u : Lp ℝ 2 μ) ω)
    rw [Real.norm_eq_abs] at hb
    nlinarith [sq_abs (deriv F ((u : Lp ℝ 2 μ) ω)), abs_nonneg (deriv F ((u : Lp ℝ 2 μ) ω)), L.coe_nonneg]
  have hi := integral_mono_ae (L1.integrable_coeFn (S.Γ w w))
    ((L1.integrable_coeFn (S.Γ u u)).const_mul ((L : ℝ)^2)) hle
  rw [integral_const_mul] at hi
  simp only [ErrorData.energy_apply]
  nlinarith

end ErrorCalculus.ErrorStructure
