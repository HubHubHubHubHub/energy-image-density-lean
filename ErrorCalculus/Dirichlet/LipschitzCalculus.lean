import ErrorCalculus.Dirichlet.LipschitzRegularize
import ErrorCalculus.Dirichlet.LipschitzLimits
import Mathlib.Analysis.Calculus.Deriv.Abs

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- B.4, with the analytic derivative-convergence step exposed as a separate hypothesis. -/
theorem lipschitz_calculus_of_deriv_tendsto {u : S.dom} (hu : S.HasEID u)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hderiv : ∀ᵐ x ∂volume,
      Tendsto (fun n => deriv (lipschitzMollify F n) x) atTop (𝓝 (deriv F x)))
    (z : Lp ℝ 2 μ) (hz : ⇑z =ᵐ[μ] fun ω => F (S.representative u ω)) :
    ∃ hz' : z ∈ S.dom, ∀ v : S.dom,
      ⇑(S.Γ ⟨z,hz'⟩ v) =ᵐ[μ] fun ω => deriv F (S.representative u ω) * S.Γ u v ω := by
  let f := lipschitzMollify F
  have hf n : MemLp (fun ω => f n (S.representative u ω)) 2 μ :=
    S.scalar_composition_memLp u (lipschitzMollify_lipschitz hF n)
  let q n := (hf n).toLp _
  have hq n : ⇑(q n) =ᵐ[μ] fun ω => f n (S.representative u ω) := (hf n).coeFn_toLp
  have hchain n : ∃ hd : q n ∈ S.dom, ∀ v : S.dom,
      ⇑(S.Γ ⟨q n,hd⟩ v) =ᵐ[μ]
        fun ω => deriv (f n) (S.representative u ω) * S.Γ u v ω := by
    have hrep : ⇑(q n) =ᵐ[μ] fun ω => f n ((u : Lp ℝ 2 μ) ω) := by
      filter_upwards [hq n, S.coeFn_representative u] with ω h1 h2
      rw [h1, h2]
    obtain ⟨hd, he⟩ := S.chain_one ((lipschitzMollify_contDiff hF n).of_le (by simp))
      (lipschitzMollify_lipschitz hF n) u (q n) hrep
    refine ⟨hd, fun v => ?_⟩
    filter_upwards [he v, S.coeFn_representative u] with ω h1 h2
    simpa only [h2] using h1
  choose hd hdchain using hchain
  let w : ℕ → S.dom := fun n => ⟨q n, hd n⟩
  let a n := S.energyCoefficient u (deriv (f n))
  let b := S.energyCoefficient u (deriv F)
  have ha n : MemLp (a n) ∞ μ := S.energyCoefficient_memLp u
    (measurable_deriv (f n)) L.coe_nonneg (abs_deriv_lipschitzMollify_le hF n)
  have hb : MemLp b ∞ μ := S.energyCoefficient_memLp u (measurable_deriv F)
    L.coe_nonneg (fun _ => norm_deriv_le_of_lipschitz (𝕜 := ℝ) hF)
  have hCa n : ∀ᵐ ω ∂μ, |a n ω| ≤ (L:ℝ) := ae_of_all _
    (S.abs_energyCoefficient_le u L.coe_nonneg (abs_deriv_lipschitzMollify_le hF n))
  have hCb : ∀ᵐ ω ∂μ, |b ω| ≤ (L:ℝ) := ae_of_all _
    (S.abs_energyCoefficient_le u L.coe_nonneg
      (fun _ => norm_deriv_le_of_lipschitz (𝕜 := ℝ) hF))
  have hab : ∀ᵐ ω ∂μ, Tendsto (fun n => a n ω) atTop (𝓝 (b ω)) :=
    hu.energyCoefficient_tendsto S hderiv
  have hw n v : ⇑(S.Γ (w n) v) =ᵐ[μ] fun ω => a n ω * S.Γ u v ω :=
    (hdchain n v).trans (S.energyCoefficient_mul_gamma u v (deriv (f n))).symm
  have hconv : Tendsto (fun n => (w n : Lp ℝ 2 μ)) atTop (𝓝 z) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hbound n : ‖(w n : Lp ℝ 2 μ)-z‖ ≤
        ((L:ℝ) * (1/2:ℝ)^n) * ‖Lp.const 2 μ (1:ℝ)‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub (q n) z, hq n, hz,
        Lp.coeFn_const (p := 2) (μ := μ) (c := (1:ℝ))] with ω hs hq hz hc
      change ‖(q n-z) ω‖ ≤ _
      simp only [hs, Pi.sub_apply, hq, hz, hc, Function.const_apply, norm_one, mul_one, Real.norm_eq_abs]
      exact abs_lipschitzMollify_sub_le hF n _
    have ht : Tendsto (fun n : ℕ => ((L:ℝ) * (1/2:ℝ)^n) * ‖Lp.const 2 μ (1:ℝ)‖)
        atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul (L:ℝ)).mul_const
          ‖Lp.const 2 μ (1:ℝ)‖
    exact squeeze_zero (fun _ => norm_nonneg _) hbound ht
  obtain ⟨hz', he⟩ := S.closed_scalar_chain u w z a b ha hb L.coe_nonneg hCa hCb hab hw hconv
  exact ⟨hz', fun v => (he v).trans (S.energyCoefficient_mul_gamma u v (deriv F))⟩

/-- scalar Lipschitz functional calculus under energy image density. -/
theorem lipschitz_calculus {u : S.dom} (hu : S.HasEID u)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (w : Lp ℝ 2 μ) (hw : ⇑w =ᵐ[μ] fun ω => F (S.representative u ω)) :
    ∃ hw' : w ∈ S.dom, ∀ v : S.dom,
      ⇑(S.Γ ⟨w,hw'⟩ v) =ᵐ[μ] fun ω => deriv F (S.representative u ω) * S.Γ u v ω :=
  S.lipschitz_calculus_of_deriv_tendsto hu hF (deriv_lipschitzMollify_tendsto_ae hF) w hw

/-- diagonal formula, with no differentiability assumption on F. -/
theorem lipschitz_calculus_diag {u : S.dom} (hu : S.HasEID u)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (w : S.dom)
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun ω => F (S.representative u ω)) :
    ⇑(S.Γ w w) =ᵐ[μ] fun ω => (deriv F (S.representative u ω))^2 * S.Γ u u ω := by
  obtain ⟨hd, he⟩ := S.lipschitz_calculus hu hF w hw
  have h1 := he w
  have h2 := he u
  have hsym := S.Γ_symm u w
  filter_upwards [h1, h2] with ω hω hω'
  change S.Γ w w ω = _ at hω
  change S.Γ w u ω = _ at hω'
  rw [hω, hsym, hω']
  ring

/-- The sharp energy contraction constant L². -/
theorem lipschitz_energy_le {u : S.dom} (hu : S.HasEID u)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (w : S.dom)
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun ω => F (S.representative u ω)) :
    S.energy.E w w ≤ (L:ℝ)^2 * S.energy.E u u := by
  have hchain := S.lipschitz_calculus_diag hu hF w hw
  have hle : ⇑(S.Γ w w) ≤ᵐ[μ] fun ω => (L:ℝ)^2 * S.Γ u u ω := by
    filter_upwards [hchain, S.Γ_nonneg u] with ω he hp
    rw [he]
    apply mul_le_mul_of_nonneg_right _ hp
    have hb := norm_deriv_le_of_lipschitz (𝕜 := ℝ) hF (x₀ := S.representative u ω)
    rw [Real.norm_eq_abs] at hb
    nlinarith [sq_abs (deriv F (S.representative u ω)),
      abs_nonneg (deriv F (S.representative u ω)), L.coe_nonneg]
  have hi := integral_mono_ae (L1.integrable_coeFn (S.Γ w w))
    ((L1.integrable_coeFn (S.Γ u u)).const_mul ((L:ℝ)^2)) hle
  rw [integral_const_mul] at hi
  simp only [ErrorData.energy_apply]
  nlinarith

/-- |u| is in the domain under EID. -/
theorem abs_mem_dom {u : S.dom} (hu : S.HasEID u) : |(u : Lp ℝ 2 μ)| ∈ S.dom := by
  have hF : LipschitzWith 1 (fun x : ℝ => |x|) := lipschitzWith_one_norm
  apply (S.lipschitz_calculus hu hF |(u : Lp ℝ 2 μ)| ?_).choose
  filter_upwards [Lp.coeFn_abs (u : Lp ℝ 2 μ), S.coeFn_representative u] with ω ha hr
  simp only [ha, hr]

/-- The positive part is in the domain under EID. -/
theorem posPart_mem_dom {u : S.dom} (hu : S.HasEID u) :
    ((u : Lp ℝ 2 μ) ⊔ 0) ∈ S.dom := by
  have hF : LipschitzWith 1 (fun x : ℝ => max x 0) := LipschitzWith.id.max_const 0
  apply (S.lipschitz_calculus hu hF ((u : Lp ℝ 2 μ) ⊔ 0) ?_).choose
  filter_upwards [Lp.coeFn_sup (u : Lp ℝ 2 μ) 0, Lp.coeFn_zero ℝ 2 μ,
    S.coeFn_representative u] with ω hs hz hr
  simp only [hs, Pi.sup_apply, hz, Pi.zero_apply, hr]

/-- taking absolute values preserves the carré du champ. -/
theorem gamma_abs {u : S.dom} (hu : S.HasEID u) :
    S.Γ ⟨|(u : Lp ℝ 2 μ)|, S.abs_mem_dom hu⟩ ⟨|(u : Lp ℝ 2 μ)|, S.abs_mem_dom hu⟩ =
      S.Γ u u := by
  have hF : LipschitzWith 1 (fun x : ℝ => |x|) := lipschitzWith_one_norm
  have hw : ⇑(|(u : Lp ℝ 2 μ)|) =ᵐ[μ] fun ω => |S.representative u ω| := by
    filter_upwards [Lp.coeFn_abs (u : Lp ℝ 2 μ), S.coeFn_representative u] with ω ha hr
    simp only [ha, hr]
  have hd := S.lipschitz_calculus_diag hu hF ⟨|(u : Lp ℝ 2 μ)|, S.abs_mem_dom hu⟩ hw
  have hzero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := volume.ae_ne 0
  apply Lp.ext
  filter_upwards [hd, hu.ae_of_ae_volume S hzero] with ω hd hz
  rw [hd]
  by_cases he : S.Γ u u ω = 0
  · simp [he]
  · have hx := hz he
    rcases lt_or_gt_of_ne hx with hn | hp
    · rw [deriv_abs_neg hn]
      ring
    · rw [deriv_abs_pos hp]
      ring

/-- The paper's Γ_abs notation, as an almost everywhere identity. -/
theorem Γ_abs {u : S.dom} (hu : S.HasEID u) :
    ⇑(S.Γ ⟨|(u : Lp ℝ 2 μ)|, S.abs_mem_dom hu⟩
      ⟨|(u : Lp ℝ 2 μ)|, S.abs_mem_dom hu⟩) =ᵐ[μ] ⇑(S.Γ u u) := by
  rw [S.gamma_abs hu]

end ErrorCalculus.ErrorStructure
