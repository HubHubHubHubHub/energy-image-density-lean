import ErrorCalculus.Dirichlet.BoundedDenseStrong
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- The mixed scalar chain rule for the canonical composition. -/
theorem gamma_lipschitzComp {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) (u v : S.dom) :
    S.Γ (S.lipschitzComp hL u) v =ᵐ[μ]
      fun ω => deriv F ((u : Lp ℝ 2 μ) ω) * S.Γ u v ω :=
  (S.chain_one hF hL u _ (S.coeFn_lipschitzComp hL u)).choose_spec v

/-- Bilinearity of the carré du champ on a difference, pointwise almost everywhere. -/
theorem gamma_sub_ae (u v : S.dom) :
    S.Γ (u-v) (u-v) =ᵐ[μ]
      fun ω => S.Γ u u ω - 2 * S.Γ u v ω + S.Γ v v ω := by
  have he : S.Γ (u-v) (u-v) = (S.Γ u u - S.Γ u v) - (S.Γ v u - S.Γ v v) := by
    simp only [map_sub, LinearMap.sub_apply, S.Γ_symm v u]
  rw [he, S.Γ_symm v u]
  filter_upwards [Lp.coeFn_sub (S.Γ u u - S.Γ u v) (S.Γ u v - S.Γ v v),
    Lp.coeFn_sub (S.Γ u u) (S.Γ u v), Lp.coeFn_sub (S.Γ u v) (S.Γ v v)] with ω h1 h2 h3
  simp only [h1, h2, h3, Pi.sub_apply]
  ring

/-- AA.1(a): the two-variable difference formula. The two scalar instances of
`calc` and bilinearity give the chain rule for G(x,y) = F(x) - F(y). -/
theorem gamma_lipschitzComp_sub {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) (u v : S.dom) :
    S.Γ (S.lipschitzComp hL u - S.lipschitzComp hL v)
      (S.lipschitzComp hL u - S.lipschitzComp hL v) =ᵐ[μ] fun ω =>
      deriv F ((u : Lp ℝ 2 μ) ω)^2 * S.Γ u u ω -
      2 * deriv F ((u : Lp ℝ 2 μ) ω) * deriv F ((v : Lp ℝ 2 μ) ω) * S.Γ u v ω +
      deriv F ((v : Lp ℝ 2 μ) ω)^2 * S.Γ v v ω := by
  filter_upwards [S.gamma_sub_ae (S.lipschitzComp hL u) (S.lipschitzComp hL v),
    S.chain_diagonal hF hL u _ (S.coeFn_lipschitzComp hL u),
    S.chain_diagonal hF hL v _ (S.coeFn_lipschitzComp hL v),
    S.gamma_lipschitzComp hF hL u (S.lipschitzComp hL v),
    S.gamma_lipschitzComp hF hL v u] with ω hs hu hv huv hvu
  rw [S.Γ_symm u (S.lipschitzComp hL v), hvu, S.Γ_symm v u] at huv
  rw [hs, hu, hv, huv]
  ring

/-- AA.1(b): the decomposition into two small carré du champ terms and one
fixed integrable weight. -/
theorem gamma_lipschitzComp_sub_decomposition {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) (u v : S.dom) :
    S.Γ (S.lipschitzComp hL u - S.lipschitzComp hL v)
      (S.lipschitzComp hL u - S.lipschitzComp hL v) =ᵐ[μ] fun ω =>
      deriv F ((u : Lp ℝ 2 μ) ω)^2 * S.Γ (u-v) (u-v) ω +
      2 * deriv F ((u : Lp ℝ 2 μ) ω) *
        (deriv F ((u : Lp ℝ 2 μ) ω) - deriv F ((v : Lp ℝ 2 μ) ω)) * S.Γ (u-v) v ω +
      (deriv F ((u : Lp ℝ 2 μ) ω) - deriv F ((v : Lp ℝ 2 μ) ω))^2 * S.Γ v v ω := by
  have hm : S.Γ (u-v) v = S.Γ u v - S.Γ v v := by simp
  filter_upwards [S.gamma_lipschitzComp_sub hF hL u v, S.gamma_sub_ae u v,
    Lp.coeFn_sub (S.Γ u v) (S.Γ v v)] with ω h1 h2 h3
  rw [h1, h2, hm, h3]
  simp only [Pi.sub_apply]
  ring

omit [IsProbabilityMeasure μ] in
/-- Uniformly bounded continuous coefficients converge against a fixed L¹ weight.
The proof extracts an almost everywhere convergent sub-subsequence from each
subsequence; no uniform continuity of the coefficient is assumed. -/
theorem tendsto_integral_bounded_coefficient {q : ℕ → Lp ℝ 2 μ} {v : Lp ℝ 2 μ}
    (hq : Tendsto q atTop (𝓝 v)) {A : ℝ → ℝ} (hA : Continuous A)
    {C : ℝ} (hC : ∀ x, |A x| ≤ C) (g : Lp ℝ 1 μ) :
    Tendsto (fun n => ∫ ω, (A (q n ω) - A (v ω))^2 * g ω ∂μ) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp (hq.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hb x y : |A x - A y| ≤ 2*C := by
    exact (abs_sub _ _).trans (by linarith [hC x, hC y])
  have hd := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n ω => (A (q (ns (ms n)) ω) - A (v ω))^2 * g ω)
    (f := fun _ => (0 : ℝ)) (fun ω => (2*C)^2 * ‖g ω‖)
    (fun n => (((hA.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)).sub
      (hA.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))).pow 2).mul
      (Lp.aestronglyMeasurable g))
    ((L1.integrable_coeFn g).norm.const_mul _) ?_ ?_
  · simpa using hd
  · intro n
    filter_upwards [] with ω
    rw [norm_mul, Real.norm_eq_abs, abs_pow, sq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    nlinarith [sq_abs (A (q (ns (ms n)) ω) - A (v ω)),
      hb (q (ns (ms n)) ω) (v ω), abs_nonneg (A (q (ns (ms n)) ω) - A (v ω))]
  · filter_upwards [hae] with ω hω
    simpa using (((hA.tendsto _).comp hω).sub_const (A (v ω))).pow 2 |>.mul_const (g ω)

/-- The scalar Lipschitz calculus is Lipschitz in the ambient L² norm. -/
theorem norm_lipschitzComp_sub_le {F : ℝ → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L F) (u v : S.dom) :
    ‖((S.lipschitzComp hL u - S.lipschitzComp hL v : S.dom) : Lp ℝ 2 μ)‖ ≤
      (L : ℝ) * ‖((u-v : S.dom) : Lp ℝ 2 μ)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (S.lipschitzComp hL u : Lp ℝ 2 μ)
    (S.lipschitzComp hL v : Lp ℝ 2 μ), S.coeFn_lipschitzComp hL u,
    S.coeFn_lipschitzComp hL v, Lp.coeFn_sub (u : Lp ℝ 2 μ) (v : Lp ℝ 2 μ)] with ω hs hu hv hd
  simpa only [Submodule.coe_sub, hs, Pi.sub_apply, hu, hv, hd, ← dist_eq_norm] using
    hL.dist_le_mul ((u : Lp ℝ 2 μ) ω) ((v : Lp ℝ 2 μ) ω)

/-- Bounds for the two derivative coefficients in the decomposition. -/
theorem deriv_coefficients_le {F : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F) (x y : ℝ) :
    (deriv F x)^2 ≤ (L : ℝ)^2 ∧
    |2 * deriv F x * (deriv F x - deriv F y)| ≤ 4*(L : ℝ)^2 ∧
    (deriv F x - deriv F y)^2 ≤ 4*(L : ℝ)^2 := by
  have hx : |deriv F x| ≤ L := norm_deriv_le_of_lipschitz (𝕜 := ℝ) hL
  have hy : |deriv F y| ≤ L := norm_deriv_le_of_lipschitz (𝕜 := ℝ) hL
  have hd : |deriv F x - deriv F y| ≤ 2*(L : ℝ) :=
    (abs_sub _ _).trans (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [sq_abs (deriv F x), abs_nonneg (deriv F x), L.coe_nonneg]
  · rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    calc
      2 * |deriv F x| * |deriv F x - deriv F y| ≤ 2 * (L : ℝ) * (2 * (L : ℝ)) :=
        mul_le_mul (by linarith) hd (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · nlinarith [sq_abs (deriv F x - deriv F y), abs_nonneg (deriv F x - deriv F y), L.coe_nonneg]

/-- The fixed-weight remainder is integrable. -/
theorem integrable_deriv_remainder {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) (u v : S.dom) :
    Integrable (fun ω => (deriv F ((u : Lp ℝ 2 μ) ω) -
      deriv F ((v : Lp ℝ 2 μ) ω))^2 * S.Γ v v ω) μ := by
  apply ((L1.integrable_coeFn (S.Γ v v)).const_mul (4*(L : ℝ)^2)).mono'
  · exact ((((hF.continuous_deriv (by norm_num)).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable _)).sub
      ((hF.continuous_deriv (by norm_num)).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable _))).pow 2).mul (Lp.aestronglyMeasurable _)
  · filter_upwards [S.Γ_nonneg v] with ω hv
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hv]
    exact mul_le_mul_of_nonneg_right (deriv_coefficients_le hL _ _).2.2 hv

/-- Quantitative L¹ estimate for the difference of two compositions. -/
theorem norm_gamma_lipschitzComp_sub_le {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) (u v : S.dom) :
    ‖S.Γ (S.lipschitzComp hL u - S.lipschitzComp hL v)
      (S.lipschitzComp hL u - S.lipschitzComp hL v)‖ ≤
      (L : ℝ)^2 * ‖S.Γ (u-v) (u-v)‖ + 4*(L : ℝ)^2 * ‖S.Γ (u-v) v‖ +
      ∫ ω, (deriv F ((u : Lp ℝ 2 μ) ω) - deriv F ((v : Lp ℝ 2 μ) ω))^2 * S.Γ v v ω ∂μ := by
  rw [L1.norm_eq_integral_norm]
  have h1 := (L1.integrable_coeFn (S.Γ (u-v) (u-v))).norm.const_mul ((L : ℝ)^2)
  have h2 := (L1.integrable_coeFn (S.Γ (u-v) v)).norm.const_mul (4*(L : ℝ)^2)
  have h3 := S.integrable_deriv_remainder hF hL u v
  have h12 : Integrable (fun ω => (L : ℝ)^2 * ‖S.Γ (u-v) (u-v) ω‖ +
      4*(L : ℝ)^2 * ‖S.Γ (u-v) v ω‖) μ := h1.add h2
  calc
    _ ≤ ∫ ω, ((L : ℝ)^2 * ‖S.Γ (u-v) (u-v) ω‖ +
        4*(L : ℝ)^2 * ‖S.Γ (u-v) v ω‖ +
        (deriv F ((u : Lp ℝ 2 μ) ω) - deriv F ((v : Lp ℝ 2 μ) ω))^2 * S.Γ v v ω) ∂μ := by
      apply integral_mono_ae (L1.integrable_coeFn _).norm ((h1.add h2).add h3)
      filter_upwards [S.gamma_lipschitzComp_sub_decomposition hF hL u v,
        S.Γ_nonneg (S.lipschitzComp hL u - S.lipschitzComp hL v),
        S.Γ_nonneg (u-v)] with ω he hp hd
      rw [Real.norm_of_nonneg hp, he]
      have hh := deriv_coefficients_le hL ((u : Lp ℝ 2 μ) ω) ((v : Lp ℝ 2 μ) ω)
      simp only [Pi.add_apply]
      apply add_le_add _ le_rfl
      apply add_le_add
      · rw [Real.norm_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right hh.1 hd
      · exact (le_abs_self _).trans (by
          rw [abs_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right hh.2.1 (abs_nonneg _))
    _ = _ := by
      rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul,
        integral_const_mul, ← L1.norm_eq_integral_norm, ← L1.norm_eq_integral_norm]

/-- AA.1(b): the carré du champ of the composition error tends to zero in L¹. -/
theorem tendsto_gamma_lipschitzComp_sub {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) {u : ℕ → S.dom} {v : S.dom}
    (hu : Tendsto (fun n => S.energy.formToDomain.symm (u n)) atTop
      (𝓝 (S.energy.formToDomain.symm v))) :
    Tendsto (fun n => S.Γ (S.lipschitzComp hL (u n) - S.lipschitzComp hL v)
      (S.lipschitzComp hL (u n) - S.lipschitzComp hL v)) atTop (𝓝 0) := by
  have hd : Tendsto (fun n => S.energy.formToDomain.symm (u n-v)) atTop (𝓝 0) := by
    simpa only [map_sub, sub_self] using hu.sub_const (S.energy.formToDomain.symm v)
  have ht1 := (S.continuous_gamma_formSpace.tendsto (0,0)).comp (hd.prodMk_nhds hd)
  have ht2 := (S.continuous_gamma_formSpace.tendsto (0,S.energy.formToDomain.symm v)).comp
    (hd.prodMk_nhds tendsto_const_nhds)
  simp only [Function.comp_def, map_zero, LinearMap.zero_apply,
    LinearEquiv.apply_symm_apply] at ht1 ht2
  have hl2 : Tendsto (fun n => (u n : Lp ℝ 2 μ)) atTop (𝓝 (v : Lp ℝ 2 μ)) :=
    S.energy.formInclusion.continuous.tendsto _ |>.comp hu
  have ht3 := tendsto_integral_bounded_coefficient hl2
    (hF.continuous_deriv (by norm_num))
    (fun x => show |deriv F x| ≤ L from norm_deriv_le_of_lipschitz (𝕜 := ℝ) hL) (S.Γ v v)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => S.norm_gamma_lipschitzComp_sub_le hF hL (u n) v)
  simpa only [norm_zero, mul_zero, zero_add] using
    ((ht1.norm.const_mul ((L : ℝ)^2)).add (ht2.norm.const_mul (4*(L : ℝ)^2))).add ht3

/-- AA.1(c): scalar C¹ Lipschitz calculus preserves convergence in the form norm. -/
theorem tendsto_lipschitzComp_formSpace {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) {u : ℕ → S.dom} {v : S.dom}
    (hu : Tendsto (fun n => S.energy.formToDomain.symm (u n)) atTop
      (𝓝 (S.energy.formToDomain.symm v))) :
    Tendsto (fun n => S.energy.formToDomain.symm (S.lipschitzComp hL (u n))) atTop
      (𝓝 (S.energy.formToDomain.symm (S.lipschitzComp hL v))) := by
  have hl2 : Tendsto (fun n => (u n : Lp ℝ 2 μ)) atTop (𝓝 (v : Lp ℝ 2 μ)) :=
    S.energy.formInclusion.continuous.tendsto _ |>.comp hu
  have he := (S.tendsto_gamma_lipschitzComp_sub hF hL hu).norm
  simp only [norm_zero, S.toErrorData.norm_gamma_self] at he
  have he' : Tendsto (fun n => S.energy.E
      (S.lipschitzComp hL (u n) - S.lipschitzComp hL v)
      (S.lipschitzComp hL (u n) - S.lipschitzComp hL v)) atTop (𝓝 0) := by
    convert he.const_mul (1/2 : ℝ) using 1 <;> simp
  have ha : Tendsto (fun n => ‖((S.lipschitzComp hL (u n) -
      S.lipschitzComp hL v : S.dom) : Lp ℝ 2 μ)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => S.norm_lipschitzComp_sub_le hL (u n) v)
    simpa using ((hl2.sub_const (v : Lp ℝ 2 μ)).norm.const_mul (L : ℝ))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := ((ha.pow 2).add he').sqrt
  simp_rw [← S.energy.formNorm_sq, QuadForm.formNorm, Real.sqrt_sq (norm_nonneg _)] at ht
  simpa only [← map_sub, zero_pow (by decide : 2 ≠ 0), zero_add, Real.sqrt_zero] using ht

/-- AA.1(d): continuity on the whole form space of every error structure. -/
theorem continuous_lipschitzComp_formSpace {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) :
    Continuous (fun x : S.energy.FormSpace =>
      S.energy.formToDomain.symm (S.lipschitzComp hL (S.energy.formToDomain x))) := by
  apply continuous_iff_seqContinuous.mpr
  intro u v hu
  exact S.tendsto_lipschitzComp_formSpace hF hL hu

/-- The derivative-bound formulation of the scalar hypothesis in AA.1. -/
theorem lipschitzWith_of_contDiff_deriv_bound {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : ∀ x, |deriv F x| ≤ L) : LipschitzWith L F :=
  lipschitzWith_of_nnnorm_deriv_le (hF.differentiable (by norm_num))
    (fun x => by exact_mod_cast hL x)

/-- AA.1(d) stated directly with the bound on F′. -/
theorem continuous_lipschitzComp_formSpace_of_deriv_bound {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : ∀ x, |deriv F x| ≤ L) :
    Continuous (fun x : S.energy.FormSpace => S.energy.formToDomain.symm
      (S.lipschitzComp (lipschitzWith_of_contDiff_deriv_bound hF hL)
        (S.energy.formToDomain x))) :=
  S.continuous_lipschitzComp_formSpace hF _

end ErrorCalculus.ErrorStructure
