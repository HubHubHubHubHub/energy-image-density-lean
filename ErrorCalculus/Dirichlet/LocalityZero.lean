import ErrorCalculus.Dirichlet.LocalityApproximation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus.ErrorStructure

/-- The bounded smooth probe of the zero level. -/
def arctanScale (ε x : ℝ) : ℝ := ε * Real.arctan (x/ε)

theorem contDiff_arctanScale (ε : ℝ) : ContDiff ℝ 1 (arctanScale ε) :=
  contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_id.div_const ε))

theorem deriv_arctanScale {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    deriv (arctanScale ε) x = 1 / (1+x^2/ε^2) := by
  have h := (((hasDerivAt_id x).div_const ε).arctan.const_mul ε).deriv
  change deriv (arctanScale ε) x = _ at h
  rw [h]
  simp only [div_pow, id_eq]
  field_simp

theorem deriv_arctanScale_pos_le_one {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    0 < deriv (arctanScale ε) x ∧ deriv (arctanScale ε) x ≤ 1 := by
  rw [deriv_arctanScale hε]
  have hp : 0 ≤ x^2/ε^2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  constructor
  · positivity
  · exact (div_le_one (by positivity)).mpr (by linarith)

theorem lipschitzWith_one_arctanScale {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith 1 (arctanScale ε) := by
  apply lipschitzWith_of_contDiff_deriv_bound (contDiff_arctanScale ε)
  intro x
  rw [abs_of_pos (deriv_arctanScale_pos_le_one hε.ne' x).1]
  exact (deriv_arctanScale_pos_le_one hε.ne' x).2

theorem abs_arctanScale_le {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    |arctanScale ε x| ≤ ε * (Real.pi/2) := by
  rw [arctanScale, abs_mul, abs_of_nonneg hε]
  apply mul_le_mul_of_nonneg_left _ hε
  exact (abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le,
    (Real.arctan_lt_pi_div_two _).le⟩)

/-- Pointwise convergence in the scale parameter, with no subsequence. -/
theorem tendsto_deriv_arctanScale {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ᶠ i in l, 0 < ε i) (ht : Tendsto ε l (𝓝 0)) (x : ℝ) :
    Tendsto (fun i => deriv (arctanScale (ε i)) x) l (𝓝 (if x = 0 then 1 else 0)) := by
  split_ifs with hx
  · apply tendsto_const_nhds.congr'
    filter_upwards [hε] with i hi
    simp [deriv_arctanScale hi.ne', hx]
  · have hh := (ht.pow 2).div ((ht.pow 2).add_const (x^2)) (by simpa using pow_ne_zero 2 hx)
    simp only [zero_pow (by decide : 2 ≠ 0), zero_add, zero_div] at hh
    apply hh.congr'
    filter_upwards [hε] with i hi
    change (ε i)^2 / ((ε i)^2+x^2) = deriv (arctanScale (ε i)) x
    rw [deriv_arctanScale hi.ne']
    have hden : (ε i)^2+x^2 ≠ 0 := ne_of_gt (by nlinarith [sq_pos_of_ne_zero hi.ne', sq_nonneg x])
    have hs : (ε i)^2 ≠ 0 := pow_ne_zero _ hi.ne'
    field_simp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- Canonical probe sequence, at scales 1/(n+1). -/
def arctanScaleComp (u : S.dom) (n : ℕ) : S.dom :=
  S.lipschitzComp (lipschitzWith_one_arctanScale (by positivity : 0 < 1/((n:ℝ)+1))) u

theorem tendsto_arctanScale_comp_L2 (u : S.dom) :
    Tendsto (fun n => (S.arctanScaleComp u n : Lp ℝ 2 μ)) atTop (𝓝 0) := by
  apply tendsto_Lp_of_uniform_error
    (e := fun n => (1/((n:ℝ)+1)) * (Real.pi/2))
  · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (Real.pi/2)
  · intro n
    filter_upwards [S.coeFn_lipschitzComp
      (lipschitzWith_one_arctanScale (by positivity : 0 < 1/((n:ℝ)+1))) u,
      Lp.coeFn_zero ℝ 2 μ] with ω hc hz
    simpa only [arctanScaleComp, hc, hz, Pi.zero_apply, sub_zero] using
      abs_arctanScale_le (by positivity : 0 ≤ 1/((n:ℝ)+1)) ((u : Lp ℝ 2 μ) ω)

theorem cauchySeq_arctanScale_comp (u : S.dom) :
    CauchySeq (fun n => S.energy.formToDomain.symm (S.arctanScaleComp u n)) := by
  apply S.cauchySeq_comp_of_deriv_tendsto
    (fun n => contDiff_arctanScale (1/((n:ℝ)+1)))
    (fun n => lipschitzWith_one_arctanScale (by positivity)) u
    (S.tendsto_arctanScale_comp_L2 u)
    (d := fun ω => if (u : Lp ℝ 2 μ) ω = 0 then 1 else 0)
  exact ae_of_all _ fun ω => Or.inr (tendsto_deriv_arctanScale
    (Eventually.of_forall fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat _)

theorem tendsto_arctanScale_comp_formSpace (u : S.dom) :
    Tendsto (fun n => S.energy.formToDomain.symm (S.arctanScaleComp u n)) atTop (𝓝 0) := by
  simpa using S.tendsto_formSpace_of_cauchySeq (v := 0)
    (S.cauchySeq_arctanScale_comp u) (S.tendsto_arctanScale_comp_L2 u)

/-- Continuity of energy at the zero form limit. -/
theorem tendsto_energy_arctanScale_comp_zero (u : S.dom) :
    Tendsto (fun n => S.energy.E (S.arctanScaleComp u n) (S.arctanScaleComp u n))
      atTop (𝓝 0) := by
  have ht := S.tendsto_arctanScale_comp_formSpace u
  have he := (S.energy.continuous_energy_formSpace.tendsto (0,0)).comp (ht.prodMk_nhds ht)
  simpa only [Function.comp_def, LinearEquiv.apply_symm_apply, map_zero] using he

/-- The energy tends to half the mass of Γ on the zero level. -/
theorem tendsto_energy_arctanScale_comp (u : S.dom) :
    Tendsto (fun n => S.energy.E (S.arctanScaleComp u n) (S.arctanScaleComp u n))
      atTop (𝓝 ((1/2:ℝ) * ∫ ω, if (u : Lp ℝ 2 μ) ω = 0 then S.Γ u u ω else 0 ∂μ)) := by
  have ht := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n ω => (deriv (arctanScale (1/((n:ℝ)+1))) ((u : Lp ℝ 2 μ) ω))^2 * S.Γ u u ω)
    (f := fun ω => if (u : Lp ℝ 2 μ) ω = 0 then S.Γ u u ω else 0)
    (fun ω => ‖S.Γ u u ω‖)
    (fun n => ((((contDiff_arctanScale _).continuous_deriv (by norm_num)).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable _)).pow 2).mul (Lp.aestronglyMeasurable _))
    (L1.integrable_coeFn _).norm ?_ ?_
  · have he n : S.energy.E (S.arctanScaleComp u n) (S.arctanScaleComp u n) =
        (1/2:ℝ) * ∫ ω, (deriv (arctanScale (1/((n:ℝ)+1))) ((u : Lp ℝ 2 μ) ω))^2 * S.Γ u u ω ∂μ := by
      rw [ErrorData.energy_apply]
      congr 1
      exact integral_congr_ae (S.chain_diagonal
        (contDiff_arctanScale (1/((n:ℝ)+1)))
        (lipschitzWith_one_arctanScale (by positivity : 0 < 1/((n:ℝ)+1))) u _
        (S.coeFn_lipschitzComp _ u))
    simpa only [he] using ht.const_mul (1/2:ℝ)
  · intro n
    filter_upwards [] with ω
    rw [norm_mul, Real.norm_eq_abs, abs_pow, sq_abs]
    have hb := deriv_arctanScale_pos_le_one (by positivity : (1/((n:ℝ)+1)) ≠ 0)
      ((u : Lp ℝ 2 μ) ω)
    have hs : (deriv (arctanScale (1/((n:ℝ)+1))) ((u : Lp ℝ 2 μ) ω))^2 ≤ 1 := by nlinarith
    simpa using mul_le_mul_of_nonneg_right hs (norm_nonneg (S.Γ u u ω))
  · filter_upwards [] with ω
    have h := (tendsto_deriv_arctanScale
      (Eventually.of_forall fun n : ℕ => by positivity : ∀ᶠ n : ℕ in atTop, 0 < 1/((n:ℝ)+1))
      tendsto_one_div_add_atTop_nhds_zero_nat ((u : Lp ℝ 2 μ) ω)).pow 2 |>.mul_const (S.Γ u u ω)
    split_ifs at h ⊢ <;> simpa using h

/-- AB.1: the carré du champ vanishes on the zero level of every domain element. -/
theorem gamma_eq_zero_on_zero (u : S.dom) :
    ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω = 0 → S.Γ u u ω = 0 := by
  have hz := tendsto_nhds_unique (S.tendsto_energy_arctanScale_comp u)
    (S.tendsto_energy_arctanScale_comp_zero u)
  have hi : Integrable (fun ω => if (u : Lp ℝ 2 μ) ω = 0 then S.Γ u u ω else 0) μ := by
    exact (L1.integrable_coeFn (S.Γ u u)).indicator ((Lp.stronglyMeasurable u.val).measurable (measurableSet_singleton 0))
  have hn : ∀ᵐ ω ∂μ, 0 ≤ (if (u : Lp ℝ 2 μ) ω = 0 then S.Γ u u ω else 0) := by
    filter_upwards [S.Γ_nonneg u] with ω hω
    change 0 ≤ S.Γ u u ω at hω
    split_ifs
    · exact hω
    · exact le_rfl
  have hh := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp (by linarith :
    (∫ ω, if (u : Lp ℝ 2 μ) ω = 0 then S.Γ u u ω else 0 ∂μ) = 0)
  filter_upwards [hh] with ω hω hu
  simpa only [hu, if_pos, Pi.zero_apply] using hω

/-- Mixed locality follows from pointwise Cauchy–Schwarz. -/
theorem gamma_mixed_eq_zero_on_eq (u v w : S.dom) :
    ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω = (v : Lp ℝ 2 μ) ω → S.Γ (u-v) w ω = 0 := by
  filter_upwards [S.gamma_eq_zero_on_zero (u-v),
    S.toErrorData.gamma_cauchy_schwarz (u-v) w,
    Lp.coeFn_sub (u : Lp ℝ 2 μ) (v : Lp ℝ 2 μ)] with ω hz hc hs he
  have hd : ((u-v : S.dom) : Lp ℝ 2 μ) ω = 0 := by
    simp only [Submodule.coe_sub, hs, Pi.sub_apply, he, sub_self]
  rw [hz hd, zero_mul] at hc
  nlinarith [sq_nonneg (S.Γ (u-v) w ω)]

/-- AB.1(f): equal functions have equal carré du champ on their equality set. -/
theorem gamma_eq_on_eq (u v : S.dom) :
    ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω = (v : Lp ℝ 2 μ) ω → S.Γ u u ω = S.Γ v v ω := by
  have he : S.Γ (u-v) (u+v) = S.Γ u u - S.Γ v v := by
    simp only [map_sub, map_add, LinearMap.sub_apply, S.Γ_symm v u]
    module
  filter_upwards [S.gamma_mixed_eq_zero_on_eq u v (u+v),
    Lp.coeFn_sub (S.Γ u u) (S.Γ v v)] with ω hm hs hu
  have hh := hm hu
  rw [he, hs] at hh
  exact sub_eq_zero.mp hh

/-- Every constant level carries zero energy density. -/
theorem gamma_eq_zero_on_const (u : S.dom) (c : ℝ) :
    ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω = c → S.Γ u u ω = 0 := by
  filter_upwards [S.gamma_eq_on_eq u (S.const c),
    Lp.coeFn_const (p := 2) (μ := μ) (c := c), Lp.coeFn_zero ℝ 1 μ] with ω he hc hz hu
  have hh := he (hu.trans hc.symm)
  simpa only [S.gamma_const, hz, Pi.zero_apply] using hh

/-- A countable union of levels still carries zero energy density. -/
theorem gamma_eq_zero_on_countable (u : S.dom) {D : Set ℝ} (hD : D.Countable) :
    ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ D → S.Γ u u ω = 0 := by
  letI := hD.toEncodable
  have h := ae_all_iff.mpr (fun c : D => S.gamma_eq_zero_on_const u c)
  filter_upwards [h] with ω hω hmem
  exact hω ⟨_, hmem⟩ rfl

end ErrorCalculus.ErrorStructure
