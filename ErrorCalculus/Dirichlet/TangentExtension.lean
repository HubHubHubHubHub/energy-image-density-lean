import ErrorCalculus.Dirichlet.IntegralFunctional
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Tangent Extension

## Main results
Tangent continuation, constructed as a primitive of the clipped derivative.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace ErrorCalculus

def tangentExtension (F : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  F a + ∫ s in a..x, deriv F (max a (min s b))

theorem lipschitzWith_clipped {f : ℝ → ℝ} {L : ℝ≥0} {a b : ℝ} (hab : a ≤ b)
    (hf : LipschitzOnWith L f (Icc a b)) :
    LipschitzWith L (fun x => f (max a (min x b))) := by
  have hm (x : ℝ) : max a (min x b) ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hl : LipschitzWith 1 (fun x : ℝ => max a (min x b)) :=
    (LipschitzWith.id.min_const b).const_max a
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (hf.dist_le_mul _ (hm x) _ (hm y)).trans (by
    simpa using mul_le_mul_of_nonneg_left (hl.dist_le_mul x y) L.coe_nonneg)

theorem hasDerivAt_tangentExtension {F : ℝ → ℝ} {L : ℝ≥0} {a b : ℝ} (hab : a ≤ b)
    (hL : LipschitzOnWith L (deriv F) (Icc a b)) (x : ℝ) :
    HasDerivAt (tangentExtension F a b) (deriv F (max a (min x b))) x := by
  have hc := (lipschitzWith_clipped hab hL).continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add (F a)

theorem deriv_tangentExtension {F : ℝ → ℝ} {L : ℝ≥0} {a b : ℝ} (hab : a ≤ b)
    (hL : LipschitzOnWith L (deriv F) (Icc a b)) :
    deriv (tangentExtension F a b) = fun x => deriv F (max a (min x b)) :=
  funext fun x => (hasDerivAt_tangentExtension hab hL x).deriv

theorem lipschitzWith_deriv_tangentExtension {F : ℝ → ℝ} {L : ℝ≥0} {a b : ℝ}
    (hab : a ≤ b) (hL : LipschitzOnWith L (deriv F) (Icc a b)) :
    LipschitzWith L (deriv (tangentExtension F a b)) := by
  rw [deriv_tangentExtension hab hL]
  exact lipschitzWith_clipped hab hL

theorem contDiff_tangentExtension {F : ℝ → ℝ} {L : ℝ≥0} {a b : ℝ} (hab : a ≤ b)
    (hL : LipschitzOnWith L (deriv F) (Icc a b)) :
    ContDiff ℝ 1 (tangentExtension F a b) :=
  contDiff_one_iff_deriv.mpr ⟨fun x => (hasDerivAt_tangentExtension hab hL x).differentiableAt,
    (lipschitzWith_deriv_tangentExtension hab hL).continuous⟩

theorem tangentExtension_eq_on {F : ℝ → ℝ} {L : ℝ≥0} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, DifferentiableAt ℝ F x)
    (hL : LipschitzOnWith L (deriv F) (Icc a b)) :
    EqOn (tangentExtension F a b) F (Icc a b) := by
  intro x hx
  have hc := (lipschitzWith_clipped hab hL).continuous
  have hd (s : ℝ) (hs : s ∈ uIcc a x) : HasDerivAt F (deriv F (max a (min s b))) s := by
    have hmem : s ∈ Icc a b := ⟨(uIcc_of_le hx.1 ▸ hs).1,
      (uIcc_of_le hx.1 ▸ hs).2.trans hx.2⟩
    simpa only [min_eq_left hmem.2, max_eq_right hmem.1] using (hF s hmem).hasDerivAt
  rw [tangentExtension, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable a x)]
  ring

theorem tangentExtension_eq_left {F : ℝ → ℝ} {a b x : ℝ} (hx : x ≤ a) :
    tangentExtension F a b x = F a + deriv F a * (x-a) := by
  unfold tangentExtension
  congr 1
  calc
    _ = ∫ _ in a..x, deriv F a := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_ge hx] at hs
      simp only [max_eq_left ((min_le_left s b).trans hs.2)]
    _ = _ := by simp [mul_comm]

theorem tangentExtension_eq_right {F : ℝ → ℝ} {L : ℝ≥0} {a b x : ℝ} (hab : a ≤ b)
    (hF : ∀ s ∈ Icc a b, DifferentiableAt ℝ F s)
    (hL : LipschitzOnWith L (deriv F) (Icc a b)) (hx : b ≤ x) :
    tangentExtension F a b x = F b + deriv F b * (x-b) := by
  have hc := (lipschitzWith_clipped hab hL).continuous
  have he := tangentExtension_eq_on hab hF hL (right_mem_Icc.mpr hab)
  have hi : (∫ s in b..x, deriv F (max a (min s b))) = deriv F b * (x-b) := by
    calc
      _ = ∫ _ in b..x, deriv F b := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hx] at hs
        simp only [min_eq_right hs.1, max_eq_right hab]
      _ = _ := by simp [mul_comm]
  unfold tangentExtension at he ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a b)
    (hc.intervalIntegrable b x), hi]
  linarith

theorem exists_lipschitzOnWith_deriv {F : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x) :
    ∃ L : ℝ≥0, LipschitzOnWith L (deriv F) (Icc a b) := by
  have hc : ContDiffOn ℝ 1 (deriv F) (Icc a b) :=
    fun x hx => ((hF x hx).derivWithin (by norm_num)).contDiffWithinAt
  exact hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc

def rpowTangent (q a b : ℝ) : ℝ → ℝ := tangentExtension (fun x => x^q) a b

def xlogxTangent (a b : ℝ) : ℝ → ℝ := tangentExtension (fun x => x*Real.log x) a b

theorem rpow_contDiffAt_on {a b : ℝ} (ha : 0 < a) (q : ℝ) :
    ∀ x ∈ Icc a b, ContDiffAt ℝ 2 (fun x : ℝ => x^q) x :=
  fun _ hx => Real.contDiffAt_rpow_const_of_ne (ne_of_gt (ha.trans_le hx.1))

theorem xlogx_contDiffAt_on {a b : ℝ} (ha : 0 < a) :
    ∀ x ∈ Icc a b, ContDiffAt ℝ 2 (fun x : ℝ => x*Real.log x) x :=
  fun _ hx => contDiffAt_id.mul (Real.contDiffAt_log.mpr (ne_of_gt (ha.trans_le hx.1)))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem integral_tangentExtension_comp {F : ℝ → ℝ} {L : ℝ≥0} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, DifferentiableAt ℝ F x)
    (hL : LipschitzOnWith L (deriv F) (Icc a b)) (v : Lp ℝ 2 μ)
    (hv : ∀ᵐ ω ∂μ, v ω ∈ Icc a b) :
    ∫ ω, tangentExtension F a b (v ω) ∂μ = ∫ ω, F (v ω) ∂μ :=
  integral_congr_ae (hv.mono fun _ h => tangentExtension_eq_on hab hF hL h)

omit [IsProbabilityMeasure μ] in
theorem deriv_tangentExtension_comp {F : ℝ → ℝ} {L : ℝ≥0} {a b : ℝ} (hab : a ≤ b)
    (hL : LipschitzOnWith L (deriv F) (Icc a b)) (v : Lp ℝ 2 μ)
    (hv : ∀ᵐ ω ∂μ, v ω ∈ Icc a b) :
    (fun ω => deriv (tangentExtension F a b) (v ω)) =ᵐ[μ] fun ω => deriv F (v ω) := by
  rw [deriv_tangentExtension hab hL]
  filter_upwards [hv] with ω hω
  rw [min_eq_left hω.2, max_eq_right hω.1]

namespace ErrorStructure
variable (S : ErrorStructure Ω μ)

theorem semigroup_mem_Icc {a b t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ ω ∂μ, f ω ∈ Icc a b) : ∀ᵐ ω ∂μ, S.semigroup t f ω ∈ Icc a b := by
  have hlo := S.semigroup_mono ht (f := Lp.const 2 μ a) (g := f) (by
    filter_upwards [hf, Lp.coeFn_const (p := 2) (μ := μ) (c := a)] with ω hω hc
    simpa [hc] using hω.1)
  have hhi := S.semigroup_mono ht (f := f) (g := Lp.const 2 μ b) (by
    filter_upwards [hf, Lp.coeFn_const (p := 2) (μ := μ) (c := b)] with ω hω hc
    simpa [hc] using hω.2)
  rw [S.semigroup_const ht] at hlo hhi
  filter_upwards [hlo, hhi, Lp.coeFn_const (p := 2) (μ := μ) (c := a),
    Lp.coeFn_const (p := 2) (μ := μ) (c := b)] with ω hl hh ha hb
  exact ⟨by simpa [ha] using hl, by simpa [hb] using hh⟩

/-- Local C² calculus is transferred through the tangent extension along a confined orbit. -/
theorem hasDerivAt_integral_comp_semigroup_of_Icc {F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (u : S.generatorDom) (hu : ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ Icc a b)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ ω, F (S.semigroup s u ω) ∂μ)
      (∫ ω, deriv F (S.semigroup t u ω) *
        S.generator (S.semigroupGeneratorDom ht.le u) ω ∂μ) t := by
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_deriv hF
  have hd := S.hasDerivAt_integral_comp_semigroup
    (fun x => ((contDiff_tangentExtension hab hL).differentiable (by norm_num) x).hasDerivAt)
    (lipschitzWith_deriv_tangentExtension hab hL) u ht
  have he := deriv_tangentExtension_comp hab hL (S.semigroup t u) (S.semigroup_mem_Icc ht.le u hu)
  have hv : (∫ ω, deriv (tangentExtension F a b) (S.semigroup t u ω) *
      S.generator (S.semigroupGeneratorDom ht.le u) ω ∂μ) =
      ∫ ω, deriv F (S.semigroup t u ω) * S.generator (S.semigroupGeneratorDom ht.le u) ω ∂μ :=
    integral_congr_ae (he.mul (Filter.EventuallyEq.refl _ _))
  rw [hv] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ici_mem_nhds ht] with s hs
  exact (integral_tangentExtension_comp hab (fun x hx => (hF x hx).differentiableAt (by norm_num))
    hL (S.semigroup s u) (S.semigroup_mem_Icc hs u hu)).symm

theorem continuous_integral_comp_semigroup_of_Icc {F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (u : Lp ℝ 2 μ) (hu : ∀ᵐ ω ∂μ, u ω ∈ Icc a b) :
    ContinuousOn (fun s => ∫ ω, F (S.semigroup s u ω) ∂μ) (Ici 0) := by
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_deriv hF
  apply (S.continuous_integral_comp_semigroup
    (fun x => ((contDiff_tangentExtension hab hL).differentiable (by norm_num) x).hasDerivAt)
    (lipschitzWith_deriv_tangentExtension hab hL) u).congr
  intro s hs
  exact (integral_tangentExtension_comp hab (fun x hx => (hF x hx).differentiableAt (by norm_num))
    hL (S.semigroup s u) (S.semigroup_mem_Icc hs u hu)).symm

end ErrorStructure
end ErrorCalculus
