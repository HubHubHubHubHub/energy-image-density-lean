import ErrorCalculus.Dirichlet.SemigroupOrbitDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import ErrorCalculus.Dirichlet.ExtensionLp

/-!
# Integral Functional

## Main results
Globally differentiable integral functionals on L².
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace ErrorCalculus

/-- Integral Taylor remainder with the sharp factor one half. -/
theorem taylor_one_remainder_le {F F' : ℝ → ℝ} {L : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hL : LipschitzWith L F') (x y : ℝ) :
    |F (x+y) - F x - F' x * y| ≤ (L : ℝ) / 2 * y^2 := by
  let R := fun s : ℝ => F (x+s*y) - F x - F' x * (s*y)
  let D := fun s : ℝ => (F' (x+s*y) - F' x) * y
  have hd (s : ℝ) : HasDerivAt R (D s) s := by
    convert! (((hF (x+s*y)).comp s (((hasDerivAt_id s).mul_const y).const_add x)).sub_const
      (F x)).sub (((hasDerivAt_id s).mul_const y).const_mul (F' x)) using 1
    ring
  have hcont := hL.continuous
  have hc : Continuous D := by dsimp [D]; fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 1)
  have hb : ‖∫ s in (0:ℝ)..1, D s‖ ≤ ∫ s in (0:ℝ)..1, (L : ℝ)*y^2*s := by
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Filter.Eventually.of_forall fun s hs => ?_)
      ((show Continuous (fun s : ℝ => (L : ℝ)*y^2*s) by fun_prop).intervalIntegrable 0 1)
    have hh := hL.norm_sub_le (x+s*y) x
    simp only [Real.norm_eq_abs, add_sub_cancel_left, abs_mul, abs_of_nonneg hs.1.le] at hh
    dsimp [D]
    rw [abs_mul]
    calc
      _ ≤ ((L : ℝ) * (s * |y|)) * |y| := mul_le_mul_of_nonneg_right hh (abs_nonneg y)
      _ = (L : ℝ)*y^2*s := by rw [← sq_abs y]; ring
  rw [he] at hb
  have hi : (∫ s in (0:ℝ)..1, (L : ℝ)*y^2*s) = (L : ℝ)/2*y^2 := by
    calc
      _ = ((L : ℝ)*y^2) * ∫ s in (0:ℝ)..1, s :=
        intervalIntegral.integral_const_mul _ _
      _ = _ := by rw [integral_id]; ring
  rw [hi] at hb
  simpa [R, Real.norm_eq_abs] using hb

theorem abs_deriv_le_linear {F' : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F') (x : ℝ) :
    |F' x| ≤ |F' 0| + (L : ℝ)*|x| := by
  have h := hL.norm_sub_le x 0
  simp only [sub_zero, Real.norm_eq_abs] at h
  calc
    |F' x| = |(F' x - F' 0) + F' 0| := by congr 1; ring
    _ ≤ |F' x - F' 0| + |F' 0| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem abs_le_quadratic {F F' : ℝ → ℝ} {L : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hL : LipschitzWith L F') (x : ℝ) :
    |F x| ≤ |F 0| + |F' 0| *|x| + (L : ℝ)/2*x^2 := by
  have h := taylor_one_remainder_le hF hL 0 x
  rw [zero_add] at h
  calc
    |F x| = |(F x - F 0 - F' 0*x) + (F 0 + F' 0*x)| := by congr 1; ring
    _ ≤ |F x - F 0 - F' 0*x| + (|F 0| + |F' 0| *|x|) :=
      (abs_add_le _ _).trans (add_le_add_right (by simpa [abs_mul] using abs_add_le (F 0) (F' 0*x)) _)
    _ ≤ _ := by linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem memLp_deriv_comp {F' : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F')
    (u : Lp ℝ 2 μ) : MemLp (fun ω => F' (u ω)) 2 μ := by
  apply ((memLp_const |F' 0|).add ((Lp.memLp u).norm.const_mul (L : ℝ))).mono'
    (hL.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))
  exact Filter.Eventually.of_forall fun ω => abs_deriv_le_linear hL (u ω)

theorem integrable_comp {F F' : ℝ → ℝ} {L : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hL : LipschitzWith L F') (u : Lp ℝ 2 μ) :
    Integrable (fun ω => F (u ω)) μ := by
  have hi := ((integrable_const |F 0|).add
    (((Lp.memLp u).integrable (by norm_num)).abs.const_mul |F' 0|)).add
      ((Lp.memLp u).integrable_sq.const_mul ((L : ℝ)/2))
  apply hi.mono' ((continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt).comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable u))
  exact Filter.Eventually.of_forall fun ω => abs_le_quadratic hF hL (u ω)

def integralFunctional (F : ℝ → ℝ) (u : Lp ℝ 2 μ) : ℝ := ∫ ω, F (u ω) ∂μ

def integralFunctionalDeriv {F' : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F')
    (u : Lp ℝ 2 μ) : Lp ℝ 2 μ →L[ℝ] ℝ :=
  innerSL ℝ ((memLp_deriv_comp hL u).toLp _)

theorem integralFunctionalDeriv_apply {F' : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F')
    (u h : Lp ℝ 2 μ) : integralFunctionalDeriv hL u h = ∫ ω, F' (u ω)*h ω ∂μ := by
  change inner ℝ ((memLp_deriv_comp hL u).toLp _) h = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_deriv_comp hL u).coeFn_toLp] with ω hω
  simp only [RCLike.inner_apply, conj_trivial, hω, mul_comm]

theorem integralFunctional_remainder_le {F F' : ℝ → ℝ} {L : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hL : LipschitzWith L F') (u h : Lp ℝ 2 μ) :
    ‖integralFunctional F (u+h) - integralFunctional F u - integralFunctionalDeriv hL u h‖ ≤
      (L : ℝ)/2 * ‖h‖^2 := by
  rw [integralFunctionalDeriv_apply, integralFunctional, integralFunctional,
    ← integral_sub (integrable_comp hF hL (u+h)) (integrable_comp hF hL u),
    ← integral_sub (f := fun ω => F ((u+h) ω) - F (u ω))
      (g := fun ω => F' (u ω)*h ω)
      ((integrable_comp hF hL (u+h)).sub (integrable_comp hF hL u))
      ((memLp_deriv_comp hL u).integrable_mul (Lp.memLp h))]
  calc
    _ ≤ ∫ ω, (L : ℝ)/2*(h ω)^2 ∂μ :=
      norm_integral_le_of_norm_le ((Lp.memLp h).integrable_sq.const_mul _) (by
        filter_upwards [Lp.coeFn_add u h] with ω hω
        simpa only [hω, Pi.add_apply, Real.norm_eq_abs] using taylor_one_remainder_le hF hL (u ω) (h ω))
    _ = _ := by rw [integral_const_mul, ← lp_two_norm_sq]

/-- The differential is the continuous L² pairing with F'(u); u is arbitrary in L². -/
theorem hasFDerivAt_integralFunctional {F F' : ℝ → ℝ} {L : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hL : LipschitzWith L F') (u : Lp ℝ 2 μ) :
    HasFDerivAt (integralFunctional F) (integralFunctionalDeriv hL u) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsBigO.trans_isLittleO (g := fun h : Lp ℝ 2 μ => ‖h‖^2)
    _ (Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < 2))
  apply Asymptotics.IsBigO.of_bound ((L : ℝ)/2)
  exact Filter.Eventually.of_forall fun h => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖)] using
      integralFunctional_remainder_le hF hL u h

theorem continuous_integralFunctional {F F' : ℝ → ℝ} {L : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hL : LipschitzWith L F') :
    Continuous (integralFunctional F : Lp ℝ 2 μ → ℝ) :=
  continuous_iff_continuousAt.mpr fun u => (hasFDerivAt_integralFunctional hF hL u).continuousAt

namespace ErrorStructure
variable (S : ErrorStructure Ω μ)

theorem hasDerivAt_integral_comp_semigroup {F F' : ℝ → ℝ} {L : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hL : LipschitzWith L F')
    (u : S.generatorDom) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ ω, F (S.semigroup s u ω) ∂μ)
      (∫ ω, F' (S.semigroup t u ω) * S.generator (S.semigroupGeneratorDom ht.le u) ω ∂μ) t := by
  have h := (hasFDerivAt_integralFunctional hF hL (S.semigroup t u)).comp_hasDerivAt t
    (S.hasDerivAt_semigroup u ht)
  simpa only [Function.comp_def, integralFunctional, integralFunctionalDeriv_apply, S.semigroup_generator_eq ht.le] using! h

theorem hasDerivWithinAt_integral_comp_semigroup {F F' : ℝ → ℝ} {L : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hL : LipschitzWith L F')
    (u : S.generatorDom) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => ∫ ω, F (S.semigroup s u ω) ∂μ)
      (∫ ω, F' (S.semigroup t u ω) * S.generator (S.semigroupGeneratorDom ht u) ω ∂μ) (Ici t) t := by
  have h := (hasFDerivAt_integralFunctional hF hL (S.semigroup t u)).comp_hasDerivWithinAt t
    (S.hasDerivWithinAt_semigroup_Ici u ht)
  simpa only [Function.comp_def, integralFunctional, integralFunctionalDeriv_apply, S.semigroup_generator_eq ht] using! h

theorem continuous_integral_comp_semigroup {F F' : ℝ → ℝ} {L : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hL : LipschitzWith L F') (u : Lp ℝ 2 μ) :
    ContinuousOn (fun s => ∫ ω, F (S.semigroup s u ω) ∂μ) (Ici 0) :=
  (continuous_integralFunctional hF hL).comp_continuousOn
    (S.energy.continuous_semigroup_apply S.energy_closed S.dense u)

end ErrorStructure
end ErrorCalculus
