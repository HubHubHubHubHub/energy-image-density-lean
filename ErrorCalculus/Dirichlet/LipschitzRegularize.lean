import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Smooth regularization of real Lipschitz functions

## Main results
Convolution with nonnegative smooth kernels of mass one preserves the Lipschitz constant and
converges uniformly on the whole real line, with an explicit error bound. The derivatives are
uniformly bounded and converge almost everywhere to the derivative of the original function.
Differentiation uses Rademacher's theorem and an integrable Lipschitz bound; everywhere
differentiability of the original function is not required.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped Convolution NNReal ContDiff
namespace ErrorCalculus

/-- radii with constant ratio two and outer radius tending to zero. -/
def lipschitzBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (1 / 2 : ℝ) ^ (n+1)
  rOut := (1 / 2 : ℝ) ^ n
  rIn_pos := pow_pos (by norm_num) _
  rIn_lt_rOut := by
    rw [pow_succ]
    nlinarith [pow_pos (show (0:ℝ) < 1/2 by norm_num) n]

/-- convolution with a nonnegative smooth kernel of mass one. -/
def lipschitzMollify (F : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (lipschitzBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F

theorem lipschitzMollify_eq_integral (F : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    lipschitzMollify F n x = ∫ t, (lipschitzBump n).normed volume t * F (x-t) := rfl

/-- Each integrand is integrable, even for an unbounded Lipschitz function. -/
theorem lipschitzMollify_integrable {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (n : ℕ) (x : ℝ) :
    Integrable (fun t => (lipschitzBump n).normed volume t * F (x-t)) :=
  (lipschitzBump n).hasCompactSupport_normed.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (lipschitzBump n).continuous_normed
    hF.continuous.locallyIntegrable x

/-- regularization is smooth. -/
theorem lipschitzMollify_contDiff {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (n : ℕ) : ContDiff ℝ ∞ (lipschitzMollify F n) :=
  (lipschitzBump n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (lipschitzBump n).contDiff_normed
    hF.continuous.locallyIntegrable

/-- convolution preserves the exact Lipschitz constant. -/
theorem lipschitzMollify_lipschitz {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (n : ℕ) : LipschitzWith L (lipschitzMollify F n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, lipschitzMollify_eq_integral, lipschitzMollify_eq_integral,
    ← integral_sub (lipschitzMollify_integrable hF n x) (lipschitzMollify_integrable hF n y)]
  calc
    _ ≤ ∫ t, (lipschitzBump n).normed volume t * ((L:ℝ) * dist x y) := by
      apply norm_integral_le_of_norm_le
      · exact (lipschitzBump n).integrable_normed.mul_const _
      · filter_upwards [] with t
        rw [← mul_sub, norm_mul, Real.norm_of_nonneg ((lipschitzBump n).nonneg_normed t)]
        apply mul_le_mul_of_nonneg_left _ ((lipschitzBump n).nonneg_normed t)
        simpa only [Real.dist_eq, Real.norm_eq_abs, sub_sub_sub_cancel_right] using
          hF.dist_le_mul (x-t) (y-t)
    _ = _ := by rw [integral_mul_const, (lipschitzBump n).integral_normed, one_mul]

/-- a uniform error bound at every point. -/
theorem abs_lipschitzMollify_sub_le {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (n : ℕ) (x : ℝ) :
    |lipschitzMollify F n x - F x| ≤ (L:ℝ) * (1/2:ℝ)^n := by
  apply (lipschitzBump n).dist_normed_convolution_le hF.continuous.aestronglyMeasurable
  intro y hy
  exact (hF.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left (le_of_lt hy) L.coe_nonneg)

/-- uniform convergence on the whole line. -/
theorem tendstoUniformly_lipschitzMollify {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) : TendstoUniformly (lipschitzMollify F) F atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have ht : Tendsto (fun n : ℕ => (L:ℝ) * (1/2:ℝ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul (L:ℝ)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x
  have hb : dist (F x) (lipschitzMollify F n x) ≤ (L:ℝ) * (1/2:ℝ)^n := by
    simpa only [Real.dist_eq, abs_sub_comm] using abs_lipschitzMollify_sub_le hF n x
  exact hb.trans_lt hn

/-- The uniform derivative bound needs only preservation of Lipschitz constants. -/
theorem abs_deriv_lipschitzMollify_le {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (n : ℕ) (x : ℝ) :
    |deriv (lipschitzMollify F n) x| ≤ L :=
  norm_deriv_le_of_lipschitz (𝕜 := ℝ) (lipschitzMollify_lipschitz hF n)

/-- The measurable bounded derivative is locally integrable. -/
theorem lipschitz_deriv_locallyIntegrable {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) : LocallyIntegrable (deriv F) volume := by
  apply locallyIntegrable_iff.mpr
  intro k hk
  exact IntegrableOn.of_bound hk.measure_lt_top
    (measurable_deriv F).aestronglyMeasurable (L:ℝ)
    (ae_of_all _ fun _ => norm_deriv_le_of_lipschitz (𝕜 := ℝ) hF)

/--
differentiate the Lipschitz integrand using Rademacher and an integrable Lipschitz bound. No
everywhere differentiability or integration by parts is needed.
-/
theorem deriv_lipschitzMollify {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (n : ℕ) (x : ℝ) :
    deriv (lipschitzMollify F n) x = lipschitzMollify (deriv F) n x := by
  let φ := (lipschitzBump n).normed volume
  have hdiff : ∀ᵐ t ∂volume, DifferentiableAt ℝ F (x-t) :=
    (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae
      hF.ae_differentiableAt
  have hd := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun y t => φ t * F (y-t)) (F' := fun t => φ t * deriv F (x-t))
    (bound := fun t => φ t * (L:ℝ)) (s := Set.univ) (x₀ := x) (μ := volume)
    (Filter.univ_mem) (Filter.Eventually.of_forall fun y =>
      ((lipschitzBump n).continuous_normed.mul
        (hF.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (lipschitzMollify_integrable hF n x)
    (((lipschitzBump n).continuous_normed.measurable.mul
      ((measurable_deriv F).comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
    (ae_of_all _ fun t => ?_) ((lipschitzBump n).integrable_normed.mul_const (L:ℝ)) ?_
  · exact hd.2.deriv
  · apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simp only [φ, Real.dist_eq, ← mul_sub, abs_mul, Real.coe_nnabs,
      abs_of_nonneg ((lipschitzBump n).nonneg_normed t), abs_of_nonneg L.coe_nonneg]
    have hb := hF.dist_le_mul (y-t) (z-t)
    simp only [Real.dist_eq, sub_sub_sub_cancel_right] at hb
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb
      ((lipschitzBump n).nonneg_normed t)
  · filter_upwards [hdiff] with t ht
    simpa using ((ht.hasDerivAt.comp x ((hasDerivAt_id x).sub_const t)).const_mul (φ t))

/-- a.e. derivative convergence follows from Lebesgue differentiation of F'. -/
theorem deriv_lipschitzMollify_tendsto_ae {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) : ∀ᵐ x ∂volume,
    Tendsto (fun n => deriv (lipschitzMollify F n) x) atTop (𝓝 (deriv F x)) := by
  simp_rw [deriv_lipschitzMollify hF]
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := lipschitzBump) (K := 2)
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · filter_upwards [] with n
    change (1/2:ℝ)^n ≤ 2 * (1/2:ℝ)^(n+1)
    rw [pow_succ]
    linarith
  · exact lipschitz_deriv_locallyIntegrable hF

end ErrorCalculus
