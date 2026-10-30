import Foundations.Sobolev1D.Cutoff
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
open MeasureTheory Filter Set Function Metric ContinuousLinearMap
open scoped Topology ENNReal ContDiff Convolution Pointwise
namespace Foundations

/-- The normalized kernels have outer radius 1/(n+1), hence at most one. -/
def mollifier (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨(1 / (n+1 : ℝ)) / 2, 1 / (n+1 : ℝ), by positivity, by
    exact half_lt_self (by positivity)⟩

def mollify (v : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  v ⋆[lsmul ℝ ℝ, volume] (mollifier n).normed volume

theorem real_convolution_comm (f g : ℝ → ℝ) :
    (f ⋆[lsmul ℝ ℝ, volume] g) = g ⋆[lsmul ℝ ℝ, volume] f := by
  ext x
  simpa only [convolution_def, flip_apply, lsmul_apply, smul_eq_mul, mul_comm] using
    congrFun (convolution_flip (L := lsmul ℝ ℝ) (μ := volume) (f := g) (g := f)) x

theorem mollify_eq_left (v : ℝ → ℝ) (n : ℕ) :
    mollify v n = (mollifier n).normed volume ⋆[lsmul ℝ ℝ, volume] v := real_convolution_comm _ _

theorem mollifier_radius_tendsto : Tendsto (fun n => (mollifier n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem mollifier_radius_le_one (n : ℕ) : (mollifier n).rOut ≤ 1 := by
  change 1 / (n+1 : ℝ) ≤ 1
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem contDiff_mollify {v : ℝ → ℝ} (hv : LocallyIntegrable v volume) (n : ℕ) :
    ContDiff ℝ ∞ (mollify v n) :=
  (mollifier n).hasCompactSupport_normed.contDiff_convolution_right _ hv (mollifier n).contDiff_normed

theorem hasCompactSupport_mollify {v : ℝ → ℝ} (hv : HasCompactSupport v) (n : ℕ) :
    HasCompactSupport (mollify v n) := hv.convolution (lsmul ℝ ℝ) (mollifier n).hasCompactSupport_normed

theorem continuous_of_locallyAC {v : ℝ → ℝ}
    (hv : ∀ a b, AbsolutelyContinuousOnInterval v a b) : Continuous v := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc := (hv (x-1) (x+1)).continuousOn
  rw [uIcc_of_le (by linarith)] at hc
  exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- Integration by parts on a containing interval; all boundary terms vanish. -/
theorem integral_mul_deriv_of_compact_AC {v ψ : ℝ → ℝ}
    (hv : ∀ a b, AbsolutelyContinuousOnInterval v a b) (hc : HasCompactSupport v)
    (hψ : ContDiff ℝ 1 ψ) :
    (∫ t, v t * deriv ψ t) = -(∫ t, deriv v t * ψ t) := by
  obtain ⟨A,hA,hbound⟩ := hc.isCompact.isBounded.exists_pos_norm_lt
  have hs : tsupport v ⊆ Ioc (-A) A := by
    intro x hx
    have h := hbound x hx
    rw [Real.norm_eq_abs, abs_lt] at h
    exact ⟨h.1,h.2.le⟩
  have hvA : v A = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    have h := hbound A hx
    simp only [Real.norm_eq_abs, abs_of_pos hA] at h
    exact lt_irrefl _ h)
  have hvnA : v (-A) = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    have h := hbound (-A) hx
    simp only [norm_neg, Real.norm_eq_abs, abs_of_pos hA] at h
    exact lt_irrefl _ h)
  have hs₁ : support (fun t => v t * deriv ψ t) ⊆ Ioc (-A) A := by
    exact (support_mul_subset_left _ _).trans ((subset_tsupport v).trans hs)
  have hs₂ : support (fun t => deriv v t * ψ t) ⊆ Ioc (-A) A := by
    exact (support_mul_subset_left _ _).trans (support_deriv_subset.trans hs)
  have hi := (hv (-A) A).integral_mul_deriv_eq_deriv_mul
    hψ.contDiffOn.absolutelyContinuousOnInterval
  rw [intervalIntegral.integral_eq_integral_of_support_subset hs₁,
    intervalIntegral.integral_eq_integral_of_support_subset hs₂, hvA, hvnA] at hi
  simpa using hi

/-- The weak derivative moves across convolution by AC integration by parts. -/
theorem deriv_mollify_eq_mollify_deriv {v : ℝ → ℝ}
    (hv : ∀ a b, AbsolutelyContinuousOnInterval v a b) (hc : HasCompactSupport v) (n : ℕ) :
    deriv (mollify v n) = mollify (deriv v) n := by
  have hvc := continuous_of_locallyAC hv
  have hφ : ContDiff ℝ 1 ((mollifier n).normed volume) := (mollifier n).contDiff_normed
  ext x
  have hd := HasCompactSupport.hasDerivAt_convolution_right (μ := volume) (lsmul ℝ ℝ)
    hvc.locallyIntegrable (mollifier n).hasCompactSupport_normed hφ x
  unfold mollify
  rw [hd.deriv]
  let ψ : ℝ → ℝ := fun t => (mollifier n).normed volume (x-t)
  have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_const.sub contDiff_id)
  have he (t : ℝ) : deriv ψ t = -(deriv ((mollifier n).normed volume) (x-t)) := by
    have h := (hφ.differentiable one_ne_zero (x-t)).hasDerivAt.comp t ((hasDerivAt_id t).const_sub x)
    simpa [ψ, Function.comp_def] using h.deriv
  have hi := integral_mul_deriv_of_compact_AC hv hc hψ
  simp_rw [he, mul_neg, integral_neg] at hi
  exact neg_injective hi

theorem tendstoUniformly_mollify {v : ℝ → ℝ} (hv : UniformContinuous v) :
    TendstoUniformly (mollify v) v atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp hv (ε/2) (half_pos hε)
  filter_upwards [mollifier_radius_tendsto.eventually (gt_mem_nhds hδ)] with n hn
  intro x
  rw [dist_comm, mollify_eq_left]
  apply ((mollifier n).dist_normed_convolution_le hv.continuous.aestronglyMeasurable ?_).trans_lt (half_lt_self hε)
  intro y hy
  exact (hmod ((mem_ball.mp hy).trans hn)).le

theorem norm_mollify_le {v : ℝ → ℝ} (hv : AEStronglyMeasurable v volume)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖v x‖ ≤ M) (n : ℕ) (x : ℝ) : ‖mollify v n x‖ ≤ M := by
  rw [mollify_eq_left]
  simpa only [dist_zero_right] using dist_convolution_le (μ := volume) (x₀ := x) (z₀ := (0 : ℝ)) hM
    (mollifier n).support_normed_eq.subset (mollifier n).nonneg_normed
    (mollifier n).integral_normed hv (fun y _ => by simpa using hb y)

/-- A common compact support for all regularizations. -/
theorem support_mollify_subset (v : ℝ → ℝ) (n : ℕ) :
    support (mollify v n) ⊆ tsupport v + closedBall (0 : ℝ) 1 := by
  apply (support_convolution_subset (lsmul ℝ ℝ)).trans
  apply add_subset_add (subset_tsupport v)
  rw [(mollifier n).support_normed_eq]
  exact (ball_subset_closedBall).trans (closedBall_subset_closedBall (mollifier_radius_le_one n))

end Foundations
