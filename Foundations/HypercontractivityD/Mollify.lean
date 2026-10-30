import Foundations.Sections.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set Function Metric ContinuousLinearMap
open scoped Topology ENNReal ContDiff Convolution Pointwise
namespace Foundations
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalized kernels have outer radius 1/(n+1), hence at most one. -/
def mollifierD (ι : Type*) [Fintype ι] (n : ℕ) : ContDiffBump (0 : ι → ℝ) :=
  ⟨(1 / (n+1 : ℝ)) / 2, 1 / (n+1 : ℝ), by positivity, by
    exact half_lt_self (by positivity)⟩

def mollifyD (v : (ι → ℝ) → ℝ) (n : ℕ) : (ι → ℝ) → ℝ :=
  v ⋆[lsmul ℝ ℝ, volume] (mollifierD ι n).normed volume

theorem real_convolution_commD (f g : (ι → ℝ) → ℝ) :
    (f ⋆[lsmul ℝ ℝ, volume] g) = g ⋆[lsmul ℝ ℝ, volume] f := by
  ext x
  simpa only [convolution_def, flip_apply, lsmul_apply, smul_eq_mul, mul_comm] using
    congrFun (convolution_flip (L := lsmul ℝ ℝ) (μ := volume) (f := g) (g := f)) x

theorem mollify_eq_leftD (v : (ι → ℝ) → ℝ) (n : ℕ) :
    mollifyD v n = (mollifierD ι n).normed volume ⋆[lsmul ℝ ℝ, volume] v := real_convolution_commD _ _

theorem mollifier_radius_tendstoD : Tendsto (fun n => (mollifierD ι n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem mollifier_radius_le_oneD (n : ℕ) : (mollifierD ι n).rOut ≤ 1 := by
  change 1 / (n+1 : ℝ) ≤ 1
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem contDiff_mollifyD {v : (ι → ℝ) → ℝ} (hv : LocallyIntegrable v volume) (n : ℕ) :
    ContDiff ℝ ∞ (mollifyD v n) :=
  (mollifierD ι n).hasCompactSupport_normed.contDiff_convolution_right _ hv (mollifierD ι n).contDiff_normed

theorem hasCompactSupport_mollifyD {v : (ι → ℝ) → ℝ} (hv : HasCompactSupport v) (n : ℕ) :
    HasCompactSupport (mollifyD v n) := hv.convolution (lsmul ℝ ℝ) (mollifierD ι n).hasCompactSupport_normed

theorem tendstoUniformly_mollifyD {v : (ι → ℝ) → ℝ} (hv : UniformContinuous v) :
    TendstoUniformly (mollifyD v) v atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp hv (ε/2) (half_pos hε)
  filter_upwards [(mollifier_radius_tendstoD (ι := ι)).eventually (gt_mem_nhds hδ)] with n hn
  intro x
  rw [dist_comm, mollify_eq_leftD]
  apply ((mollifierD ι n).dist_normed_convolution_le hv.continuous.aestronglyMeasurable ?_).trans_lt (half_lt_self hε)
  intro y hy
  exact (hmod ((mem_ball.mp hy).trans hn)).le

theorem norm_mollify_leD {v : (ι → ℝ) → ℝ} (hv : AEStronglyMeasurable v volume)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖v x‖ ≤ M) (n : ℕ) (x : ι → ℝ) : ‖mollifyD v n x‖ ≤ M := by
  rw [mollify_eq_leftD]
  simpa only [dist_zero_right] using dist_convolution_le (μ := volume) (x₀ := x) (z₀ := (0 : ℝ)) hM
    (mollifierD ι n).support_normed_eq.subset (mollifierD ι n).nonneg_normed
    (mollifierD ι n).integral_normed hv (fun y _ => by simpa using hb y)

/-- A common compact support for all regularizations. -/
theorem support_mollify_subsetD (v : (ι → ℝ) → ℝ) (n : ℕ) :
    support (mollifyD v n) ⊆ tsupport v + closedBall (0 : ι → ℝ) 1 := by
  apply (support_convolution_subset (lsmul ℝ ℝ)).trans
  apply add_subset_add (subset_tsupport v)
  rw [(mollifierD ι n).support_normed_eq]
  exact (ball_subset_closedBall).trans (closedBall_subset_closedBall (mollifier_radius_le_oneD n))

theorem memLp_mollify_compactD (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ]
    {f : (ι → ℝ) → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (n : ℕ) :
    MemLp (mollifyD f n) 2 μ :=
  (contDiff_mollifyD hf.locallyIntegrable n).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_mollifyD hc n)

/-- The continuous compactly supported case, for any locally finite measure. -/
theorem tendsto_L2_mollify_continuousD (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ]
    {f : (ι → ℝ) → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun n => (memLp_mollify_compactD μ hf hc n).toLp (mollifyD f n)) atTop
      (𝓝 ((hf.memLp_of_hasCompactSupport hc : MemLp f 2 μ).toLp f)) := by
  let K := tsupport f + closedBall (0 : ι → ℝ) 1
  have hK : IsCompact K := hc.isCompact.add (isCompact_closedBall _ _)
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hf
  have hM₀ : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  have hb : MemLp (K.indicator (fun _ => M)) 2 μ :=
    memLp_indicator_const 2 hK.measurableSet M (Or.inr hK.measure_lt_top.ne)
  apply tendsto_toLp_dominated μ _ _ hb
  · intro n
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ K
    · simpa only [indicator_of_mem hx] using norm_mollify_leD hf.aestronglyMeasurable hM₀ hM n x
    · have hz : mollifyD f n x = 0 := notMem_support.mp (fun hs => hx (support_mollify_subsetD f n hs))
      simp only [hz, norm_zero, indicator_of_notMem hx, le_refl]
  · exact Eventually.of_forall (fun x =>
      (tendstoUniformly_mollifyD (hc.uniformContinuous_of_continuous hf)).tendsto_at x)

end Foundations
