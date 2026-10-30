import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Smooth compactly supported approximation in L¹

## Main results
Every integrable real kernel on Euclidean space can be approximated in L¹ by smooth compactly
supported functions, in every dimension. The construction uses Mathlib's continuous compactly
supported approximation, normalized bumps and dominated convergence.

Reference: De Philippis–Rindler, arXiv p. 12, the smooth compactly supported part b₁,ε in the kernel
decomposition.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped Topology Convolution
namespace GeometricMeasure
namespace KernelCompactness
variable {d : ℕ}

/--
Smooth bump function centered at zero, with outer radius 1/(m+1) and inner radius half as large.
-/
def l1Bump (d m : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) where
  rIn := 1 / ((m : ℝ) + 1) / 2
  rOut := 1 / ((m : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)

/-- The outer radii of the bump functions tend to zero. -/
theorem l1Bump_rOut_tendsto :
    Tendsto (fun m : ℕ => (l1Bump d m).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The outer radii of the bump functions are at most one. -/
theorem l1Bump_rOut_le_one (m : ℕ) : (l1Bump d m).rOut ≤ 1 := by
  change 1 / ((m : ℝ) + 1) ≤ 1
  rw [div_le_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) m]

/-- Smoothing of a function by the normalized bump function at index m. -/
def bumpSmoothing (d m : ℕ) (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  (l1Bump d m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g

/--
The smoothing of a continuous compactly supported function is bounded by any uniform bound on that
function.
-/
theorem bumpSmoothing_norm_le (m : ℕ) {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C)
    (x : EuclideanSpace ℝ (Fin d)) : ‖bumpSmoothing d m g x‖ ≤ C := by
  have hex := hgc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
    ((l1Bump d m).integrable_normed (μ := volume)).locallyIntegrable hg x
  rw [bumpSmoothing, convolution_def]
  calc
    ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) ((l1Bump d m).normed volume t) (g (x - t))‖ ≤
        ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) ((l1Bump d m).normed volume t) (g (x - t))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, (l1Bump d m).normed volume t * C := by
      apply integral_mono hex.norm ((l1Bump d m).integrable_normed.mul_const C)
      intro t
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, norm_mul,
        Real.norm_of_nonneg ((l1Bump d m).nonneg_normed t)]
      exact mul_le_mul_of_nonneg_left (hC _) ((l1Bump d m).nonneg_normed t)
    _ = C := by rw [integral_mul_const, (l1Bump d m).integral_normed, one_mul]

/-- The smoothing vanishes outside the closed ball of radius R+1 if g vanishes outside B̄(0,R). -/
theorem bumpSmoothing_eq_zero (m : ℕ) {g : EuclideanSpace ℝ (Fin d) → ℝ} {R : ℝ}
    (hR : ∀ y, R < ‖y‖ → g y = 0) {x : EuclideanSpace ℝ (Fin d)} (hx : R + 1 < ‖x‖) :
    bumpSmoothing d m g x = 0 := by
  rw [bumpSmoothing, convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  by_cases ht : ‖t‖ < 1
  · have hxt : R < ‖x - t‖ := by
      have h := norm_sub_norm_le x t
      linarith
    simp [hR _ hxt]
  · have hs : t ∉ Function.support ((l1Bump d m).normed volume) := by
      rw [(l1Bump d m).support_normed_eq]
      intro hb
      rw [mem_ball, dist_zero_right] at hb
      exact ht (hb.trans_le (l1Bump_rOut_le_one m))
    rw [Function.notMem_support] at hs
    simp [hs]

/-- Smoothing of a continuous compactly supported function: L¹ convergence. -/
theorem bumpSmoothing_l1_tendsto {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun m => ∫ x, ‖bumpSmoothing d m g x - g x‖) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  have hRz : ∀ y, R < ‖y‖ → g y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hR hmem
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  let F : EuclideanSpace ℝ (Fin d) → ℝ :=
    (closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + 1)).indicator (fun _ => 2 * C)
  have hF : Integrable F :=
    (integrableOn_const (C := 2 * C) measure_closedBall_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  have hlim := tendsto_integral_of_dominated_convergence
    (F := fun m x => ‖bumpSmoothing d m g x - g x‖) (f := fun _ => (0 : ℝ)) F
    (fun m => ((hgc.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      ((l1Bump d m).integrable_normed (μ := volume)).locallyIntegrable hg).sub hg).norm.aestronglyMeasurable)
    hF
    (fun m => Eventually.of_forall (fun x => by
      rw [norm_norm]
      by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + 1)
      · simp only [F, indicator_of_mem hx]
        calc ‖bumpSmoothing d m g x - g x‖ ≤ ‖bumpSmoothing d m g x‖ + ‖g x‖ := norm_sub_le _ _
          _ ≤ C + C := add_le_add (bumpSmoothing_norm_le m hg hgc hC x) (hC x)
          _ = 2 * C := by ring
      · have hx' : R + 1 < ‖x‖ := by
          rw [mem_closedBall, dist_zero_right, not_le] at hx
          exact hx
        rw [bumpSmoothing_eq_zero m hRz hx', hRz x (by linarith), sub_zero, norm_zero]
        simp only [F, indicator_of_notMem hx, le_refl]))
    (Eventually.of_forall (fun x => by
      have h := ContDiffBump.convolution_tendsto_right_of_continuous
        (φ := fun m => l1Bump d m) (μ := volume) l1Bump_rOut_tendsto hg x
      have h2 := (h.sub_const (g x)).norm
      simpa [bumpSmoothing] using h2))
  simpa only [integral_zero] using hlim

/--
Every integrable real kernel on Euclidean space has a smooth compactly supported approximation with
L¹ error below any prescribed δ > 0. Reference: De Philippis–Rindler, p. 12, b₁,ε ∈ C¹_c. Mathlib
also provides `MeasureTheory.Lp.dense_hasCompactSupport_contDiff`.
-/
theorem exists_smooth_compact_l1_approx {k : EuclideanSpace ℝ (Fin d) → ℝ} (hk : Integrable k)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ κ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) κ ∧ HasCompactSupport κ ∧
      (∫ x, ‖k x - κ x‖) < δ := by
  obtain ⟨g, hgc, hkg, hg, hgi⟩ := hk.exists_hasCompactSupport_integral_sub_le (half_pos hδ)
  have ht := bumpSmoothing_l1_tendsto hg hgc
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds (half_pos hδ))).exists
  refine ⟨bumpSmoothing d m g, ?_, ?_, ?_⟩
  · exact (l1Bump d m).hasCompactSupport_normed.contDiff_convolution_left _
      (l1Bump d m).contDiff_normed hg.locallyIntegrable
  · exact (l1Bump d m).hasCompactSupport_normed.convolution _ hgc
  · have hbi : Integrable (bumpSmoothing d m g) :=
      ((hgc.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
        ((l1Bump d m).integrable_normed (μ := volume)).locallyIntegrable hg).integrable_of_hasCompactSupport
        ((l1Bump d m).hasCompactSupport_normed.convolution _ hgc))
    calc (∫ x, ‖k x - bumpSmoothing d m g x‖) ≤
        ∫ x, (‖k x - g x‖ + ‖bumpSmoothing d m g x - g x‖) := by
          apply integral_mono (hk.sub hbi).norm ((hk.sub hgi).norm.add (hbi.sub hgi).norm)
          intro x
          calc ‖k x - bumpSmoothing d m g x‖ = ‖(k x - g x) - (bumpSmoothing d m g x - g x)‖ := by
                ring_nf
            _ ≤ _ := norm_sub_le _ _
      _ = (∫ x, ‖k x - g x‖) + ∫ x, ‖bumpSmoothing d m g x - g x‖ :=
          integral_add (hk.sub hgi).norm (hbi.sub hgi).norm
      _ < δ / 2 + δ / 2 := add_lt_add_of_le_of_lt hkg hm
      _ = δ := add_halves δ

end KernelCompactness
end GeometricMeasure
