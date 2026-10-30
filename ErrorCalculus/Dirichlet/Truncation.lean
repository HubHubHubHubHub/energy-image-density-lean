import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace ErrorCalculus

/-- a compact smooth cutoff, equal to one on a neighborhood of [-M,M]. -/
def truncationBump (M : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := |M| + 1
  rOut := |M| + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The primitive of the cutoff, normalized to vanish at zero. -/
def truncation (M x : ℝ) : ℝ := ∫ t in 0..x, truncationBump M t

theorem hasDerivAt_truncation (M x : ℝ) :
    HasDerivAt (truncation M) (truncationBump M x) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((truncationBump M).continuous.intervalIntegrable _ _)
    (truncationBump M).continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    (truncationBump M).continuous.continuousAt

@[simp] theorem deriv_truncation (M x : ℝ) :
    deriv (truncation M) x = truncationBump M x := (hasDerivAt_truncation M x).deriv

theorem truncation_contDiff (M : ℝ) : ContDiff ℝ 1 (truncation M) := by
  rw [contDiff_one_iff_deriv]
  exact ⟨fun x => (hasDerivAt_truncation M x).differentiableAt,
    by convert (truncationBump M).continuous using 1; ext x; exact deriv_truncation M x⟩

theorem truncation_lipschitz (M : ℝ) : LipschitzWith 1 (truncation M) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_truncation M x).differentiableAt)
  intro x
  change ‖deriv (truncation M) x‖ ≤ (1 : ℝ)
  rw [deriv_truncation, Real.norm_of_nonneg (truncationBump M).nonneg]
  exact (truncationBump M).le_one

theorem truncationBump_eq_one {M x : ℝ} (hx : |x| ≤ M) : truncationBump M x = 1 := by
  apply (truncationBump M).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact hx.trans (by dsimp [truncationBump]; linarith [le_abs_self M])

theorem deriv_truncation_eq_one {M x : ℝ} (hx : |x| ≤ M) :
    deriv (truncation M) x = 1 := by rw [deriv_truncation, truncationBump_eq_one hx]

theorem truncation_eq_self {M x : ℝ} (hx : |x| ≤ M) : truncation M x = x := by
  have hM : 0 ≤ M := (abs_nonneg x).trans hx
  have he : ∀ t ∈ uIcc 0 x, truncationBump M t = (1 : ℝ) := by
    intro t ht
    apply truncationBump_eq_one
    have ht' := (mem_uIcc.mp ht)
    rcases ht' with ht' | ht' <;> rw [abs_le] <;>
      have hx' := abs_le.mp hx <;> constructor <;> linarith
  unfold truncation
  rw [intervalIntegral.integral_congr he]
  simp

/-- A finite uniform bound; its value is irrelevant to the domain argument. -/
def truncationBound (M : ℝ) : ℝ := ∫ t : ℝ, ‖truncationBump M t‖

theorem truncationBound_nonneg (M : ℝ) : 0 ≤ truncationBound M :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem norm_truncation_le (M x : ℝ) : ‖truncation M x‖ ≤ truncationBound M := by
  apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
  exact integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _ => norm_nonneg _)
    ((truncationBump M).continuous.integrable_of_hasCompactSupport
      (truncationBump M).hasCompactSupport).norm

/-- The bounded, globally Lipschitz substitute for multiplication. -/
def truncatedProduct (M : ℝ) (x : Fin 2 → ℝ) : ℝ := truncation M (x 0) * truncation M (x 1)

theorem truncatedProduct_contDiff (M : ℝ) : ContDiff ℝ 1 (truncatedProduct M) :=
  ((truncation_contDiff M).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).contDiff).mul
    ((truncation_contDiff M).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).contDiff)

theorem truncatedProduct_lipschitz (M : ℝ) :
    LipschitzWith ⟨2 * truncationBound M, by positivity [truncationBound_nonneg M]⟩
      (truncatedProduct M) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h0 := (truncation_lipschitz M).dist_le_mul (x 0) (y 0)
  have h1 := (truncation_lipschitz M).dist_le_mul (x 1) (y 1)
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at h0 h1
  have h0' : ‖x 0 - y 0‖ ≤ ‖x-y‖ := norm_le_pi_norm (x-y) 0
  have h1' : ‖x 1 - y 1‖ ≤ ‖x-y‖ := norm_le_pi_norm (x-y) 1
  rw [dist_eq_norm]
  change ‖truncation M (x 0)*truncation M (x 1) -
    truncation M (y 0)*truncation M (y 1)‖ ≤ (2*truncationBound M)*‖x-y‖
  calc
    _ = ‖(truncation M (x 0)-truncation M (y 0))*truncation M (x 1) +
        truncation M (y 0)*(truncation M (x 1)-truncation M (y 1))‖ := by congr 1; ring
    _ ≤ ‖truncation M (x 0)-truncation M (y 0)‖*‖truncation M (x 1)‖ +
        ‖truncation M (y 0)‖*‖truncation M (x 1)-truncation M (y 1)‖ := by
      simpa only [norm_mul] using norm_add_le
        ((truncation M (x 0)-truncation M (y 0))*truncation M (x 1))
        (truncation M (y 0)*(truncation M (x 1)-truncation M (y 1)))
    _ ≤ ‖x-y‖*truncationBound M + truncationBound M*‖x-y‖ :=
      add_le_add (mul_le_mul (h0.trans h0') (norm_truncation_le M _) (norm_nonneg _)
        (norm_nonneg _))
        (mul_le_mul (norm_truncation_le M _) (h1.trans h1') (norm_nonneg _)
          (truncationBound_nonneg M))
    _ = _ := by ring

theorem truncatedProduct_eq_mul {M : ℝ} {x : Fin 2 → ℝ}
    (h0 : |x 0| ≤ M) (h1 : |x 1| ≤ M) : truncatedProduct M x = x 0 * x 1 := by
  simp [truncatedProduct, truncation_eq_self h0, truncation_eq_self h1]

theorem fderiv_truncatedProduct {M : ℝ} {x : Fin 2 → ℝ}
    (h0 : |x 0| ≤ M) (h1 : |x 1| ≤ M) (v : Fin 2 → ℝ) :
    fderiv ℝ (truncatedProduct M) x v = x 0 * v 1 + x 1 * v 0 := by
  have h0d := (hasDerivAt_truncation M (x 0)).comp_hasFDerivAt x
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt
  have h1d := (hasDerivAt_truncation M (x 1)).comp_hasFDerivAt x
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt
  change fderiv ℝ ((truncation M ∘ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0)) *
    (truncation M ∘ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1))) x v = _
  rw [(h0d.mul h1d).fderiv]
  simp [truncationBump_eq_one h0, truncationBump_eq_one h1,
    truncation_eq_self h0, truncation_eq_self h1]

end ErrorCalculus
