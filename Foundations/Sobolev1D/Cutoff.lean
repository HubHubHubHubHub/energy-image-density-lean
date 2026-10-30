import Foundations.Sobolev1D.Lp
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
namespace Foundations

/-- Fixed smooth plateau, with inner radius one and outer radius two. -/
def cutoffBase : ContDiffBump (0 : ℝ) := default

/-- The radius is n+1, so the zero index is nondegenerate. -/
def cutoff (n : ℕ) (x : ℝ) : ℝ := cutoffBase (x / (n+1 : ℝ))

theorem contDiff_cutoff (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  cutoffBase.contDiff.comp (contDiff_id.div_const _)

theorem cutoff_nonneg (n : ℕ) (x : ℝ) : 0 ≤ cutoff n x := cutoffBase.nonneg

theorem cutoff_le_one (n : ℕ) (x : ℝ) : cutoff n x ≤ 1 := cutoffBase.le_one

theorem norm_cutoff_le_one (n : ℕ) (x : ℝ) : ‖cutoff n x‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg n x)] using cutoff_le_one n x

theorem cutoff_eq_one {n : ℕ} {x : ℝ} (hx : |x| ≤ n+1) : cutoff n x = 1 := by
  apply cutoffBase.one_of_mem_closedBall
  change dist (x / (n+1 : ℝ)) 0 ≤ 1
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (by positivity : (0:ℝ) < n+1)]
  exact (div_le_one (by positivity)).mpr hx

theorem hasCompactSupport_cutoff (n : ℕ) : HasCompactSupport (cutoff n) := by
  change HasCompactSupport (fun x : ℝ => cutoffBase (x / (n+1 : ℝ)))
  simpa only [div_eq_mul_inv, mul_comm, smul_eq_mul] using
    cutoffBase.hasCompactSupport.comp_smul (c := (n+1 : ℝ)⁻¹) (by positivity)

theorem deriv_cutoff (n : ℕ) (x : ℝ) :
    deriv (cutoff n) x = deriv cutoffBase (x / (n+1 : ℝ)) / (n+1 : ℝ) := by
  have h := ((cutoffBase.contDiff : ContDiff ℝ 1 cutoffBase).differentiable one_ne_zero (x / (n+1 : ℝ))).hasDerivAt.comp x
    ((hasDerivAt_id x).div_const (n+1 : ℝ))
  change deriv (fun y : ℝ => cutoffBase (y / (n+1 : ℝ))) x = _
  simpa only [Function.comp_def, id_eq, one_div, ← div_eq_mul_inv] using h.deriv

/-- A finite constant suffices; no unsupported numerical bound on the bump is assumed. -/
theorem exists_norm_deriv_cutoff_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ n x, ‖deriv (cutoff n) x‖ ≤ C / (n+1 : ℝ) := by
  obtain ⟨C,hC⟩ := cutoffBase.hasCompactSupport.deriv.exists_bound_of_continuous
    (cutoffBase.contDiff : ContDiff ℝ 1 cutoffBase).continuous_deriv_one
  refine ⟨C, (norm_nonneg (deriv cutoffBase 0)).trans (hC 0), fun n x => ?_⟩
  rw [deriv_cutoff, norm_div, Real.norm_of_nonneg (show (0:ℝ) ≤ n+1 by positivity)]
  exact div_le_div_of_nonneg_right (hC _) (by positivity)

theorem tendsto_cutoff (x : ℝ) : Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => x / (n+1 : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul x
  have h := cutoffBase.continuous.continuousAt.tendsto.comp ht
  have hz : cutoffBase (0 : ℝ) = 1 := cutoffBase.one_of_mem_closedBall (by simpa using cutoffBase.rIn_pos.le)
  simpa only [hz, Function.comp_def, cutoff] using h

theorem tendsto_deriv_cutoff (x : ℝ) : Tendsto (fun n => deriv (cutoff n) x) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_norm_deriv_cutoff_le
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => hbound n x)
  simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C

/-- Truncated function and its a.e. derivative, before identification with `deriv`. -/
def truncateH1 (n : ℕ) (u : ℝ → ℝ) : ℝ → ℝ := fun x => cutoff n x * u x

def truncateH1Deriv (n : ℕ) (u g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv (cutoff n) x * u x + cutoff n x * g x

theorem memLp_truncateH1 {μ : Measure ℝ} {u : ℝ → ℝ} (hu : MemLp u 2 μ) (n : ℕ) :
    MemLp (truncateH1 n u) 2 μ := by
  apply hu.of_le ((contDiff_cutoff n).continuous.aestronglyMeasurable.mul hu.1)
  apply Eventually.of_forall
  intro x
  simpa only [truncateH1, Pi.mul_apply, norm_mul, one_mul] using
    mul_le_mul_of_nonneg_right (norm_cutoff_le_one n x) (norm_nonneg (u x))

theorem tendsto_cutoff_mul {μ : Measure ℝ} {u : ℝ → ℝ} (hu : MemLp u 2 μ) :
    Tendsto (fun n => (memLp_truncateH1 hu n).toLp (truncateH1 n u)) atTop (𝓝 (hu.toLp u)) := by
  apply tendsto_toLp_dominated μ (memLp_truncateH1 hu) hu hu.norm
  · intro n
    exact Eventually.of_forall (fun x => by
      simpa only [truncateH1, Pi.mul_apply, norm_mul, one_mul] using
        mul_le_mul_of_nonneg_right (norm_cutoff_le_one n x) (norm_nonneg (u x)))
  · exact Eventually.of_forall (fun x => by simpa [truncateH1] using (tendsto_cutoff x).mul_const (u x))

theorem truncateH1Deriv_bound {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n x, ‖deriv (cutoff n) x‖ ≤ C / (n+1 : ℝ)) (n : ℕ) (u g : ℝ → ℝ) (x : ℝ) :
    ‖truncateH1Deriv n u g x‖ ≤ C * ‖u x‖ + ‖g x‖ := by
  have hd : ‖deriv (cutoff n) x‖ ≤ C := (hb n x).trans
    ((div_le_self hC (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1:ℝ) ≤ n+1)))
  calc
    ‖truncateH1Deriv n u g x‖ ≤ ‖deriv (cutoff n) x‖ * ‖u x‖ + ‖cutoff n x‖ * ‖g x‖ := by
      simpa only [truncateH1Deriv, norm_mul] using norm_add_le (deriv (cutoff n) x * u x) (cutoff n x * g x)
    _ ≤ C * ‖u x‖ + 1 * ‖g x‖ := add_le_add (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (norm_cutoff_le_one n x) (norm_nonneg _))
    _ = _ := by ring

theorem memLp_truncateH1Deriv {μ : Measure ℝ} {u g : ℝ → ℝ}
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ) (n : ℕ) : MemLp (truncateH1Deriv n u g) 2 μ := by
  obtain ⟨C,hC,hb⟩ := exists_norm_deriv_cutoff_le
  apply ((hu.norm.const_mul C).add hg.norm).mono'
  · exact (((contDiff_cutoff n).of_le (by simp) : ContDiff ℝ 1 (cutoff n)).continuous_deriv_one.aestronglyMeasurable.mul hu.1).add
      ((contDiff_cutoff n).continuous.aestronglyMeasurable.mul hg.1)
  · exact Eventually.of_forall (truncateH1Deriv_bound hC hb n u g)

theorem tendsto_deriv_cutoff_mul {μ : Measure ℝ} {u g : ℝ → ℝ}
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ) :
    Tendsto (fun n => (memLp_truncateH1Deriv hu hg n).toLp (truncateH1Deriv n u g))
      atTop (𝓝 (hg.toLp g)) := by
  obtain ⟨C,hC,hb⟩ := exists_norm_deriv_cutoff_le
  apply tendsto_toLp_dominated μ (memLp_truncateH1Deriv hu hg) hg ((hu.norm.const_mul C).add hg.norm)
  · exact fun n => Eventually.of_forall (truncateH1Deriv_bound hC hb n u g)
  · exact Eventually.of_forall (fun x => by
      simpa only [truncateH1Deriv, zero_mul, one_mul, zero_add] using
        ((tendsto_deriv_cutoff x).mul_const (u x)).add ((tendsto_cutoff x).mul_const (g x)))

theorem absolutelyContinuous_truncateH1 {u : ℝ → ℝ}
    (hu : ∀ a b, AbsolutelyContinuousOnInterval u a b) (n : ℕ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (truncateH1 n u) a b :=
  (((contDiff_cutoff n).of_le (by simp) : ContDiff ℝ 1 (cutoff n)).contDiffOn.absolutelyContinuousOnInterval).fun_mul (hu a b)

theorem hasCompactSupport_truncateH1 (n : ℕ) (u : ℝ → ℝ) : HasCompactSupport (truncateH1 n u) :=
  (hasCompactSupport_cutoff n).mul_right

theorem ae_hasDerivAt_truncateH1 {u g : ℝ → ℝ}
    (hu : ∀ᵐ x ∂volume, HasDerivAt u (g x) x) (n : ℕ) :
    ∀ᵐ x ∂volume, HasDerivAt (truncateH1 n u) (truncateH1Deriv n u g x) x := by
  filter_upwards [hu] with x hx
  exact (((contDiff_cutoff n).differentiable (by simp) x).hasDerivAt.mul hx)

/-- R.1, in the stronger sequential form with explicit truncations and derivative classes. -/
theorem exists_truncation_tendsto {ρ g : ℝ → ℝ} (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (c : ℝ) (hu : MemLp (primitiveRepresentative c g) 2 (densityMeasure ρ))
    (hg : MemLp g 2 (densityMeasure ρ)) :
    ∃ (v h : ℕ → ℝ → ℝ) (hv : ∀ n, MemLp (v n) 2 (densityMeasure ρ))
      (hh : ∀ n, MemLp (h n) 2 (densityMeasure ρ)),
      (∀ n, v n = truncateH1 n (primitiveRepresentative c g)) ∧
      (∀ n, HasCompactSupport (v n)) ∧
      (∀ n a b, AbsolutelyContinuousOnInterval (v n) a b) ∧
      (∀ n, deriv (v n) =ᵐ[densityMeasure ρ] h n) ∧
      Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hu.toLp _)) ∧
      Tendsto (fun n => (hh n).toLp (h n)) atTop (𝓝 (hg.toLp g)) := by
  have hl := locallyIntegrable_of_memLp_density hρ hpos hg
  refine ⟨fun n => truncateH1 n (primitiveRepresentative c g),
    fun n => truncateH1Deriv n (primitiveRepresentative c g) g,
    memLp_truncateH1 hu, memLp_truncateH1Deriv hu hg, fun n => rfl,
    fun n => hasCompactSupport_truncateH1 n _,
    fun n => absolutelyContinuous_truncateH1 (absolutelyContinuousOnInterval_representative hl c) n,
    ?_, tendsto_cutoff_mul hu, tendsto_deriv_cutoff_mul hu hg⟩
  intro n
  apply (ae_densityMeasure_iff hρ.measurable hpos).mpr
  exact (ae_hasDerivAt_truncateH1 (ae_hasDerivAt_representative hl c) n).mono (fun x hx => hx.deriv)

end Foundations
