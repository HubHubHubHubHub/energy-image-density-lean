import ErrorCalculus.Dirichlet.ExtensionGammaBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Representatives commute almost everywhere with finite Lp sums. -/
theorem lp_coeFn_sum {p : ℝ≥0∞} {ι : Type*} (s : Finset ι) (f : ι → Lp ℝ p μ) :
    ⇑(∑ i ∈ s, f i) =ᵐ[μ] fun ω => ∑ i ∈ s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ p μ
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with ω ha hs
    simp only [ha, Pi.add_apply, hs]

/-- Multiplication of an Lp class by an essentially bounded scalar function. -/
def boundedMul {p : ℝ≥0∞} (c : Ω → ℝ) (hc : MemLp c ∞ μ) (f : Lp ℝ p μ) : Lp ℝ p μ :=
  ((Lp.memLp f).mul hc).toLp _

theorem coeFn_boundedMul {p : ℝ≥0∞} (c : Ω → ℝ) (hc : MemLp c ∞ μ) (f : Lp ℝ p μ) :
    ⇑(boundedMul c hc f) =ᵐ[μ] fun ω => c ω * f ω :=
  ((Lp.memLp f).mul hc).coeFn_toLp

theorem norm_boundedMul_le {p : ℝ≥0∞} (c : Ω → ℝ) (hc : MemLp c ∞ μ)
    (f : Lp ℝ p μ) {C : ℝ} (hC : ∀ᵐ ω ∂μ, |c ω| ≤ C) :
    ‖boundedMul c hc f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coeFn_boundedMul c hc f, hC] with ω he hb
  rw [he, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

theorem boundedMul_sub {p : ℝ≥0∞} (c : Ω → ℝ) (hc : MemLp c ∞ μ) (f g : Lp ℝ p μ) :
    boundedMul c hc (f-g) = boundedMul c hc f - boundedMul c hc g := by
  apply Lp.ext
  filter_upwards [coeFn_boundedMul c hc (f-g), coeFn_boundedMul c hc f,
    coeFn_boundedMul c hc g, Lp.coeFn_sub f g,
    Lp.coeFn_sub (boundedMul c hc f) (boundedMul c hc g)] with ω h1 h2 h3 h4 h5
  simp only [h1, h2, h3, h4, h5, Pi.sub_apply, mul_sub]

/-- L² norm squared in representative form. -/
theorem lp_two_norm_sq (f : Lp ℝ 2 μ) : ‖f‖^2 = ∫ ω, (f ω)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

/-- Dominated convergence to zero in L², stated for classes. -/
theorem lp_two_tendsto_zero_of_dominated (f : ℕ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ)
    (hb : ∀ n, ∀ᵐ ω ∂μ, |f n ω| ≤ |g ω|)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have hg : Integrable (fun ω => (g ω)^2) μ :=
    (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0:ℝ))
    (F := fun n ω => (f n ω)^2) (fun ω => (g ω)^2)
    (fun n => (Lp.aestronglyMeasurable (f n)).pow 2) hg (fun n => ?_) ?_
  · simp only [integral_zero] at h
    have hs := h.sqrt
    simp only [← lp_two_norm_sq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hs
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hs
  · filter_upwards [hb n] with ω hω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq).mpr hω
  · filter_upwards [ht] with ω hω
    simpa using hω.pow 2

/-- bounded coefficients vanishing a.e. times a fixed L² weight. -/
theorem boundedMul_tendsto_zero_two (c : ℕ → Ω → ℝ) (hc : ∀ n, MemLp (c n) ∞ μ)
    (g : Lp ℝ 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, ∀ᵐ ω ∂μ, |c n ω| ≤ C)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun n => c n ω) atTop (𝓝 0)) :
    Tendsto (fun n => boundedMul (c n) (hc n) g) atTop (𝓝 0) := by
  apply lp_two_tendsto_zero_of_dominated _ (C • g)
  · intro n
    filter_upwards [coeFn_boundedMul (c n) (hc n) g, Lp.coeFn_smul C g, hb n] with ω he hs hb
    simp only [he, hs, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  · filter_upwards [ae_all_iff.mpr (fun n => coeFn_boundedMul (c n) (hc n) g), ht] with ω he ht
    simp only [he]
    simpa using ht.mul_const (g ω)

/-- Dominated convergence for L¹ weights, used in the mixed chain-rule formula. -/
theorem boundedMul_tendsto_zero_one (c : ℕ → Ω → ℝ) (hc : ∀ n, MemLp (c n) ∞ μ)
    (g : Lp ℝ 1 μ) {C : ℝ}
    (hb : ∀ n, ∀ᵐ ω ∂μ, |c n ω| ≤ C)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun n => c n ω) atTop (𝓝 0)) :
    Tendsto (fun n => boundedMul (c n) (hc n) g) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hi := tendsto_integral_of_dominated_convergence (f := fun _ => (0:ℝ))
    (F := fun n ω => ‖c n ω * g ω‖) (fun ω => C * |g ω|)
    (fun n => ((hc n).1.mul (Lp.aestronglyMeasurable g)).norm)
    ((L1.integrable_coeFn g).norm.const_mul C) (fun n => ?_) ?_
  · simp only [integral_zero] at hi
    apply hi.congr'
    filter_upwards [] with n
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [coeFn_boundedMul (c n) (hc n) g] with ω hω
    rw [hω]
  · filter_upwards [hb n] with ω hω
    simp only [Real.norm_eq_abs, abs_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)
  · filter_upwards [ht] with ω hω
    simpa using (hω.mul_const (g ω)).norm

end ErrorCalculus
