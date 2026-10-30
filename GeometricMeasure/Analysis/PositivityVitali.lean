import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Positivity, local Vitali convergence and tails

## Main results
For an integrable zero-mean sequence tₙ with tₙ + hₙ ≥ 0 and hₙ converging in L¹, local
convergence in measure of the negative parts on a finite-measure exhaustion implies tₙ → 0 in L¹.
The ambient
measure may be infinite.

Reference: De Philippis–Rindler, arXiv p. 13, Lemma 2.2(c). The printed integral over B₁ in that
argument must be read over E.
The measure-theoretic arguments use Mathlib.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace GeometricMeasure.StrongConstancy
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Real L¹ convergence and the extended L¹ seminorm have the same zero limit. -/
theorem l1_tendsto_iff {f : ℕ → α → ℝ} (hf : ∀ n, Integrable (f n) μ) :
    Tendsto (fun n => ∫ x, ‖f n x‖ ∂μ) atTop (𝓝 0) ↔
      Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0) := by
  have he n : eLpNorm (f n) 1 μ = ENNReal.ofReal (∫ x, ‖f n x‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ofReal_integral_norm_eq_lintegral_enorm (hf n)]
  simp_rw [he]
  constructor
  · intro h
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  · intro h
    have hh := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp h
    simpa only [Function.comp_def, ENNReal.toReal_zero,
      ENNReal.toReal_ofReal (integral_nonneg (fun _ => norm_nonneg _))] using hh

/-- Uniform absolute continuity of the integrals passes to a dominated family. -/
theorem unifIntegrable_of_norm_le {f g : ℕ → α → ℝ}
    (hg : UnifIntegrable g 1 μ) (hfg : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖g n x‖) :
    UnifIntegrable f 1 μ := by
  classical
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hg hε
  refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
  apply le_trans (eLpNorm_mono_ae ?_) (hb n s hs hμs)
  filter_upwards [hfg n] with x hx
  simp only [Set.indicator_apply]
  split_ifs <;> simp_all

/-- Strong L¹ convergence gives uniform integrability, globally and after restriction. -/
theorem unifIntegrable_of_l1_tendsto {h : ℕ → α → ℝ} {g : α → ℝ}
    (hh : ∀ n, Integrable (h n) μ) (hg : Integrable g μ)
    (hc : Tendsto (fun n => ∫ x, ‖h n x - g x‖ ∂μ) atTop (𝓝 0)) :
    UnifIntegrable h 1 μ :=
  unifIntegrable_of_tendsto_Lp le_rfl (by simp)
    (fun n => memLp_one_iff_integrable.mpr (hh n)) (memLp_one_iff_integrable.mpr hg)
    ((l1_tendsto_iff (fun n => (hh n).sub hg)).mp hc)

/-- Positivity of t+h controls the negative part of t. -/
theorem negative_part_le {t h : ℝ} (hz : 0 ≤ t + h) :
    0 ≤ max 0 (-t) ∧ max 0 (-t) ≤ ‖h‖ := by
  refine ⟨le_max_left _ _, max_le (norm_nonneg _) ?_⟩
  have := le_abs_self h
  rw [Real.norm_eq_abs]
  linarith

/-- Local Vitali for a nonnegative sequence; strict superlevels suffice. -/
theorem vitali_nonnegative [IsFiniteMeasure μ] {f : ℕ → α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hpos : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x)
    (hui : UnifIntegrable f 1 μ)
    (hm : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => μ {x | δ < f n x}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 0) := by
  have hc : TendstoInMeasure μ f atTop (fun _ => (0 : ℝ)) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hm (ε / 2) (half_pos hε)) (fun _ => bot_le)
    intro n
    apply measure_mono_ae
    filter_upwards [hpos n] with x hx
    change ε ≤ ‖f n x - 0‖ → ε / 2 < f n x
    rw [sub_zero, Real.norm_of_nonneg hx]
    intro he
    linarith
  have hh := tendsto_Lp_finite_of_tendstoInMeasure (p := 1) le_rfl (by simp)
    (fun n => (hf n).aestronglyMeasurable) MemLp.zero hui hc
  simp only [sub_zero] at hh
  have hr := (l1_tendsto_iff hf).mpr hh
  convert hr using 1
  ext n
  apply integral_congr_ae
  filter_upwards [hpos n] with x hx
  exact (Real.norm_of_nonneg hx).symm

/-- The tails of a fixed L¹ function vanish along every measurable exhaustion. -/
theorem l1_tails {g : α → ℝ} (hg : Integrable g μ)
    (s : ℕ → Set α) (hs : ∀ k, MeasurableSet (s k))
    (hmono : Monotone s) (hcover : ⋃ k, s k = univ) :
    Tendsto (fun k => ∫ x in (s k)ᶜ, ‖g x‖ ∂μ) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone (fun k => (hs k).compl)
    (fun i j hij => compl_subset_compl.mpr (hmono hij))
    (f := fun x => ‖g x‖) (μ := μ) ⟨0, hg.norm.integrableOn⟩
  have he : (⋂ k, (s k)ᶜ) = (∅ : Set α) := by
    rw [← compl_iUnion, hcover, compl_univ]
  simpa only [he, Measure.restrict_empty, integral_zero_measure] using h

/-- Tail estimate for the positivity argument, with no compact support assumption on the errors. -/
theorem dominated_tail_bound {f h g : α → ℝ}
    (hf : Integrable f μ) (hh : Integrable h μ) (hg : Integrable g μ)
    (hfg : ∀ᵐ x ∂μ, f x ≤ ‖h x‖) (s : Set α) :
    (∫ x in sᶜ, f x ∂μ) ≤
      (∫ x, ‖h x - g x‖ ∂μ) + ∫ x in sᶜ, ‖g x‖ ∂μ := by
  calc
    _ ≤ ∫ x in sᶜ, (‖h x - g x‖ + ‖g x‖) ∂μ := by
      apply integral_mono_ae hf.integrableOn (((hh.sub hg).norm.add hg.norm).integrableOn)
      filter_upwards [ae_restrict_of_ae hfg] with x hx
      exact hx.trans (norm_le_norm_sub_add _ _)
    _ = (∫ x in sᶜ, ‖h x - g x‖ ∂μ) + ∫ x in sᶜ, ‖g x‖ ∂μ :=
      integral_add (hh.sub hg).norm.integrableOn hg.norm.integrableOn
    _ ≤ _ := add_le_add
      (setIntegral_le_integral (hh.sub hg).norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))) le_rfl

/-- Local Vitali plus the tails yields the global L¹ conclusion. -/
theorem dominated_local_to_global {f h : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hh : ∀ n, Integrable (h n) μ)
    (hg : Integrable g μ) (hpos : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x)
    (hdom : ∀ n, ∀ᵐ x ∂μ, f n x ≤ ‖h n x‖)
    (hc : Tendsto (fun n => ∫ x, ‖h n x - g x‖ ∂μ) atTop (𝓝 0))
    (s : ℕ → Set α) (hs : ∀ k, MeasurableSet (s k))
    (hmono : Monotone s) (hcover : ⋃ k, s k = univ)
    (hlocal : ∀ k, Tendsto (fun n => ∫ x in s k, f n x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n => ha.trans_le (integral_nonneg_of_ae (hpos n)))
  · intro ε hε
    obtain ⟨k, hk⟩ := (l1_tails hg s hs hmono hcover).eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / 3 by linarith)) |>.exists
    filter_upwards [(hlocal k).eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by linarith)),
      hc.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by linarith))] with n hn hc'
    have hb := dominated_tail_bound (hf n) (hh n) hg (hdom n) (s k)
    have he := integral_add_compl (hs k) (hf n)
    linarith

/--
If tₙ is integrable with zero mean, tₙ + hₙ ≥ 0, hₙ → g in L¹, and the negative parts of tₙ tend
locally to zero in measure on an increasing measurable finite-measure exhaustion, then tₙ → 0 and tₙ
+ hₙ → g in L¹. The ambient measure may be infinite.

Reference: De Philippis–Rindler, arXiv p. 13, Lemma 2.2; its integral over B₁ must be read over E.
-/
theorem positivity_zero_mass {t h : ℕ → α → ℝ} {g : α → ℝ}
    (ht : ∀ n, Integrable (t n) μ) (hh : ∀ n, Integrable (h n) μ)
    (hg : Integrable g μ) (hz : ∀ n, ∀ᵐ x ∂μ, 0 ≤ t n x + h n x)
    (hmass : ∀ n, (∫ x, t n x ∂μ) = 0)
    (hc : Tendsto (fun n => ∫ x, ‖h n x - g x‖ ∂μ) atTop (𝓝 0))
    (s : ℕ → Set α) (hs : ∀ k, MeasurableSet (s k))
    (hfinite : ∀ k, μ (s k) ≠ ⊤) (hmono : Monotone s) (hcover : ⋃ k, s k = univ)
    (hlevel : ∀ k δ, 0 < δ → Tendsto
      (fun n => (μ.restrict (s k)) {x | δ < max 0 (-t n x)}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖t n x‖ ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ x, ‖t n x + h n x - g x‖ ∂μ) atTop (𝓝 0) := by
  let f : ℕ → α → ℝ := fun n x => max 0 (-t n x)
  have hf n : Integrable (f n) μ := by
    convert (ht n).neg.pos_part using 1
    funext x
    exact max_comm _ _
  have hpos n : ∀ᵐ x ∂μ, 0 ≤ f n x := Filter.Eventually.of_forall (fun _ => le_max_left _ _)
  have hdom n : ∀ᵐ x ∂μ, f n x ≤ ‖h n x‖ := (hz n).mono (fun _ hx => (negative_part_le hx).2)
  have hui : UnifIntegrable f 1 μ := unifIntegrable_of_norm_le
    (unifIntegrable_of_l1_tendsto hh hg hc) (fun n => by
      filter_upwards [hpos n, hdom n] with x hp hd
      simpa only [Real.norm_of_nonneg hp] using hd)
  have hlocal k : Tendsto (fun n => ∫ x in s k, f n x ∂μ) atTop (𝓝 0) := by
    letI : IsFiniteMeasure (μ.restrict (s k)) := ⟨by simpa using (hfinite k).lt_top⟩
    exact vitali_nonnegative (fun n => (hf n).integrableOn)
      (fun n => ae_restrict_of_ae (hpos n)) (hui.restrict (s k)) (hlevel k)
  have hf0 := dominated_local_to_global hf hh hg hpos hdom hc s hs hmono hcover hlocal
  have hid n : (∫ x, ‖t n x‖ ∂μ) = 2 * ∫ x, f n x ∂μ := by
    have he : (fun x => ‖t n x‖) = fun x => t n x + 2 * f n x := by
      funext x
      dsimp [f]
      rcases le_total 0 (t n x) with hp | hn
      · rw [abs_of_nonneg hp, max_eq_left (by linarith)]
        ring
      · rw [abs_of_nonpos hn, max_eq_right (by linarith)]
        ring
    rw [he, integral_add (ht n) ((hf n).const_mul 2), integral_const_mul, hmass, zero_add]
  have ht0 : Tendsto (fun n => ∫ x, ‖t n x‖ ∂μ) atTop (𝓝 0) := by
    simpa only [hid, mul_zero] using hf0.const_mul 2
  refine ⟨ht0, squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _)) ?_
    (by simpa only [add_zero] using ht0.add hc)⟩
  intro n
  calc
    _ ≤ ∫ x, (‖t n x‖ + ‖h n x - g x‖) ∂μ := by
      apply integral_mono (((ht n).add (hh n)).sub hg).norm
        ((ht n).norm.add ((hh n).sub hg).norm)
      intro x
      change ‖t n x + h n x - g x‖ ≤ ‖t n x‖ + ‖h n x - g x‖
      rw [add_sub_assoc]
      exact norm_add_le _ _
    _ = _ := integral_add (ht n).norm ((hh n).sub hg).norm

end GeometricMeasure.StrongConstancy
