import Foundations.HypercontractivityD.Mollify
import Foundations.LogSobolevD.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ContDiff
namespace Foundations
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A smooth partial derivative is smooth, including mixed derivatives. -/
theorem contDiff_partialD {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : ι) :
    ContDiff ℝ ∞ (partialD f i) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_partialD {f : (ι → ℝ) → ℝ} (hf : HasCompactSupport f) (i : ι) :
    HasCompactSupport (partialD f i) := hf.fderiv_apply ℝ (Pi.single i 1)

theorem isC1BoundedD_of_smooth_compactSupport {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : IsC1BoundedD f :=
  ⟨hf.of_le (by simp), hc.exists_bound_of_continuous hf.continuous,
    fun i => (hasCompactSupport_partialD hc i).exists_bound_of_continuous
      (contDiff_partialD hf i).continuous⟩

theorem isC2BoundedD_of_smooth_compactSupport {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : IsC2BoundedD f :=
  ⟨isC1BoundedD_of_smooth_compactSupport hf hc, fun i =>
    isC1BoundedD_of_smooth_compactSupport (contDiff_partialD hf i) (hasCompactSupport_partialD hc i)⟩

/--
Compactly supported continuous approximation followed by local mollification gives smooth compactly
supported L² approximants.
-/
theorem exists_smooth_compactSupport_L2_approxD {μ : Measure (ι → ℝ)}
    [IsLocallyFiniteMeasure μ] [μ.Regular] (f : Lp ℝ 2 μ) {η : ℝ} (hη : 0 < η) :
    ∃ (g : (ι → ℝ) → ℝ) (hg : MemLp g 2 μ),
      ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ‖f-hg.toLp g‖ ≤ η := by
  obtain ⟨h,hc,hclose,hcont,hLp⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num) (ε := ENNReal.ofReal (η/2)) (by positivity)
  have hfh : ‖f-hLp.toLp h‖ ≤ η/2 := by
    have he : (Lp.memLp f).toLp (f : (ι → ℝ) → ℝ) = f := Lp.toLp_coeFn f (Lp.memLp f)
    rw [← he,← MemLp.toLp_sub,Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hclose).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (tendsto_L2_mollify_continuousD μ hcont hc)
    (η/2) (half_pos hη)
  let hg := memLp_mollify_compactD μ hcont hc N
  refine ⟨mollifyD h N,hg,contDiff_mollifyD hcont.locallyIntegrable N,
    hasCompactSupport_mollifyD hc N,?_⟩
  have hmid : ‖hg.toLp (mollifyD h N)-hLp.toLp h‖ < η/2 := by
    simpa only [dist_eq_norm] using hN N le_rfl
  have htri := dist_triangle f (hLp.toLp h) (hg.toLp (mollifyD h N))
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (hLp.toLp h)] at htri
  linarith

/-- A sequence version, retaining the smooth compact representatives and their L² classes. -/
theorem exists_smooth_compactSupport_L2_seqD {μ : Measure (ι → ℝ)}
    [IsLocallyFiniteMeasure μ] [μ.Regular] (f : Lp ℝ 2 μ) :
    ∃ (g : ℕ → (ι → ℝ) → ℝ) (hg : ∀ n, MemLp (g n) 2 μ),
      (∀ n, ContDiff ℝ ∞ (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 f) := by
  have hex (n : ℕ) := exists_smooth_compactSupport_L2_approxD f
    (η := 1/((n : ℝ)+1)) (by positivity)
  choose g hg hC hc hb using hex
  refine ⟨g,hg,hC,hc,?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε))
  refine ⟨N,fun n hn => ?_⟩
  rw [dist_eq_norm,norm_sub_rev]
  exact (hb n).trans_lt (hN n hn)

/-- The concrete density hypothesis needed by Nelson is a theorem, not an assumption. -/
theorem exists_C2b_L2_gaussianD_seq (f : Lp ℝ 2 (gaussianProduct ι)) :
    ∃ (g : ℕ → (ι → ℝ) → ℝ) (hg : ∀ n, IsC2BoundedD (g n)),
      Tendsto (fun n => ((hg n).1.memLp 2).toLp (g n)) atTop (𝓝 f) := by
  obtain ⟨g,hg,hC,hc,ht⟩ := exists_smooth_compactSupport_L2_seqD f
  exact ⟨g,fun n => isC2BoundedD_of_smooth_compactSupport (hC n) (hc n),ht⟩

end Foundations
