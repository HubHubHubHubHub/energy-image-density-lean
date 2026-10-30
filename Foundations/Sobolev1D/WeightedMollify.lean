import Foundations.Sobolev1D.MollifyL2

noncomputable section
open MeasureTheory Filter Set Function Metric ContinuousLinearMap
open scoped Topology ENNReal ContDiff Convolution Pointwise
namespace Foundations

/-- An upper bound for the density is only used on a fixed compact set. -/
theorem exists_density_restrict_upper {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    {K : Set ℝ} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ (densityMeasure ρ).restrict K ≤ C • volume := by
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hρ.continuousOn
  refine ⟨ENNReal.ofReal M, ENNReal.ofReal_ne_top, ?_⟩
  rw [densityMeasure, restrict_withDensity hK.measurableSet,
    ← withDensity_indicator hK.measurableSet, ← withDensity_const]
  apply withDensity_mono
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · simp only [indicator_of_mem hx]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM x hx))
  · simp only [indicator_of_notMem hx]
    exact bot_le

theorem memLp_of_restrict_support {μ : Measure ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (hK : MeasurableSet K) (hs : support f ⊆ K) (hf : MemLp f 2 (μ.restrict K)) :
    MemLp f 2 μ := by
  have h := (memLp_indicator_iff_restrict hK).mpr hf
  rwa [indicator_eq_self.mpr hs] at h

theorem memLp_volume_of_density_compact {ρ f : ℝ → ℝ}
    (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) (hf : MemLp f 2 (densityMeasure ρ))
    (hc : HasCompactSupport f) : MemLp f 2 volume :=
  memLp_of_restrict_support (isClosed_tsupport f).measurableSet (subset_tsupport f)
    (memLp_restrict_of_density hρ hpos hf hc.isCompact)

theorem memLp_density_of_volume_compact {ρ f : ℝ → ℝ} (hρ : Continuous ρ)
    (hf : MemLp f 2 volume) (hc : HasCompactSupport f) : MemLp f 2 (densityMeasure ρ) := by
  obtain ⟨C,hC,hle⟩ := exists_density_restrict_upper hρ hc.isCompact
  exact memLp_of_restrict_support (isClosed_tsupport f).measurableSet (subset_tsupport f)
    (hf.of_measure_le_smul hC hle)

theorem norm_toLp_le_of_restrict_le {μ ν : Measure ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hle : μ.restrict K ≤ C • ν) (hs : support f ⊆ K)
    (hf : MemLp f 2 μ) (hg : MemLp f 2 ν) :
    ‖hf.toLp f‖ ≤ (C ^ (1/2 : ℝ)).toReal * ‖hg.toLp f‖ := by
  have hh := eLpNorm_le_of_measure_le_smul (f := f) (p := 2) hle
  rw [eLpNorm_restrict_eq_of_support_subset hs] at hh
  norm_num only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hh
  have htop : C ^ (1/2 : ℝ) * eLpNorm f 2 ν ≠ ⊤ := by finiteness
  have h := ENNReal.toReal_mono htop hh
  simpa only [smul_eq_mul, ENNReal.toReal_mul, Lp.norm_toLp] using h

/-- On a common compact support, unweighted L² convergence implies weighted L² convergence. -/
theorem tendsto_L2_density_of_commonSupport {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hfρ : ∀ n, MemLp (f n) 2 (densityMeasure ρ)) (hgρ : MemLp g 2 (densityMeasure ρ))
    (hsf : ∀ n, support (f n) ⊆ K) (hsg : support g ⊆ K)
    (ht : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun n => (hfρ n).toLp (f n)) atTop (𝓝 (hgρ.toLp g)) := by
  obtain ⟨C,hC,hle⟩ := exists_density_restrict_upper hρ hK
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _)
    (g := fun n => (C^(1/2:ℝ)).toReal * ‖(hf n).toLp (f n) - hg.toLp g‖)
  · intro n
    have hs : support (f n-g) ⊆ K := (support_sub (f n) g).trans (union_subset (hsf n) hsg)
    have h := norm_toLp_le_of_restrict_le hC hle hs ((hfρ n).sub hgρ) ((hf n).sub hg)
    rwa [(hfρ n).toLp_sub hgρ, (hf n).toLp_sub hg] at h
  · simpa only [mul_zero] using
      (tendsto_iff_norm_sub_tendsto_zero.mp ht).const_mul (C^(1/2:ℝ)).toReal

theorem memLp_mollify_density {ρ f : ℝ → ℝ} (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (hf : MemLp f 2 (densityMeasure ρ)) (hc : HasCompactSupport f) (n : ℕ) :
    MemLp (mollify f n) 2 (densityMeasure ρ) :=
  memLp_density_of_volume_compact hρ
    (memLp_mollify (memLp_volume_of_density_compact hρ hpos hf hc) n)
    (hasCompactSupport_mollify hc n)

theorem tendsto_L2_mollify_density {ρ f : ℝ → ℝ} (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (hf : MemLp f 2 (densityMeasure ρ)) (hc : HasCompactSupport f) :
    Tendsto (fun n => (memLp_mollify_density hρ hpos hf hc n).toLp (mollify f n)) atTop
      (𝓝 (hf.toLp f)) := by
  let K := tsupport f + closedBall (0 : ℝ) 1
  have hK : IsCompact K := hc.isCompact.add (isCompact_closedBall _ _)
  have hfvol := memLp_volume_of_density_compact hρ hpos hf hc
  apply tendsto_L2_density_of_commonSupport hρ hK (fun n => memLp_mollify hfvol n) hfvol
    (memLp_mollify_density hρ hpos hf hc) hf (support_mollify_subset f) ?_ (tendsto_L2_mollify hfvol)
  intro x hx
  exact ⟨x, subset_tsupport f hx, 0, by simp, by simp⟩

/-- Local smoothing of an AC compactly supported function in the graph norm. -/
theorem exists_mollification_tendsto {ρ v : ℝ → ℝ} (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (hv : ∀ a b, AbsolutelyContinuousOnInterval v a b) (hc : HasCompactSupport v)
    (hvLp : MemLp v 2 (densityMeasure ρ)) (hdLp : MemLp (deriv v) 2 (densityMeasure ρ)) :
    ∃ (w : ℕ → ℝ → ℝ) (hw : ∀ n, MemLp (w n) 2 (densityMeasure ρ))
      (hdw : ∀ n, MemLp (deriv (w n)) 2 (densityMeasure ρ)),
      (∀ n, w n = mollify v n) ∧ (∀ n, ContDiff ℝ ∞ (w n)) ∧
      (∀ n, HasCompactSupport (w n)) ∧
      Tendsto (fun n => (hw n).toLp (w n)) atTop (𝓝 (hvLp.toLp v)) ∧
      Tendsto (fun n => (hdw n).toLp (deriv (w n))) atTop (𝓝 (hdLp.toLp (deriv v))) := by
  have hde (n) := deriv_mollify_eq_mollify_deriv hv hc n
  have hdw (n) : MemLp (deriv (mollify v n)) 2 (densityMeasure ρ) := by
    rw [hde n]
    exact memLp_mollify_density hρ hpos hdLp hc.deriv n
  refine ⟨mollify v, memLp_mollify_density hρ hpos hvLp hc, hdw, fun _ => rfl,
    contDiff_mollify (continuous_of_locallyAC hv).locallyIntegrable,
    hasCompactSupport_mollify hc, tendsto_L2_mollify_density hρ hpos hvLp hc, ?_⟩
  have he (n) : (hdw n).toLp (deriv (mollify v n)) =
      (memLp_mollify_density hρ hpos hdLp hc.deriv n).toLp (mollify (deriv v) n) := by
    apply Lp.ext
    filter_upwards [(hdw n).coeFn_toLp, (memLp_mollify_density hρ hpos hdLp hc.deriv n).coeFn_toLp] with x hx hy
    rw [hx, hy, hde n]
  simpa only [he] using tendsto_L2_mollify_density hρ hpos hdLp hc.deriv

end Foundations
