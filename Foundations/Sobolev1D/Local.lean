import Foundations.Sections.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Order.Compact

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Foundations

/-- The measure with real density ρ relative to Lebesgue measure. -/
def densityMeasure (ρ : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (ρ x))

theorem exists_min_pos_on_Icc {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) (a b : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Icc a b, c ≤ ρ x :=
  isCompact_Icc.exists_forall_le' hρ.continuousOn (fun x _ => hpos x)

/-- Positive measurable densities have exactly the Lebesgue null sets. -/
theorem ae_densityMeasure_iff {ρ : ℝ → ℝ} (hρ : Measurable ρ)
    (hpos : ∀ x, 0 < ρ x) {P : ℝ → Prop} :
    (∀ᵐ x ∂densityMeasure ρ, P x) ↔ ∀ᵐ x ∂volume, P x := by
  rw [densityMeasure, ae_withDensity_iff (hρ.ennreal_ofReal)]
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le.mpr (hpos _), not_false_eq_true, true_implies]

/-- A local lower bound gives domination of restricted Lebesgue measure. -/
theorem restrict_volume_le_density {ρ : ℝ → ℝ} {K : Set ℝ} (hK : MeasurableSet K)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x ∈ K, c ≤ ρ x) :
    volume.restrict K ≤ (ENNReal.ofReal c)⁻¹ • densityMeasure ρ := by
  have hz : ENNReal.ofReal c ≠ 0 := by positivity
  have h : ENNReal.ofReal c • volume.restrict K ≤ densityMeasure ρ := by
    rw [← withDensity_const, ← withDensity_indicator hK]
    apply withDensity_mono
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ K
    · simpa [hx] using ENNReal.ofReal_le_ofReal (hlower x hx)
    · simp [hx]
  calc
    volume.restrict K = (ENNReal.ofReal c)⁻¹ • (ENNReal.ofReal c • volume.restrict K) := by
      rw [smul_smul, ENNReal.inv_mul_cancel hz ENNReal.ofReal_ne_top, one_smul]
    _ ≤ (ENNReal.ofReal c)⁻¹ • densityMeasure ρ := by gcongr

theorem exists_density_restrict_le {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ volume.restrict K ≤ C • densityMeasure ρ := by
  obtain ⟨c,hc,hl⟩ := hK.exists_forall_le' hρ.continuousOn (fun x _ => hpos x)
  exact ⟨(ENNReal.ofReal c)⁻¹, by simp [hc], restrict_volume_le_density hK.measurableSet hc hl⟩

/-- Hölder's inequality together with domination of measures, in a form used locally. -/
theorem integral_abs_le_of_measure_le_smul {μ ν : Measure ℝ} [IsFiniteMeasure ν]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hle : ν ≤ C • μ) {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    ∫ x, ‖f x‖ ∂ν ≤ ((C ^ (1/2 : ℝ)).toReal * (ν univ ^ (1/2 : ℝ)).toReal) * ‖hf.toLp f‖ := by
  have hl := hf.of_measure_le_smul hC hle
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hl.1
  have h2 := eLpNorm_le_of_measure_le_smul (f := f) (p := 2) hle
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, one_div_one, one_div, ENNReal.toReal_inv] at h1 h2
  have hh : eLpNorm f 1 ν ≤ (C ^ (1/2 : ℝ) * eLpNorm f 2 μ) * ν univ ^ (1/2 : ℝ) := by
    refine h1.trans ?_
    simpa only [smul_eq_mul] using mul_le_mul_left h2 (ν univ ^ (1/2 : ℝ))
  have ht : (C ^ (1/2 : ℝ) * eLpNorm f 2 μ) * ν univ ^ (1/2 : ℝ) ≠ ∞ := by finiteness
  have hr := ENNReal.toReal_mono ht hh
  rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hl.1] at hr
  simpa only [ENNReal.toReal_mul, Lp.norm_toLp, mul_assoc, mul_left_comm, mul_comm] using hr

theorem memLp_restrict_of_density {ρ f : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) (hf : MemLp f 2 (densityMeasure ρ))
    {K : Set ℝ} (hK : IsCompact K) : MemLp f 2 (volume.restrict K) := by
  obtain ⟨C,hC,hle⟩ := exists_density_restrict_le hρ hpos hK
  exact hf.of_measure_le_smul hC hle

theorem locallyIntegrable_of_memLp_density {ρ f : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) (hf : MemLp f 2 (densityMeasure ρ)) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact (memLp_restrict_of_density hρ hpos hf hK).integrable (by norm_num)

theorem integral_abs_le_of_density_pos {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℝ) (hf : MemLp f 2 (densityMeasure ρ)),
      ∫ x in K, ‖f x‖ ≤ C * ‖hf.toLp f‖ := by
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  obtain ⟨C,hC,hle⟩ := exists_density_restrict_le hρ hpos hK
  exact ⟨_, mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    fun f hf => integral_abs_le_of_measure_le_smul hC hle hf⟩

/-- Weighted L² convergence implies local L¹ convergence. -/
theorem tendsto_integral_abs_sub_of_density {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (densityMeasure ρ)) (hg : MemLp g 2 (densityMeasure ρ))
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    {K : Set ℝ} (hK : IsCompact K) :
    Tendsto (fun n => ∫ x in K, ‖f n x - g x‖) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := integral_abs_le_of_density_pos hρ hpos hK
  have hn : Tendsto (fun n => ‖(hf n).toLp (f n) - hg.toLp g‖) atTop (𝓝 0) := by
    simpa using (hlim.sub_const (hg.toLp g)).norm
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _))
    (fun n => hbound (f n - g) ((hf n).sub hg))
  have he : (fun n => C * ‖((hf n).sub hg).toLp (f n - g)‖) =
      (fun n => C * ‖(hf n).toLp (f n) - hg.toLp g‖) := by
    funext n
    exact congrArg (fun z : Lp ℝ 2 (densityMeasure ρ) => C * ‖z‖) ((hf n).toLp_sub hg)
  rw [he]
  simpa only [mul_zero] using hn.const_mul C

end Foundations
