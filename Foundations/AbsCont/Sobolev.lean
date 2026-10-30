import Foundations.AbsCont.TotalVariation
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.LpSpace.Complete

noncomputable section
open MeasureTheory Filter Set Function ContinuousLinearMap
open scoped Topology ENNReal NNReal ContDiff
namespace Foundations
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [HasContDiffBump E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem exists_norm_fderiv_acCutoff_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ n x, ‖fderiv ℝ (acCutoff (E := E) n) x‖ ≤ C / (n+1:ℝ) := by
  let χ : ContDiffBump (0:E) := default
  have hc : ContDiff ℝ 1 χ := χ.contDiff
  obtain ⟨C,hC⟩ := (χ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hc.continuous_fderiv one_ne_zero)
  refine ⟨C, (norm_nonneg _).trans (hC 0), fun n x => ?_⟩
  have hd : fderiv ℝ (acCutoff (E := E) n) x =
      fderiv ℝ χ ((n+1:ℝ)⁻¹ • x) ∘L ((n+1:ℝ)⁻¹ • ContinuousLinearMap.id ℝ E) :=
    ((hc.differentiable one_ne_zero _).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul (n+1:ℝ)⁻¹)).fderiv
  rw [hd]
  calc
    _ ≤ ‖fderiv ℝ χ ((n+1:ℝ)⁻¹ • x)‖ * ‖(n+1:ℝ)⁻¹ • ContinuousLinearMap.id ℝ E‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * ((n+1:ℝ)⁻¹ * 1) := by
      gcongr
      · exact (norm_nonneg _).trans (hC 0)
      · exact hC _
      · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (by positivity)
    _ = _ := by simp [div_eq_mul_inv]

theorem tendsto_fderiv_acCutoff (x : E) :
    Tendsto (fun n => fderiv ℝ (acCutoff (E := E) n) x) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := exists_norm_fderiv_acCutoff_le (E := E)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => hb n x)
  simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C

/-- Removing compact support from the endpoint Sobolev inequality by smooth truncation and Fatou. -/
theorem eLpNorm_le_eLpNorm_fderiv_one_of_integrable {g : E → ℝ}
    (hg : ContDiff ℝ 1 g) (hi : Integrable g) (hd : Integrable (fderiv ℝ g))
    {p : ℝ≥0} (hp : NNReal.HolderConjugate (Module.finrank ℝ E) p) :
    eLpNorm g p ≤ eLpNormLESNormFDerivOneConst (volume : Measure E) p *
      eLpNorm (fderiv ℝ g) 1 := by
  let u : ℕ → E → ℝ := fun n x => acCutoff n x * g x
  have hu (n : ℕ) : ContDiff ℝ 1 (u n) := ((contDiff_acCutoff n).of_le (by simp)).mul hg
  have huk (n : ℕ) : HasCompactSupport (u n) := (hasCompactSupport_acCutoff n).mul_right
  have hud (n : ℕ) (x : E) : fderiv ℝ (u n) x =
      acCutoff n x • fderiv ℝ g x + g x • fderiv ℝ (acCutoff n) x :=
    fderiv_fun_mul ((contDiff_acCutoff n).differentiable (by simp) x)
      (hg.differentiable one_ne_zero x)
  obtain ⟨C,hC,hCb⟩ := exists_norm_fderiv_acCutoff_le (E := E)
  have hb (n : ℕ) (x : E) : ‖fderiv ℝ (u n) x‖ ≤ ‖fderiv ℝ g x‖ + C * ‖g x‖ := by
    rw [hud]
    have hcn : ‖acCutoff n x‖ ≤ 1 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (acCutoff_mem_Icc n x).1] using (acCutoff_mem_Icc n x).2
    have hdn : ‖fderiv ℝ (acCutoff n) x‖ ≤ C := (hCb n x).trans
      (div_le_self hC (by linarith [Nat.cast_nonneg (α := ℝ) n]))
    calc
      _ ≤ ‖acCutoff n x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ (acCutoff n) x‖ := by
        simpa only [norm_smul] using norm_add_le
          (acCutoff n x • fderiv ℝ g x) (g x • fderiv ℝ (acCutoff n) x)
      _ ≤ 1 * ‖fderiv ℝ g x‖ + ‖g x‖ * C := by gcongr
      _ = _ := by ring
  have ht (x : E) : Tendsto (fun n => fderiv ℝ (u n) x) atTop (𝓝 (fderiv ℝ g x)) := by
    simp_rw [hud]
    simpa using ((tendsto_acCutoff x).smul_const (fderiv ℝ g x)).add
      ((tendsto_fderiv_acCutoff x).const_smul (g x))
  have hI : Tendsto (fun n => ∫ x, ‖fderiv ℝ (u n) x‖) atTop
      (𝓝 (∫ x, ‖fderiv ℝ g x‖)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖fderiv ℝ g x‖ + C * ‖g x‖)
    · intro n; exact ((hu n).continuous_fderiv one_ne_zero).norm.aestronglyMeasurable
    · exact hd.norm.add (hi.norm.const_mul C)
    · intro n; exact Eventually.of_forall fun x => by simpa only [norm_norm] using hb n x
    · exact Eventually.of_forall fun x => (ht x).norm
  have hLp : Tendsto (fun n => eLpNorm (fderiv ℝ (u n)) 1) atTop
      (𝓝 (eLpNorm (fderiv ℝ g) 1)) := by
    have he (n : ℕ) : eLpNorm (fderiv ℝ (u n)) 1 = ENNReal.ofReal (∫ x, ‖fderiv ℝ (u n) x‖) := by
      rw [eLpNorm_one_eq_lintegral_enorm, ofReal_integral_norm_eq_lintegral_enorm]
      exact ((hu n).continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport ((huk n).fderiv ℝ)
    simp_rw [he]
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hd]
    exact ENNReal.continuous_ofReal.tendsto _ |>.comp hI
  let K : ℝ≥0∞ := eLpNormLESNormFDerivOneConst (volume : Measure E) p
  have hKL : Tendsto (fun n => K * eLpNorm (fderiv ℝ (u n)) 1) atTop
      (𝓝 (K * eLpNorm (fderiv ℝ g) 1)) := ENNReal.Tendsto.const_mul hLp (Or.inr ENNReal.coe_ne_top)
  have hFatou : eLpNorm g (p : ℝ≥0∞) volume ≤ atTop.liminf (fun n => eLpNorm (u n) (p : ℝ≥0∞) volume) := by
    exact Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := (volume : Measure E))
      (p := (p : ℝ≥0∞)) (f := u) (fun n => (hu n).continuous.aestronglyMeasurable) g
      (Eventually.of_forall fun x => by simpa [u] using (tendsto_acCutoff x).mul_const (g x))
  have hGNS : atTop.liminf (fun n => eLpNorm (u n) (p : ℝ≥0∞) volume) ≤
      atTop.liminf (fun n => K * eLpNorm (fderiv ℝ (u n)) 1 volume) := by
    exact liminf_le_liminf (Eventually.of_forall fun n =>
      eLpNorm_le_eLpNorm_fderiv_one (volume : Measure E) (u := u n) (p := p) (hu n) (huk n) hp)
  exact hFatou.trans (hGNS.trans_eq hKL.liminf_eq)

end Foundations
