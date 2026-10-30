import ErrorCalculus.Dirichlet.OUDLogSobolevC2
import Foundations.HypercontractivityD.Density

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set Topology ContinuousLinearMap
open scoped Convolution
namespace ErrorCalculus
variable {d : ℕ}

/-- Differentiation on the bounded C¹ factor, with an integrable compact kernel.
This is the version not directly supplied by Mathlib's compact-factor derivative lemmas. -/
theorem hasFDerivAt_convolution_C1b {f k : (Fin d → ℝ) → ℝ}
    (hf : ErrorCalculus.IsC1BoundedD f) (hk : Continuous k) (hc : HasCompactSupport k)
    (x : Fin d → ℝ) :
    HasFDerivAt (k ⋆[lsmul ℝ ℝ, volume] f)
      (∫ y, k y • fderiv ℝ f (x-y)) x := by
  obtain ⟨C, hC⟩ := hf.2.2
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F' := fun x y => k y • fderiv ℝ f (x-y)) (bound := fun y => ‖k y‖ * C)
    (by simp)
  · exact Eventually.of_forall fun x =>
      (hk.mul (hf.1.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact hc.convolutionExists_left_of_continuous_right (lsmul ℝ ℝ)
      hk.locallyIntegrable hf.1.continuous x
  · exact (hk.smul (hf.continuous_fderiv.comp
      (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact ae_of_all _ fun y x _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · exact (hk.integrable_of_hasCompactSupport hc).norm.mul_const C
  · exact ae_of_all _ fun y x _ => by
      convert ((hf.differentiable (x-y)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const y)).const_smul (k y) using 1 <;> simp [Function.comp_def, Pi.smul_def, smul_eq_mul]

/-- Convolution commutes with each first partial derivative of a bounded C¹ function. -/
theorem partialD_mollifyD {f : (Fin d → ℝ) → ℝ}
    (hf : ErrorCalculus.IsC1BoundedD f) (n : ℕ) (i : Fin d) :
    Foundations.partialD (Foundations.mollifyD f n) i =
      Foundations.mollifyD (Foundations.partialD f i) n := by
  let k := (Foundations.mollifierD (Fin d) n).normed volume
  have hk : Continuous k :=
    (show ContDiff ℝ 1 k from (Foundations.mollifierD (Fin d) n).contDiff_normed).continuous
  have hc : HasCompactSupport k := (Foundations.mollifierD (Fin d) n).hasCompactSupport_normed
  funext x
  rw [Foundations.partialD, Foundations.mollify_eq_leftD,
    (hasFDerivAt_convolution_C1b hf hk hc x).fderiv]
  have hi : Integrable (fun y => k y • fderiv ℝ f (x-y)) volume :=
    hc.convolutionExists_left_of_continuous_right (lsmul ℝ ℝ)
      hk.locallyIntegrable hf.continuous_fderiv x
  rw [ContinuousLinearMap.integral_apply hi, Foundations.mollify_eq_leftD]
  rfl

/-- Differentiating the smooth kernel needs only local integrability of the other factor. -/
theorem partialD_mollifyD_kernel {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (n : ℕ) (i : Fin d) :
    Foundations.partialD (Foundations.mollifyD f n) i =
      (Foundations.partialD ((Foundations.mollifierD (Fin d) n).normed volume) i)
        ⋆[lsmul ℝ ℝ, volume] f := by
  funext x
  rw [Foundations.partialD, Foundations.mollifyD,
    ((Foundations.mollifierD (Fin d) n).hasCompactSupport_normed.hasFDerivAt_convolution_right
      (lsmul ℝ ℝ) hf.locallyIntegrable
      (show ContDiff ℝ 1 _ from (Foundations.mollifierD (Fin d) n).contDiff_normed) x).fderiv,
    convolution_precompR_apply (lsmul ℝ ℝ) hf.locallyIntegrable
      ((Foundations.mollifierD (Fin d) n).hasCompactSupport_normed.fderiv ℝ)
      ((show ContDiff ℝ 1 _ from (Foundations.mollifierD (Fin d) n).contDiff_normed).continuous_fderiv (by norm_num))]
  exact congrFun (Foundations.real_convolution_commD _ _) x

theorem bounded_convolution_left {f k : (Fin d → ℝ) → ℝ}
    (_hf : Continuous f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hk : Continuous k) (hc : HasCompactSupport k) :
    ∃ C : ℝ, ∀ x, ‖(k ⋆[lsmul ℝ ℝ, volume] f) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨(∫ y, ‖k y‖) * C, fun x => ?_⟩
  calc
    _ ≤ ∫ y, ‖k y * f (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖k y‖ * C := by
      apply integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
        ((hk.integrable_of_hasCompactSupport hc).norm.mul_const C)
      exact ae_of_all _ fun y => by
        dsimp only
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    _ = _ := integral_mul_const C _

theorem bounded_mollifyD {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (n : ℕ) :
    ∃ C : ℝ, ∀ x, ‖Foundations.mollifyD f n x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hb
  exact ⟨C, Foundations.norm_mollify_leD hf.aestronglyMeasurable
    ((norm_nonneg (f 0)).trans (hC 0)) hC n⟩

/-- A bounded continuous function has bounded smooth regularizations and bounded first partials. -/
theorem foundations_isC1BoundedD_mollify {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (n : ℕ) :
    Foundations.IsC1BoundedD (Foundations.mollifyD f n) := by
  refine ⟨(Foundations.contDiff_mollifyD hf.locallyIntegrable n).of_le (by simp),
    bounded_mollifyD hf hb n, fun i => ?_⟩
  rw [partialD_mollifyD_kernel hf]
  exact bounded_convolution_left hf hb
    (Foundations.contDiff_partialD (Foundations.mollifierD (Fin d) n).contDiff_normed i).continuous
    (Foundations.hasCompactSupport_partialD
      (Foundations.mollifierD (Fin d) n).hasCompactSupport_normed i)

/-- C¹_b regularizes to C²_b; the second derivatives differentiate the kernel. -/
theorem isC2BoundedD_mollifyD {f : (Fin d → ℝ) → ℝ}
    (hf : ErrorCalculus.IsC1BoundedD f) (n : ℕ) :
    Foundations.IsC2BoundedD (Foundations.mollifyD f n) := by
  refine ⟨foundations_isC1BoundedD_mollify hf.1.continuous hf.2.1 n, fun i => ?_⟩
  rw [partialD_mollifyD hf]
  exact foundations_isC1BoundedD_mollify
    ((foundations_isC1BoundedD hf).continuous_partial i)
    ((foundations_isC1BoundedD hf).partial_bounded i) n

/-- Pointwise convergence only requires continuity, including for the first partials. -/
theorem tendsto_mollifyD_pointwise {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (x : Fin d → ℝ) :
    Tendsto (fun n => Foundations.mollifyD f n x) atTop (𝓝 (f x)) := by
  simp_rw [Foundations.mollify_eq_leftD]
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    Foundations.mollifier_radius_tendstoD hf x

/-- Dominated convergence for any finite measure, hence also the explicit OU density. -/
theorem tendsto_mollifyD_L2 {μ : Measure (Fin d → ℝ)} [IsFiniteMeasure μ]
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun n => ((isC1BoundedD_of_foundations
      (foundations_isC1BoundedD_mollify hf hb n)).memLp μ 2).toLp (Foundations.mollifyD f n))
      atTop (𝓝 ((MemLp.of_bound hf.aestronglyMeasurable hb.choose
        (ae_of_all _ hb.choose_spec) : MemLp f 2 μ).toLp f)) := by
  apply Foundations.tendsto_toLp_dominated μ _ _ (memLp_const hb.choose)
  · intro n
    exact ae_of_all _ (Foundations.norm_mollify_leD hf.aestronglyMeasurable
      ((norm_nonneg (f 0)).trans (hb.choose_spec 0)) hb.choose_spec n)
  · exact ae_of_all _ (tendsto_mollifyD_pointwise hf)

theorem tendsto_mollifyD_L2_gaussian {f : (Fin d → ℝ) → ℝ}
    (hf : ErrorCalculus.IsC1BoundedD f) :
    Tendsto (fun n => (ouDOfFunction (Foundations.mollifyD f n)
      (isC1BoundedD_of_foundations (isC2BoundedD_mollifyD hf n).1) :
        Lp ℝ 2 (densityMeasureD (ouDensityD d)))) atTop
      (𝓝 (ouDOfFunction f hf : Lp ℝ 2 (densityMeasureD (ouDensityD d)))) :=
  tendsto_mollifyD_L2 hf.1.continuous hf.2.1

end ErrorCalculus
