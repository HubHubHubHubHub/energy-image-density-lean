import Foundations.LogSobolevD.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integrable_gaussianD_affine {E : Type*} [NormedAddCommGroup E]
    {f : (ι → ℝ) → E} (hf : Continuous f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (a b : ℝ) (x : ι → ℝ) :
    Integrable (fun y => f (fun i => a*x i+b*y i)) (gaussianProduct ι) := by
  exact (memLp_gaussianD_of_bounded (hf.comp (by fun_prop))
    (by obtain ⟨C,hC⟩ := hb; exact ⟨C,fun y => hC _⟩) 1).integrable le_rfl

theorem norm_mehlerKernelD_le {f : (ι → ℝ) → ℝ} {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (t : ℝ) (x : ι → ℝ) : ‖mehlerKernelD t f x‖ ≤ C :=
  (norm_integral_le_of_norm_le_const (ae_of_all _ (fun y => hC _))).trans_eq (by simp)

theorem le_mehlerKernelD {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) {c : ℝ} (hc : ∀ x, c ≤ f x) (t : ℝ) (x : ι → ℝ) :
    c ≤ mehlerKernelD t f x := by
  simpa [mehlerKernelD] using integral_mono (integrable_const c)
    (integrable_gaussianD_affine hf hb _ _ x) (fun y => hc _)

theorem mehlerKernelD_le {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) {c : ℝ} (hc : ∀ x, f x ≤ c) (t : ℝ) (x : ι → ℝ) :
    mehlerKernelD t f x ≤ c := by
  simpa [mehlerKernelD] using integral_mono
    (integrable_gaussianD_affine hf hb _ _ x) (integrable_const c) (fun y => hc _)

theorem continuous_mehlerKernelD {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Continuous (fun p : ℝ × (ι → ℝ) => mehlerKernelD p.1 f p.2) := by
  obtain ⟨C,hC⟩ := hb
  apply continuous_of_dominated (bound := fun _ => C)
  · intro p; exact (hf.comp (by fun_prop)).aestronglyMeasurable
  · intro p; exact ae_of_all _ (fun y => hC _)
  · exact integrable_const C
  · exact ae_of_all _ (fun y => hf.comp (by fun_prop))

theorem tendsto_mehlerKernelD_atTop {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (x : ι → ℝ) :
    Tendsto (fun t => mehlerKernelD t f x) atTop (𝓝 (∫ y, f y ∂gaussianProduct ι)) := by
  obtain ⟨C,hC⟩ := hb
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => C)
  · exact Eventually.of_forall fun t => (hf.comp (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => ae_of_all _ (fun y => hC _)
  · exact integrable_const C
  · refine ae_of_all _ (fun y => (hf.tendsto y).comp ?_)
    apply tendsto_pi_nhds.mpr
    intro i
    simpa using (tendsto_mehlerCoeffA_atTop.mul_const (x i)).add (tendsto_mehlerCoeffB_atTop.mul_const (y i))

theorem integral_mehlerKernelD {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, mehlerKernelD t f x ∂gaussianProduct ι) = ∫ x, f x ∂gaussianProduct ι := by
  have hmp := measurePreserving_mehlerMixD (ι := ι) ht
  have hi : Integrable (fun z => f (mehlerMixD t z)) ((gaussianProduct ι).prod (gaussianProduct ι)) := by
    obtain ⟨C,hC⟩ := hb
    exact (MemLp.of_bound (hf.comp (by unfold mehlerMixD; fun_prop)).aestronglyMeasurable C (ae_of_all _ (fun z => hC _)) (p := 1)).integrable le_rfl
  calc
    _ = ∫ z, f (mehlerMixD t z) ∂(gaussianProduct ι).prod (gaussianProduct ι) := (integral_prod_symm _ hi).symm
    _ = _ := by
      have hh := integral_map hmp.measurable.aemeasurable (f := f) (by rw [hmp.map_eq]; exact hf.aestronglyMeasurable)
      rw [hmp.map_eq] at hh
      exact hh.symm

theorem hasFDerivAt_mehlerKernelD {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (t : ℝ) (x : ι → ℝ) :
    HasFDerivAt (mehlerKernelD t f)
      (∫ y, mehlerCoeffA t • fderiv ℝ f (fun i => mehlerCoeffA t*x i+mehlerCoeffB t*y i) ∂gaussianProduct ι) x := by
  obtain ⟨C,hC0,hC⟩ := hf.fderiv_bounded
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := gaussianProduct ι)
    (F := fun x y => f (fun i => mehlerCoeffA t*x i+mehlerCoeffB t*y i))
    (F' := fun x y => mehlerCoeffA t • fderiv ℝ f (fun i => mehlerCoeffA t*x i+mehlerCoeffB t*y i))
    (bound := fun _ => ‖mehlerCoeffA t‖*C) (s := univ) (by simp)
  · exact Eventually.of_forall fun z => (hf.contDiff.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact integrable_gaussianD_affine hf.contDiff.continuous hf.bounded _ _ x
  · exact (((hf.contDiff.continuous_fderiv (by norm_num)).comp (show Continuous (fun y : ι → ℝ => fun i => mehlerCoeffA t*x i+mehlerCoeffB t*y i) from by fun_prop)).const_smul (mehlerCoeffA t)).aestronglyMeasurable
  · exact ae_of_all _ (fun y z _ => by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  · exact integrable_const _
  · refine ae_of_all _ (fun y z _ => ?_)
    have hd := (hf.hasFDerivAt _).comp z
      (((hasFDerivAt_id z).const_smul (mehlerCoeffA t)).add_const (mehlerCoeffB t • y))
    convert hd using 1
    · rfl
    · ext v
      simp [Pi.smul_def, Pi.add_def]

theorem partialD_mehlerKernelD {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (t : ℝ) (i : ι) (x : ι → ℝ) :
    partialD (mehlerKernelD t f) i x = mehlerCoeffA t * mehlerKernelD t (partialD f i) x := by
  obtain ⟨C,hC0,hC⟩ := hf.fderiv_bounded
  have hi : Integrable (fun y => mehlerCoeffA t • fderiv ℝ f
      (fun i => mehlerCoeffA t*x i+mehlerCoeffB t*y i)) (gaussianProduct ι) :=
    by
      simpa only [Pi.smul_def] using (integrable_gaussianD_affine (hf.contDiff.continuous_fderiv (by norm_num)) ⟨C,hC⟩ (mehlerCoeffA t) (mehlerCoeffB t) x).smul (mehlerCoeffA t)
  rw [partialD,(hasFDerivAt_mehlerKernelD hf t x).fderiv,ContinuousLinearMap.integral_apply hi]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,integral_const_mul,mehlerKernelD,partialD]

theorem isC1BoundedD_mehlerKernelD {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (t : ℝ) :
    IsC1BoundedD (mehlerKernelD t f) := by
  obtain ⟨C,hC0,hC⟩ := hf.fderiv_bounded
  refine ⟨contDiff_one_iff_fderiv.mpr ⟨fun x => (hasFDerivAt_mehlerKernelD hf t x).differentiableAt,?_⟩,?_,?_⟩
  · have he := funext (fun x => (hasFDerivAt_mehlerKernelD hf t x).fderiv)
    rw [he]
    apply continuous_of_dominated (bound := fun _ => ‖mehlerCoeffA t‖*C)
    · intro x; exact (((hf.contDiff.continuous_fderiv (by norm_num)).comp (show Continuous (fun y : ι → ℝ => fun i => mehlerCoeffA t*x i+mehlerCoeffB t*y i) from by fun_prop)).const_smul (mehlerCoeffA t)).aestronglyMeasurable
    · intro x; exact ae_of_all _ (fun y => by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
    · exact integrable_const _
    · refine ae_of_all _ (fun y => ?_)
      have hc := hf.contDiff.continuous_fderiv (by norm_num); fun_prop
  · obtain ⟨D,hD⟩ := hf.bounded
    exact ⟨D,fun x => norm_mehlerKernelD_le hD t x⟩
  · intro i
    obtain ⟨D,hD⟩ := hf.partial_bounded i
    refine ⟨‖mehlerCoeffA t‖*D,fun x => ?_⟩
    rw [partialD_mehlerKernelD hf,norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_mehlerKernelD_le hD t x) (norm_nonneg _)

theorem isC2BoundedD_mehlerKernelD {f : (ι → ℝ) → ℝ} (hf : IsC2BoundedD f) (t : ℝ) :
    IsC2BoundedD (mehlerKernelD t f) := by
  refine ⟨isC1BoundedD_mehlerKernelD hf.1 t,fun i => ?_⟩
  rw [funext (partialD_mehlerKernelD hf.1 t i)]
  exact (isC1BoundedD_mehlerKernelD (hf.2 i) t).const_mul _

theorem partialD2_mehlerKernelD {f : (ι → ℝ) → ℝ} (hf : IsC2BoundedD f) (t : ℝ) (i j : ι) (x : ι → ℝ) :
    partialD (partialD (mehlerKernelD t f) i) j x =
      (mehlerCoeffA t)^2 * mehlerKernelD t (partialD (partialD f i) j) x := by
  rw [funext (partialD_mehlerKernelD hf.1 t i),
    partialD_const_mul (isC1BoundedD_mehlerKernelD (hf.2 i) t),partialD_mehlerKernelD (hf.2 i)]
  ring

end Foundations
