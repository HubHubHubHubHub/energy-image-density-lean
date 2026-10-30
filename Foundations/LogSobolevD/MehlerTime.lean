import Foundations.LogSobolevD.Mehler
import Foundations.LogSobolevD.GaussianIBP

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def ouGeneratorD (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, (partialD (partialD f i) i x - x i*partialD f i x)

theorem hasDerivAt_mehlerKernelD_time_raw {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f)
    {t : ℝ} (ht : 0 < t) (x : ι → ℝ) :
    HasDerivAt (fun s => mehlerKernelD s f x)
      (∫ y, ∑ i, partialD f i (fun j => mehlerCoeffA t*x j+mehlerCoeffB t*y j) *
        (-mehlerCoeffA t*x i+(mehlerCoeffA t)^2/mehlerCoeffB t*y i) ∂gaussianProduct ι) t := by
  choose C hC using hf.partial_bounded
  have hC0 : ∀ i, 0 ≤ C i := fun i => (norm_nonneg _).trans (hC i 0)
  have hb0 := mehlerCoeffB_pos (half_pos ht)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := gaussianProduct ι)
    (F := fun s y => f (fun i => mehlerCoeffA s*x i+mehlerCoeffB s*y i))
    (F' := fun s y => ∑ i, partialD f i (fun j => mehlerCoeffA s*x j+mehlerCoeffB s*y j) *
      (-mehlerCoeffA s*x i+(mehlerCoeffA s)^2/mehlerCoeffB s*y i))
    (bound := fun y => ∑ i, C i*(‖x i‖+(1/mehlerCoeffB (t/2))*‖y i‖))
    (s := Ioi (t/2)) (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun s => (hf.contDiff.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_gaussianD_affine hf.contDiff.continuous hf.bounded _ _ x)
    (by have hc := hf.continuous_partial; fun_prop) ?_ ?_ ?_).2
  · refine ae_of_all _ (fun y s hs => ?_)
    have hs0 : 0 < s := (half_pos ht).trans hs
    have ha : ‖mehlerCoeffA s‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (mehlerCoeffA_pos s).le]
      exact mehlerCoeffA_le_one hs0.le
    have hb : ‖(mehlerCoeffA s)^2/mehlerCoeffB s‖ ≤ 1/mehlerCoeffB (t/2) := by
      rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (mehlerCoeffB_nonneg s))]
      apply div_le_div₀ zero_le_one ?_ hb0 (monotone_mehlerCoeffB hs.le)
      have ha' := mehlerCoeffA_le_one hs0.le
      nlinarith [mehlerCoeffA_pos s]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul]
    apply mul_le_mul (hC i _) ?_ (norm_nonneg _) (hC0 i)
    apply (norm_add_le _ _).trans
    simp only [norm_mul,norm_neg]
    exact add_le_add (by simpa using mul_le_mul_of_nonneg_right ha (norm_nonneg (x i)))
      (mul_le_mul_of_nonneg_right hb (norm_nonneg (y i)))
  · exact integrable_finsetSum _ (fun i _ =>
      (((integrable_const ‖x i‖).add ((integrable_gaussianD_coord i).norm.const_mul _)).const_mul (C i)))
  · refine ae_of_all _ (fun y s hs => ?_)
    have hd : HasDerivAt (fun s => fun i => mehlerCoeffA s*x i+mehlerCoeffB s*y i)
        (fun i => -mehlerCoeffA s*x i+(mehlerCoeffA s)^2/mehlerCoeffB s*y i) s :=
      hasDerivAt_pi.mpr (fun i => (hasDerivAt_mehlerCoeffA s).mul_const (x i) |>.add
        ((hasDerivAt_mehlerCoeffB ((half_pos ht).trans hs)).mul_const (y i)))
    apply ((hf.hasFDerivAt _).comp_hasDerivAt s hd).congr_deriv
    rw [fderiv_eq_sum_partialD]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- OU equation at strictly positive time, with the sum over all coordinates explicit. -/
theorem hasDerivAt_mehlerKernelD_time {f : (ι → ℝ) → ℝ} (hf : IsC2BoundedD f)
    {t : ℝ} (ht : 0 < t) (x : ι → ℝ) :
    HasDerivAt (fun s => mehlerKernelD s f x) (ouGeneratorD (mehlerKernelD t f) x) t := by
  apply (hasDerivAt_mehlerKernelD_time_raw hf.1 ht x).congr_deriv
  have hi (i : ι) := integrable_gaussianD_affine (hf.2 i).contDiff.continuous (hf.2 i).bounded
    (mehlerCoeffA t) (mehlerCoeffB t) x
  have hiy (i : ι) : Integrable (fun y => y i*partialD f i
      (fun j => mehlerCoeffA t*x j+mehlerCoeffB t*y j)) (gaussianProduct ι) :=
    integrable_coord_mul_boundedD ((hf.2 i).contDiff.continuous.comp (by fun_prop))
      (by obtain ⟨C,hC⟩ := (hf.2 i).bounded; exact ⟨C,fun y => hC _⟩) i
  have hint (i : ι) : Integrable (fun y => partialD f i (fun j => mehlerCoeffA t*x j+mehlerCoeffB t*y j)*
      (-mehlerCoeffA t*x i+(mehlerCoeffA t)^2/mehlerCoeffB t*y i)) (gaussianProduct ι) := by
    refine (((hi i).const_mul (-mehlerCoeffA t*x i)).add ((hiy i).const_mul ((mehlerCoeffA t)^2/mehlerCoeffB t))).congr (ae_of_all _ (fun y => ?_))
    dsimp
    ring
  rw [integral_finsetSum _ (fun i _ => hint i)]
  unfold ouGeneratorD
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (-mehlerCoeffA t*x i)*mehlerKernelD t (partialD f i) x +
        ((mehlerCoeffA t)^2/mehlerCoeffB t)*
          (∫ y, y i*partialD f i (mehlerCoeffA t • x+mehlerCoeffB t • y) ∂gaussianProduct ι) := by
      dsimp only [mehlerKernelD,Pi.add_def,Pi.smul_def,smul_eq_mul]
      rw [← integral_const_mul,← integral_const_mul,← integral_add ((hi i).const_mul _) ((hiy i).const_mul _)]
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring)
    _ = _ := by
      rw [integral_gaussianD_affine_partial (hf.2 i),partialD2_mehlerKernelD hf,partialD_mehlerKernelD hf.1]
      dsimp only [mehlerKernelD,Pi.add_def,Pi.smul_def,smul_eq_mul]
      field_simp [(mehlerCoeffB_pos ht).ne']
      <;> ring

theorem continuous_ouGeneratorD {f : (ι → ℝ) → ℝ} (hf : IsC2BoundedD f) :
    Continuous (ouGeneratorD f) := by
  unfold ouGeneratorD
  exact continuous_finset_sum _ (fun i _ => ((hf.2 i).continuous_partial i).sub
    ((continuous_apply i).mul (hf.1.continuous_partial i)))

/-- A time-independent integrable bound on the OU generator. -/
theorem norm_mehler_generatorD_le {f : (ι → ℝ) → ℝ} (hf : IsC2BoundedD f)
    {D E : ι → ℝ} (hD : ∀ i x, ‖partialD f i x‖ ≤ D i)
    (hE : ∀ i x, ‖partialD (partialD f i) i x‖ ≤ E i)
    {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    ‖ouGeneratorD (mehlerKernelD t f) x‖ ≤ ∑ i, (E i+‖x i‖*D i) := by
  have ha : ‖mehlerCoeffA t‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (mehlerCoeffA_pos t).le]; exact mehlerCoeffA_le_one ht
  have ha2 : ‖(mehlerCoeffA t)^2‖ ≤ 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg (mehlerCoeffA t)]
  unfold ouGeneratorD
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [partialD2_mehlerKernelD hf,partialD_mehlerKernelD hf.1]
  apply (norm_sub_le _ _).trans
  simp only [norm_mul]
  apply add_le_add
  · exact (mul_le_mul ha2 (norm_mehlerKernelD_le (hE i) t x) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · exact mul_le_mul_of_nonneg_left
      ((mul_le_mul ha (norm_mehlerKernelD_le (hD i) t x) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)) (norm_nonneg _)

end Foundations
