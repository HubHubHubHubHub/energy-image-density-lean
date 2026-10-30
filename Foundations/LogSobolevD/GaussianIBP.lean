import Foundations.LogSobolevD.Basic
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Refreshing one coordinate of a product Gaussian preserves its law. -/
theorem measurePreserving_gaussianD_update (i : ι) :
    MeasurePreserving (fun z : (ι → ℝ) × (ι → ℝ) => Function.update z.1 i (z.2 i))
      ((gaussianProduct ι).prod (gaussianProduct ι)) (gaussianProduct ι) := by
  let F : ι → ℝ × ℝ → ℝ := fun j => if j = i then Prod.snd else Prod.fst
  have hF : ∀ j, MeasurePreserving (F j) (standardGaussian.prod standardGaussian) standardGaussian := by
    intro j
    dsimp [F]
    split_ifs
    · exact measurePreserving_snd
    · exact measurePreserving_fst
  have hp := measurePreserving_pi (fun _ : ι => standardGaussian.prod standardGaussian)
    (fun _ : ι => standardGaussian) hF
  have he := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun _ => standardGaussian) (fun _ => standardGaussian)).symm
  convert hp.comp he using 1
  ext z j
  by_cases h : j = i <;> simp [F,Function.update_apply,h] <;> rfl

theorem integral_gaussianD_update {f : (ι → ℝ) → ℝ}
    (hc : Continuous f) (hi : Integrable f (gaussianProduct ι)) (i : ι) :
    (∫ x, f x ∂gaussianProduct ι) =
      ∫ x, ∫ z, f (Function.update x i z) ∂standardGaussian ∂gaussianProduct ι := by
  have hp := measurePreserving_gaussianD_update i
  have hin := hp.integrable_comp_of_integrable hi
  calc
    _ = ∫ z, f (Function.update z.1 i (z.2 i)) ∂(gaussianProduct ι).prod (gaussianProduct ι) := by
      have hh := integral_map hp.measurable.aemeasurable (f := f) (by rw [hp.map_eq]; exact hc.aestronglyMeasurable)
      rwa [hp.map_eq] at hh
    _ = ∫ x, ∫ y, f (Function.update x i (y i)) ∂gaussianProduct ι ∂gaussianProduct ι := integral_prod _ hin
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => integral_comp_eval (μ := fun _ : ι => standardGaussian) (i := i) ((hc.comp (contDiff_update (𝕜 := ℝ) 1 x i).continuous).aestronglyMeasurable))

theorem hasDerivAt_gaussianD_slice {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f)
    (i : ι) (x : ι → ℝ) (z : ℝ) :
    HasDerivAt (fun y => f (Function.update x i y)) (partialD f i (Function.update x i z)) z :=
  (hf.hasFDerivAt _).comp_hasDerivAt z (hasDerivAt_update x i z)

theorem IsC1BoundedD.slice {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (i : ι) (x : ι → ℝ) :
    IsC1Bounded (fun z => f (Function.update x i z)) := by
  refine ⟨hf.contDiff.comp (contDiff_update 1 x i),?_,?_⟩
  · obtain ⟨C,hC⟩ := hf.bounded
    exact ⟨C,fun z => hC _⟩
  · obtain ⟨D,hD⟩ := hf.partial_bounded i
    exact ⟨D,fun z => by rw [(hasDerivAt_gaussianD_slice hf i x z).deriv]; exact hD _⟩

theorem integrable_gaussianD_coord (i : ι) : Integrable (fun x : ι → ℝ => x i) (gaussianProduct ι) := by
  apply integrable_eval
  convert integrable_pow_gaussian 1 using 1
  funext x
  simp

theorem integrable_coord_mul_boundedD {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (i : ι) :
    Integrable (fun x => x i*f x) (gaussianProduct ι) := by
  obtain ⟨C,hC⟩ := hb
  apply ((integrable_gaussianD_coord i).norm.mul_const C).mono' (by fun_prop)
  exact ae_of_all _ (fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))

/-- Product Gaussian integration by parts, proved by refreshing one coordinate and Fubini. -/
theorem integral_partialD_gaussian {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (i : ι) :
    (∫ x, partialD f i x ∂gaussianProduct ι) = ∫ x, x i*f x ∂gaussianProduct ι := by
  rw [integral_gaussianD_update (hf.continuous_partial i) ((hf.memLp_partial i 1).integrable le_rfl) i,
    integral_gaussianD_update (by have hc := hf.contDiff.continuous; fun_prop)
      (integrable_coord_mul_boundedD hf.contDiff.continuous hf.bounded i) i]
  apply integral_congr_ae
  refine ae_of_all _ (fun x => ?_)
  have h := integral_deriv_gaussian (hf.slice i x)
  simpa only [(funext fun z => (hasDerivAt_gaussianD_slice hf i x z).deriv),Function.update_self] using h

/-- Coordinate derivative after a common scalar dilation and vector translation. -/
theorem partialD_affine {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f)
    (a : ι → ℝ) (b : ℝ) (i : ι) (x : ι → ℝ) :
    partialD (fun y => f (a+b • y)) i x = b*partialD f i (a+b • x) := by
  have hd := (hf.hasFDerivAt _).comp x (((hasFDerivAt_id x).const_smul b).const_add a)
  have he := congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) hd.fderiv
  simpa [partialD, Function.comp_def] using he

theorem IsC1BoundedD.affine {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f)
    (a : ι → ℝ) (b : ℝ) : IsC1BoundedD (fun y => f (a+b • y)) := by
  refine ⟨hf.contDiff.comp (by fun_prop),?_,fun i => ?_⟩
  · obtain ⟨C,hC⟩ := hf.bounded
    exact ⟨C,fun _ => hC _⟩
  · obtain ⟨C,hC⟩ := hf.partial_bounded i
    refine ⟨‖b‖*C,fun x => ?_⟩
    rw [partialD_affine hf,norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

theorem integral_gaussianD_affine_partial {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f)
    (a : ι → ℝ) (b : ℝ) (i : ι) :
    (∫ y, y i*f (a+b • y) ∂gaussianProduct ι) =
      b*∫ y, partialD f i (a+b • y) ∂gaussianProduct ι := by
  rw [← integral_partialD_gaussian (hf.affine a b) i,← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ (fun y => partialD_affine hf a b i y))

end Foundations
