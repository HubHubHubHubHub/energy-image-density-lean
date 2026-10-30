import ErrorCalculus.Dirichlet.ImageData
import ErrorCalculus.Dirichlet.Calculus
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {m : ℕ} (X : Fin m → Lp ℝ 2 μ)

/-- Pulling back a composition also pulls back each of its coordinates. -/
theorem pullback_composition {k : ℕ} (u : Fin k → Lp ℝ 2 (imageLaw X))
    (Φ : (Fin k → ℝ) → ℝ) (w : Lp ℝ 2 (imageLaw X))
    (hw : ⇑w =ᵐ[imageLaw X] fun x => Φ (fun i => u i x)) :
    ⇑(pullback X w) =ᵐ[μ] fun ω => Φ (fun i => pullback X (u i) ω) := by
  have hh := ae_eq_comp (measurable_imageRepresentative X).aemeasurable hw
  filter_upwards [pullback_ae_eq X w, hh, ae_all_iff.mpr (fun i => pullback_ae_eq X (u i))]
    with ω hω hwω huω
  simp only [Function.comp_apply] at hwω
  rw [hω, hwω]
  congr 1
  funext i
  exact (huω i).symm

/-- A Lipschitz function is square integrable for the law of an L² tuple. -/
theorem imageFunction_memLp [IsProbabilityMeasure μ] {F : (Fin m → ℝ) → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F) :
    MemLp F 2 (imageLaw X) := by
  apply (memLp_map_measure_iff hL.continuous.measurable.aestronglyMeasurable
    (measurable_imageRepresentative X).aemeasurable).mpr
  exact MemLp.ae_eq ((imageRepresentative_ae_eq X).symm.fun_comp F)
    (ErrorStructure.composition_memLp X hL)

/-- The pullback of an ordinary function is its evaluation on the source tuple. -/
theorem pullback_ofFunction {F : (Fin m → ℝ) → ℝ} (w : Lp ℝ 2 (imageLaw X))
    (hw : ⇑w =ᵐ[imageLaw X] F) :
    ⇑(pullback X w) =ᵐ[μ] fun ω => F (fun i => X i ω) := by
  exact (pullback_ae_eq X w).trans
    ((ae_eq_comp (measurable_imageRepresentative X).aemeasurable hw).trans
      ((imageRepresentative_ae_eq X).fun_comp F))

namespace ErrorStructure
variable [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) (hX : ∀ i, X i ∈ S.dom)
include hX

/-- all C¹ Lipschitz functions belong to the image domain, including m=0. -/
theorem imageDom_of_contDiff_lipschitz {F : (Fin m → ℝ) → ℝ} {L : ℝ≥0}
    (hC : ContDiff ℝ 1 F) (hL : LipschitzWith L F) (w : Lp ℝ 2 (imageLaw X))
    (hw : ⇑w =ᵐ[imageLaw X] F) : w ∈ S.toErrorData.imageDom X := by
  change pullback X w ∈ S.dom
  have ht := pullback_ofFunction X w hw
  by_cases hm : 0 < m
  · exact (S.calc m hm (fun i => ⟨X i, hX i⟩) F L hC hL (pullback X w) ht).choose
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    have he : pullback X w = Lp.const 2 μ (F 0) := by
      apply Lp.ext
      apply ht.trans
      apply EventuallyEq.trans _ (Lp.coeFn_const (p := 2) (μ := μ) (c := F 0)).symm
      exact ae_of_all _ fun ω => congrArg F (Subsingleton.elim _ _)
    rw [he]
    exact (S.constant_calculus (F 0)).choose

/-- smooth compactly supported functions give density for the image law. -/
theorem imageDom_dense : Dense (S.toErrorData.imageDom X : Set (Lp ℝ 2 (imageLaw X))) := by
  apply (Lp.dense_hasCompactSupport_contDiff (μ := imageLaw X) (E := Fin m → ℝ) (F := ℝ)
    (p := 2) (by norm_num)).mono
  rintro w ⟨F, hw, hc, hF⟩
  have hC : ContDiff ℝ 1 F := hF.of_le (by simp)
  obtain ⟨C, hCbound⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hC.continuous_fderiv (by norm_num))
  have hL : LipschitzWith (Real.toNNReal C) F := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hC.differentiable (by norm_num))
    intro x
    exact_mod_cast (hCbound x).trans (Real.le_coe_toNNReal C)
  exact S.imageDom_of_contDiff_lipschitz X hX hC hL w hw

end ErrorStructure
end ErrorCalculus
