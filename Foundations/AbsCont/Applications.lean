import Foundations.AbsCont.Criterion
import Foundations.AbsCont.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section
open MeasureTheory Filter Set Function ContinuousLinearMap
open scoped Topology ENNReal ContDiff BoundedContinuousFunction
namespace Foundations

/-- Transport of the normalized integration-by-parts hypothesis. -/
theorem HasIBPBound.map_equiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    {ν : Measure E} (e : E ≃L[ℝ] F) {v : E} {C : ℝ} (hb : HasIBPBound ν v C) :
    HasIBPBound (ν.map e) (e v) C := by
  intro φ hφ hφk hφb
  have H := hb (φ ∘ e) (hφ.comp e.contDiff) (hφk.comp_homeomorph e.toHomeomorph)
    (fun x => hφb (e x))
  have he (x : E) : fderiv ℝ (φ ∘ e) x v = fderiv ℝ φ (e x) (e v) := by
    rw [fderiv_comp x (hφ.differentiable (by simp) (e x)) e.differentiableAt, e.fderiv]
    rfl
  simp_rw [he] at H
  rwa [integral_map e.continuous.measurable.aemeasurable
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable)]

/-- The normalized version, all positive dimensions. -/
theorem absolutelyContinuous_of_hasIBPBound {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    {C : Fin d → ℝ} (hb : ∀ i, HasIBPBound ν (EuclideanSpace.basisFun (Fin d) ℝ i) (C i)) :
    ν ≪ volume := by
  by_cases hdim : d = 1
  · subst d
    let e : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
    have he : e (EuclideanSpace.basisFun (Fin 1) ℝ 0) = 1 := by
      rw [EuclideanSpace.basisFun_apply]
      exact (OrthonormalBasis.singleton (Fin 1) ℝ).repr_symm_single 0 |>.trans (by simp)
    have H := (hb 0).map_equiv e.toContinuousLinearEquiv
    change HasIBPBound (ν.map e) (e (EuclideanSpace.basisFun (Fin 1) ℝ 0)) (C 0) at H
    rw [he] at H
    have hac := absolutelyContinuous_of_integral_deriv_le_real (ν.map e) H
    have ha := e.symm.toHomeomorph.measurableEmbedding.absolutelyContinuous_map hac
    change (ν.map e).map e.symm ≪ (volume : Measure ℝ).map e.symm at ha
    rw [e.symm.measurePreserving.map_eq, Measure.map_map e.symm.continuous.measurable e.continuous.measurable] at ha
    simp only [Function.comp_def, e.symm_apply_apply] at ha
    change ν.map id ≪ volume at ha
    simpa only [Measure.map_id] using ha
  · exact absolutelyContinuous_of_integral_deriv_le_of_two_le (by omega) ν hb

/-- The classical supremum-norm formulation for smooth compact tests. -/
theorem absolutelyContinuous_of_integral_deriv_le {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    {C : Fin d → ℝ} (hC : ∀ i, 0 ≤ C i)
    (hb : ∀ i (φ : EuclideanSpace ℝ (Fin d) →ᵇ ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      |∫ x, fderiv ℝ φ x (EuclideanSpace.basisFun (Fin d) ℝ i) ∂ν| ≤ C i * ‖φ‖) :
    ν ≪ volume := by
  apply absolutelyContinuous_of_hasIBPBound hd ν (C := C)
  intro i φ hφ hφk hφb
  let f : EuclideanSpace ℝ (Fin d) →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup φ hφ.continuous 1 hφb
  have H := hb i f hφ hφk
  have hnf : ‖f‖ ≤ (1 : ℝ) :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hφ.continuous zero_le_one hφb
  have hmul : C i * ‖f‖ ≤ C i :=
    (mul_le_mul_of_nonneg_left hnf (hC i)).trans_eq (mul_one _)
  exact H.trans hmul

/-- Probabilistic form: integration-by-parts bounds on X imply a density for its law. -/
theorem absolutelyContinuous_map_of_ibp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {d : ℕ} (hd : 1 ≤ d)
    {X : Ω → EuclideanSpace ℝ (Fin d)} (hX : Measurable X)
    {C : Fin d → ℝ} (hC : ∀ i, 0 ≤ C i)
    (hb : ∀ i (φ : EuclideanSpace ℝ (Fin d) →ᵇ ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      |∫ a : Ω, fderiv ℝ φ (X a) (EuclideanSpace.basisFun (Fin d) ℝ i) ∂P| ≤ C i * ‖φ‖) :
    P.map X ≪ volume := by
  apply absolutelyContinuous_of_integral_deriv_le hd (P.map X) hC
  intro i φ hφ hk
  rw [integral_map hX.aemeasurable
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable)]
  exact hb i φ hφ hk

end Foundations
