import ErrorCalculus.Dirichlet.LocalizedEID
import ErrorCalculus.Dirichlet.EIDConditionalGeneral
import ErrorCalculus.Dirichlet.EIDUniversal

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {n : ℕ}

/-- Transport the literal restricted EID law to EuclideanSpace with its volume normalization. -/
theorem eid_toEuclidean_of_eid (f : Fin n → S.dom) (h : S.eidMeasure f ≪ volume) :
    (μ.restrict {ω | 0 < (Matrix.of (fun i j => S.Γ (f i) (f j) ω)).det}).map
      (S.toEuclidean f) ≪ volume := by
  have H := h.map (euclideanEquiv n).continuous.measurable
  have hv : (volume : Measure (Fin n → ℝ)).map (euclideanEquiv n) = volume :=
    (PiLp.volume_preserving_toLp (Fin n)).map_eq
  rw [hv, eidMeasure, Measure.map_map (euclideanEquiv n).continuous.measurable
    (S.measurable_representativeVec f)] at H
  exact H

theorem eid_toEuclidean_of_generatorDom_of_DPR (f : Fin n → S.dom)
    (hDPR : DePhilippisRindler n) (hf : ∀ i, (f i : Lp ℝ 2 μ) ∈ S.generatorDom) :
    (μ.restrict {ω | 0 < (Matrix.of (fun i j => S.Γ (f i) (f j) ω)).det}).map
      (S.toEuclidean f) ≪ volume :=
  S.eid_toEuclidean_of_eid f (S.eid_of_generatorDom_of_DPR f hDPR hf)

theorem eid_of_DPR_toEuclidean (f : Fin n → S.dom) (hDPR : DePhilippisRindler n) :
    (μ.restrict {ω | 0 < (Matrix.of (fun i j => S.Γ (f i) (f j) ω)).det}).map
      (S.toEuclidean f) ≪ volume := S.eid_toEuclidean_of_eid f (S.eid_of_DPR f hDPR)

/-- Dimension one is unconditional, by scalar energy-image-density theorem. -/
theorem eid_n_one_unconditional (f : Fin 1 → S.dom) : S.eidMeasure f ≪ volume := by
  let e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have H := (S.map_restrict_gamma_pos_absolutelyContinuous (f 0)).map e.symm.measurable
  have hv : (volume : Measure ℝ).map e.symm = volume :=
    ((volume_preserving_funUnique (Fin 1) ℝ).symm e).map_eq
  rw [hv, Measure.map_map e.symm.measurable (Lp.stronglyMeasurable (f 0 : Lp ℝ 2 μ)).measurable] at H
  have hdet : {ω | 0 < (Matrix.of (fun i j => S.Γ (f i) (f j) ω)).det} =
      {ω | 0 < S.Γ (f 0) (f 0) ω} := by
    ext ω
    simp [Matrix.det_fin_one]
  unfold eidMeasure
  rw [hdet]
  have he : (fun ω => e.symm ((f 0 : Lp ℝ 2 μ) ω)) =ᵐ[μ] S.representativeVec f := by
    filter_upwards [S.coeFn_representativeVec f] with ω hω
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [e, hi] using congrFun hω i
  rw [← Measure.map_congr (ae_restrict_of_ae he)]
  exact H

/--
stronger regularity assumptions give EID without DPR. In addition to boundedness, requires domain
representatives of Γ and global positive determinant.
-/
theorem eid_of_gamma_det_pos (hn : 0 < n) (f : Fin n → S.dom)
    (hf : ∀ i, (f i : Lp ℝ 2 μ) ∈ S.generatorDom)
    (hΓ : ∀ i j, ∃ v : S.dom, ⇑(v : Lp ℝ 2 μ) =ᵐ[μ] S.Γ (f i) (f j) ∧
      AEBounded (μ := μ) (v : Lp ℝ 2 μ))
    (hdet : ∀ᵐ ω ∂μ, 0 < (Matrix.of (fun i j => S.Γ (f i) (f j) ω)).det) :
    S.eidMeasure f ≪ volume := by
  have h := S.absolutelyContinuous_map_representativeVec_of_det_pos hn f hf hΓ hdet
  rw [← S.eidImageLaw_eq_map] at h
  exact (S.eidMeasure_absolutelyContinuous_imageLaw f).trans h

/-- Algebraic sign check: boundary −2I and the result of incorrectly inserting
σ = −2Af μ in the definition with −∫φ dσ agree only when the pairing I vanishes. -/
theorem boundary_divergence_sign_check (I : ℝ) : -(2 * I) = -((-2) * I) ↔ I = 0 := by
  constructor <;> intro h <;> linarith

end ErrorCalculus.ErrorStructure
