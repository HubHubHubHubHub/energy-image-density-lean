import GeometricMeasure.Current.DilationTests
import GeometricMeasure.Current.Compactness.Basic

/-!
# Dilations of measure currents

This file contains the results of the development of `GeometricMeasure.Current.Dilation` that the
main statements of the library (the head theorems listed in the README of the repository) use.
`GeometricMeasure.Current.Dilation` imports it and continues the development.

## Main statements

* `measureOneCurrent_add`: The one-current is additive in the vector measure: `measureOneCurrent (M
  + N) = measureOneCurrent M + measureOneCurrent N`.
* `measureOneCurrent_smul_map_dilation`: The one-current of `c • M.map (dilationEquiv x₀ r hr)` at
  `ω` equals `c` times the one-current of `M` at `dilationTest x₀ r hr ω`.
* `signedTestCurrent_smul`: The scalar current is homogeneous in the signed measure:
  `signedTestCurrent (c • D) = c • signedTestCurrent D` for every real `c`.
* `signedTestCurrent_map_dilation`: The current of `D.map (dilationEquiv x₀ r hr)` at a scalar test
  `φ` equals the current of `D` at `dilationTest x₀ r hr φ`.
* `signedTotalVariation_smul`: For every real `c`, the total variation of `c • D` is `‖c‖₊ •
  D.totalVariation`.
* `signedTotalVariation_map_equiv`: The total variation of the image `D.map e` of a signed measure
  under a measurable equivalence `e` is `D.totalVariation.map e`.
-/
noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d m : ℕ}

theorem vectorMeasurePairing_smul
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (c : ℝ) (ω : BoundedCovectorField d m) :
    vectorMeasurePairing (c • M) ω = c * vectorMeasurePairing M ω := by
  conv_lhs => rw [← withDensityᵥ_polarDensity M, ← withDensityᵥ_smul]
  rw [vectorMeasurePairing_withDensityᵥ _ ((integrable_polarDensity M).smul c)]
  simp only [Pi.smul_apply, map_smul, smul_eq_mul, integral_const_mul, vectorMeasurePairing]

theorem vectorMeasurePairing_add
    (M N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ω : BoundedCovectorField d m) :
    vectorMeasurePairing (M + N) ω = vectorMeasurePairing M ω + vectorMeasurePairing N ω := by
  let ν := M.variation + N.variation
  have hM : M.variation ≪ ν := Measure.AbsolutelyContinuous.mk (fun s _ hs => by
    exact (add_eq_zero.mp hs).1)
  have hN : N.variation ≪ ν := Measure.AbsolutelyContinuous.mk (fun s _ hs => by
    exact (add_eq_zero.mp hs).2)
  obtain ⟨f, _, hf, hfm⟩ := (absolutelyContinuous_iff_exists_density M ν).mp
    ((absolutelyContinuous_iff_variation M ν).mpr hM)
  obtain ⟨g, _, hg, hgn⟩ := (absolutelyContinuous_iff_exists_density N ν).mp
    ((absolutelyContinuous_iff_variation N ν).mpr hN)
  rw [← hfm, ← hgn, ← withDensityᵥ_add hf hg,
    vectorMeasurePairing_withDensityᵥ ν (hf.add hg), vectorMeasurePairing_withDensityᵥ ν hf,
    vectorMeasurePairing_withDensityᵥ ν hg]
  simp only [Pi.add_apply, map_add]
  exact integral_add (integrable_boundedCovector_apply ν hf ω)
    (integrable_boundedCovector_apply ν hg ω)

theorem measureOneCurrent_add
    (M N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d))) :
    measureOneCurrent (M + N) = measureOneCurrent M + measureOneCurrent N := by
  ext ω
  simpa only [vectorMeasurePairing_currentTest, add_apply] using
    vectorMeasurePairing_add M N (ω : BoundedCovectorField d d)

theorem measureOneCurrent_smul
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (c : ℝ) : measureOneCurrent (c • M) = c • measureOneCurrent M := by
  ext ω
  simpa only [vectorMeasurePairing_currentTest, smul_apply, smul_eq_mul] using
    vectorMeasurePairing_smul M c (ω : BoundedCovectorField d d)

theorem measureOneCurrent_map_dilation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (ω : OneFormCurrentTest d) :
    measureOneCurrent (M.map (dilationEquiv x₀ r hr)) ω =
      measureOneCurrent M (dilationTest x₀ r hr ω) := by
  rw [measureOneCurrent_apply, measureOneCurrent_apply,
    (dilationEquiv x₀ r hr).measurableEmbedding.variation_map]
  calc
    _ = ∫ y, ω y (polarDensity M ((dilationEquiv x₀ r hr).symm y))
        ∂(M.variation.map (dilationEquiv x₀ r hr)) :=
      integral_congr_ae ((polarDensity_map_equiv M _).mono (fun y hy => congrArg (ω y) hy))
    _ = _ := by rw [integral_map_equiv]; simp only [MeasurableEquiv.symm_apply_apply,
      dilationTest_apply]

theorem measureOneCurrent_smul_map_dilation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ)
    (ω : OneFormCurrentTest d) :
    measureOneCurrent (c • M.map (dilationEquiv x₀ r hr)) ω =
      c * measureOneCurrent M (dilationTest x₀ r hr ω) := by
  simp [measureOneCurrent_smul, measureOneCurrent_map_dilation]

theorem map_toSignedMeasure_equiv
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    (e : EuclideanSpace ℝ (Fin d) ≃ᵐ EuclideanSpace ℝ (Fin d)) :
    ν.toSignedMeasure.map e = (ν.map e).toSignedMeasure := by
  apply VectorMeasure.ext
  intro A hA
  rw [VectorMeasure.map_apply _ e.measurable hA,
    Measure.toSignedMeasure_apply_measurable (e.measurable hA),
    Measure.toSignedMeasure_apply_measurable hA]
  simp [measureReal_def, e.map_apply]

theorem signedTestCurrent_smul (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (c : ℝ) :
    signedTestCurrent (c • D) = c • signedTestCurrent D := by
  ext φ
  simp only [smul_apply, smul_eq_mul, signedTestCurrent_apply,
    SignedMeasure.toJordanDecomposition_smul_real]
  rcases le_or_gt 0 c with hc | hc
  · rw [JordanDecomposition.real_smul_posPart_nonneg _ _ hc,
      JordanDecomposition.real_smul_negPart_nonneg _ _ hc]
    simp [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, Real.toNNReal_of_nonneg hc, mul_sub]
  · rw [JordanDecomposition.real_smul_posPart_neg _ _ hc,
      JordanDecomposition.real_smul_negPart_neg _ _ hc]
    simp [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, Real.toNNReal_of_nonneg (neg_nonneg.mpr hc.le)]
    ring

theorem signedTestCurrent_map_dilation (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (φ : ScalarCurrentTest d) :
    signedTestCurrent (D.map (dilationEquiv x₀ r hr)) φ =
      signedTestCurrent D (dilationTest x₀ r hr φ) := by
  let e := dilationEquiv x₀ r hr
  have hrep : D.map e = (D.toJordanDecomposition.posPart.map e).toSignedMeasure -
      (D.toJordanDecomposition.negPart.map e).toSignedMeasure := by
    conv_lhs => rw [← D.toSignedMeasure_toJordanDecomposition]
    exact (map_sub (VectorMeasure.mapGm e) _ _).trans
      (by simp only [VectorMeasure.mapGm_apply, map_toSignedMeasure_equiv])
  rw [hrep, ← signedMeasurePairing_currentTest, signedMeasurePairing_sub,
    signedTestCurrent_apply, integral_map_equiv, integral_map_equiv]
  rfl

theorem signedTotalVariation_smul (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (c : ℝ) :
    (c • D).totalVariation = ‖c‖₊ • D.totalVariation := by
  simp only [SignedMeasure.totalVariation, SignedMeasure.toJordanDecomposition_smul_real]
  rcases le_or_gt 0 c with hc | hc
  · rw [JordanDecomposition.real_smul_posPart_nonneg _ _ hc,
      JordanDecomposition.real_smul_negPart_nonneg _ _ hc, ← smul_add]
    congr 1
    apply NNReal.eq
    simp [Real.toNNReal_of_nonneg hc, Real.norm_eq_abs, abs_of_nonneg hc]
  · rw [JordanDecomposition.real_smul_posPart_neg _ _ hc,
      JordanDecomposition.real_smul_negPart_neg _ _ hc, ← smul_add, add_comm]
    congr 1
    apply NNReal.eq
    simp [Real.toNNReal_of_nonneg (neg_nonneg.mpr hc.le), Real.norm_eq_abs, abs_of_neg hc]

theorem signedTotalVariation_map_equiv (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (e : EuclideanSpace ℝ (Fin d) ≃ᵐ EuclideanSpace ℝ (Fin d)) :
    SignedMeasure.totalVariation (D.map e) = D.totalVariation.map e := by
  let j : JordanDecomposition (EuclideanSpace ℝ (Fin d)) := {
    posPart := D.toJordanDecomposition.posPart.map e
    negPart := D.toJordanDecomposition.negPart.map e
    mutuallySingular := e.measurableEmbedding.mutuallySingular_map
      D.toJordanDecomposition.mutuallySingular }
  have hj : j.toSignedMeasure = D.map e := by
    conv_rhs => rw [← D.toSignedMeasure_toJordanDecomposition]
    change _ = VectorMeasure.mapGm e (_ - _)
    rw [map_sub]
    simp only [VectorMeasure.mapGm_apply, map_toSignedMeasure_equiv]
    rfl
  rw [← hj, SignedMeasure.totalVariation, JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  exact (Measure.map_add _ _ e.measurable).symm

end GeometricMeasure
