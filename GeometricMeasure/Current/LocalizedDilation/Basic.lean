import GeometricMeasure.Current.Dilation.Basic

/-!
# Localized dilations of currents

This file contains the definitions and results of the development of
`GeometricMeasure.Current.LocalizedDilation` that the main statements of the library (the head
theorems listed in the README of the repository) use, together with the basic API of their
definitions. `GeometricMeasure.Current.LocalizedDilation` imports it and continues the development.

## Main definitions

* `localizedDilation`: The image under `dilationEquiv x₀ r hr` of the restriction of `M` to
  `closedBall x₀ |r|`, multiplied by `c`.
* `HasMeasureDivergenceOn`: `D` is the divergence of `M` on `U`: on every scalar test supported in
  `U`, the current of `D` equals minus the boundary of the one-current of `M`.

## Main statements

* `variation_localizedDilation_univ`: The total variation of `localizedDilation M x₀ r hr c` is `|c|
  * M.variation (closedBall x₀ |r|)`.
* `variation_localizedDilation_compl`: The variation of `localizedDilation M x₀ r hr c` vanishes
  outside `closedBall 0 1`.
* `hasMeasureDivergenceOn_localizedDilation`: If `D` is the divergence of `M`, then `(c * r) •
  (D.restrict (closedBall x₀ |r|)).map (dilationEquiv x₀ r hr)` is the divergence of
  `localizedDilation M x₀ r hr c` on `ball 0 1`.
-/
noncomputable section
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d m : ℕ}

/-- The image under `dilationEquiv x₀ r hr` of the restriction of `M` to `closedBall x₀ |r|`,
multiplied by `c`. -/
def localizedDilation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)) :=
  c • (M.restrict (Metric.closedBall x₀ |r|)).map (dilationEquiv x₀ r hr)

theorem variation_localizedDilation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    (localizedDilation M x₀ r hr c).variation =
      ‖c‖₊ • ((M.variation.restrict (Metric.closedBall x₀ |r|)).map (dilationEquiv x₀ r hr)) := by
  rw [localizedDilation, VectorMeasure.variation_smul,
    (dilationEquiv x₀ r hr).measurableEmbedding.variation_map,
    VectorMeasure.variation_restrict measurableSet_closedBall]

theorem variation_localizedDilation_univ
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    (localizedDilation M x₀ r hr c).variation univ =
      ENNReal.ofReal |c| * M.variation (Metric.closedBall x₀ |r|) := by
  rw [variation_localizedDilation, Measure.smul_apply, (dilationEquiv x₀ r hr).map_apply]
  change (‖c‖₊ : ℝ≥0∞) * _ = _
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_eq_abs]
  simp

theorem variation_localizedDilation_compl
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    (localizedDilation M x₀ r hr c).variation
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 := by
  rw [variation_localizedDilation, Measure.smul_apply, (dilationEquiv x₀ r hr).map_apply,
    preimage_compl, preimage_closedBall_dilation, mul_one,
    Measure.restrict_apply measurableSet_closedBall.compl]
  simp

/-- `D` is the divergence of `M` on `U`: on every scalar test supported in `U`, the current of `D`
equals minus the boundary of the one-current of `M`. -/
def HasMeasureDivergenceOn
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (U : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ φ : ScalarCurrentTest d, tsupport (φ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ U →
    signedTestCurrent D φ = -oneCurrentBoundary (measureOneCurrent M) φ

theorem measureOneCurrent_restrict_of_tsupport_subset
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) (ω : OneFormCurrentTest d)
    (hs : tsupport (ω : EuclideanSpace ℝ (Fin d) → _) ⊆ A) :
    measureOneCurrent (M.restrict A) ω = measureOneCurrent M ω := by
  rw [measureOneCurrent_apply, measureOneCurrent_apply, VectorMeasure.variation_restrict hA]
  calc
    _ = ∫ x in A, ω x (polarDensity M x) ∂M.variation :=
      integral_congr_ae ((polarDensity_restrict M hA).mono (fun x hx => congrArg (ω x) hx))
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]; rfl)

theorem signedTestCurrent_restrict_of_tsupport_subset
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) (φ : ScalarCurrentTest d)
    (hs : tsupport (φ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ A) :
    signedTestCurrent (D.restrict A) φ = signedTestCurrent D φ := by
  have hrep : D.restrict A = (D.toJordanDecomposition.posPart.restrict A).toSignedMeasure -
      (D.toJordanDecomposition.negPart.restrict A).toSignedMeasure := by
    conv_lhs => rw [← D.toSignedMeasure_toJordanDecomposition]
    rw [JordanDecomposition.toSignedMeasure, VectorMeasure.restrict_sub,
      VectorMeasure.restrict_toSignedMeasure hA, VectorMeasure.restrict_toSignedMeasure hA]
  rw [hrep, ← signedMeasurePairing_currentTest, signedMeasurePairing_sub, signedTestCurrent_apply]
  have hz : ∀ x, x ∉ A → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
  change (∫ x in A, φ x ∂D.toJordanDecomposition.posPart) -
    (∫ x in A, φ x ∂D.toJordanDecomposition.negPart) = _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    setIntegral_eq_integral_of_forall_compl_eq_zero hz]

theorem tsupport_dilationTest_subset_closedBall {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0)
    (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞))
    (hs : tsupport (φ : EuclideanSpace ℝ (Fin d) → F) ⊆ Metric.closedBall 0 1) :
    tsupport (dilationTest x₀ r hr φ : EuclideanSpace ℝ (Fin d) → F) ⊆
      Metric.closedBall x₀ |r| := by
  rw [tsupport_dilationTest, ← mul_one |r|, ← preimage_closedBall_dilation x₀ r hr 1]
  exact preimage_mono hs

theorem boundary_localizedDilation_apply
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (hdiv : HasMeasureDivergence M D)
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ)
    (φ : ScalarCurrentTest d)
    (hφ : tsupport (φ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ Metric.closedBall 0 1) :
    oneCurrentBoundary (measureOneCurrent (localizedDilation M x₀ r hr c)) φ =
      -(c * r) * signedTestCurrent D (dilationTest x₀ r hr φ) := by
  have hd : tsupport (currentTestDerivative φ : EuclideanSpace ℝ (Fin d) → _) ⊆
      Metric.closedBall 0 1 := (tsupport_fderiv_subset ℝ).trans hφ
  rw [oneCurrentBoundary_apply, localizedDilation, measureOneCurrent_smul_map_dilation,
    measureOneCurrent_restrict_of_tsupport_subset _ measurableSet_closedBall _
      (tsupport_dilationTest_subset_closedBall x₀ r hr _ hd)]
  have h := hdiv (dilationTest x₀ r hr φ)
  rw [oneCurrentBoundary_apply, currentTestDerivative_dilationTest,
    measureOneCurrent_smul_test] at h
  rw [h]
  field_simp

theorem hasMeasureDivergenceOn_localizedDilation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (hdiv : HasMeasureDivergence M D)
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    HasMeasureDivergenceOn (localizedDilation M x₀ r hr c)
      ((c * r) • (D.restrict (Metric.closedBall x₀ |r|)).map (dilationEquiv x₀ r hr))
      (Metric.ball 0 1) := by
  intro φ hφ
  have hs := hφ.trans Metric.ball_subset_closedBall
  rw [signedTestCurrent_smul, smul_apply, smul_eq_mul,
    signedTestCurrent_map_dilation,
    signedTestCurrent_restrict_of_tsupport_subset _ measurableSet_closedBall _
      (tsupport_dilationTest_subset_closedBall x₀ r hr φ hs),
    boundary_localizedDilation_apply M D hdiv x₀ r hr c φ hs]
  ring

end GeometricMeasure
