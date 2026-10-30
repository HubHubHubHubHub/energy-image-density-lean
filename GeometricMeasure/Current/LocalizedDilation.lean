import GeometricMeasure.Current.Dilation

/-! Compactly supported dilations and divergence on the open unit ball. -/
noncomputable section
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d m : ℕ}

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

theorem hasMeasureDivergenceOn_of_weaklyTendsto
    (Ms : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (Ds : ℕ → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (hM : VectorMeasureWeaklyTendsto Ms M) (hD : SignedMeasureWeaklyTendsto Ds D)
    (hdiv : ∀ n, HasMeasureDivergenceOn (Ms n) (Ds n) U) : HasMeasureDivergenceOn M D U := by
  intro φ hφ
  have hleft := hD (φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
  simp only [signedMeasurePairing_currentTest] at hleft
  apply tendsto_nhds_unique hleft
  exact ((boundary_tendsto_of_weaklyTendsto Ms M hM φ).neg).congr'
    (Eventually.of_forall (fun n => (hdiv n φ hφ).symm))

theorem exists_localizedDilation_weak_subseq
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (x₀ : EuclideanSpace ℝ (Fin d)) (rs cs : ℕ → ℝ) (hrs : ∀ n, rs n ≠ 0) (C : ℝ≥0)
    (hmass : ∀ n, ENNReal.ofReal |cs n| * M.variation (Metric.closedBall x₀ |rs n|) ≤
      (C : ℝ≥0∞)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ N : VectorMeasure
      (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)),
      N.variation (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 ∧
      N.variation univ ≤ (C : ℝ≥0∞) ∧
      VectorMeasureWeaklyTendsto
        (fun n => localizedDilation M x₀ (rs (φ n)) (hrs (φ n)) (cs (φ n))) N := by
  apply exists_vectorMeasure_weak_subseq_of_codomain
    (fun n => localizedDilation M x₀ (rs n) (hrs n) (cs n)) (isCompact_closedBall 0 1) C
  · exact fun n => variation_localizedDilation_compl M x₀ (rs n) (hrs n) (cs n)
  · intro n
    rw [variation_localizedDilation_univ]
    exact hmass n

theorem signedTestCurrent_dilation_abs_le
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (φ : ScalarCurrentTest d)
    (hφ : tsupport (φ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ Metric.closedBall 0 1) :
    |signedTestCurrent D (dilationTest x₀ r hr φ)| ≤
      ‖(φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ *
        D.totalVariation.real (Metric.closedBall x₀ |r|) := by
  haveI : IsFiniteMeasure D.totalVariation := by
    unfold SignedMeasure.totalVariation
    infer_instance
  have hs := tsupport_dilationTest_subset_closedBall x₀ r hr φ hφ
  apply (signedTestCurrent_abs_le_integral_norm D _).trans
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.closedBall x₀ |r|)
    (f := fun x => ‖dilationTest x₀ r hr φ x‖) (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), norm_zero])]
  calc
    _ ≤ ∫ _ in Metric.closedBall x₀ |r|,
        ‖(φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ ∂D.totalVariation := by
      apply integral_mono ((dilationTest x₀ r hr φ).integrable
        (locallyIntegrableOn_const (1 : ℝ))).norm.restrict (integrable_const _)
      intro x
      exact (φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm _
    _ = _ := by simp [integral_const, mul_comm]

theorem boundary_localizedDilation_tendsto_zero
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (hdiv : HasMeasureDivergence M D)
    (x₀ : EuclideanSpace ℝ (Fin d)) (rs cs : ℕ → ℝ) (hrs : ∀ n, rs n ≠ 0)
    (hsmall : Tendsto (fun n => ENNReal.ofReal |cs n * rs n| *
      D.totalVariation (Metric.closedBall x₀ |rs n|)) atTop (𝓝 0))
    (φ : ScalarCurrentTest d)
    (hφ : tsupport (φ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ Metric.ball 0 1) :
    Tendsto (fun n => oneCurrentBoundary
      (measureOneCurrent (localizedDilation M x₀ (rs n) (hrs n) (cs n))) φ) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n => |cs n * rs n| *
      D.totalVariation.real (Metric.closedBall x₀ |rs n|)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hsmall
  have hb := hreal.const_mul ‖(φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖
  simp only [mul_zero] at hb
  apply squeeze_zero_norm _ hb
  intro n
  rw [boundary_localizedDilation_apply M D hdiv x₀ (rs n) (hrs n) (cs n) φ
    (hφ.trans Metric.ball_subset_closedBall), norm_mul, norm_neg, Real.norm_eq_abs,
    Real.norm_eq_abs]
  calc
    _ ≤ |cs n * rs n| *
        (‖(φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ *
          D.totalVariation.real (Metric.closedBall x₀ |rs n|)) :=
      mul_le_mul_of_nonneg_left (signedTestCurrent_dilation_abs_le D x₀ (rs n) (hrs n) φ
        (hφ.trans Metric.ball_subset_closedBall)) (abs_nonneg _)
    _ = _ := by ring

theorem exists_localizedDilation_weak_subseq_divergenceFreeOn
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (hdiv : HasMeasureDivergence M D)
    (x₀ : EuclideanSpace ℝ (Fin d)) (rs cs : ℕ → ℝ) (hrs : ∀ n, rs n ≠ 0) (C : ℝ≥0)
    (hmass : ∀ n, ENNReal.ofReal |cs n| * M.variation (Metric.closedBall x₀ |rs n|) ≤
      (C : ℝ≥0∞))
    (hsmall : Tendsto (fun n => ENNReal.ofReal |cs n * rs n| *
      D.totalVariation (Metric.closedBall x₀ |rs n|)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ N : VectorMeasure
      (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)),
      N.variation (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 ∧
      N.variation univ ≤ (C : ℝ≥0∞) ∧
      VectorMeasureWeaklyTendsto
        (fun n => localizedDilation M x₀ (rs (φ n)) (hrs (φ n)) (cs (φ n))) N ∧
      HasMeasureDivergenceOn N 0 (Metric.ball 0 1) := by
  obtain ⟨φ, hφ, N, hs, hm, hconv⟩ :=
    exists_localizedDilation_weak_subseq M x₀ rs cs hrs C hmass
  refine ⟨φ, hφ, N, hs, hm, hconv, ?_⟩
  intro ψ hψ
  have hzero := (boundary_localizedDilation_tendsto_zero M D hdiv x₀ rs cs hrs hsmall ψ hψ).comp
    hφ.tendsto_atTop
  have hlim := boundary_tendsto_of_weaklyTendsto _ N hconv ψ
  have heq := tendsto_nhds_unique hlim hzero
  simp [signedTestCurrent_zero, heq]

def massNormalizedDilation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (x₀ : EuclideanSpace ℝ (Fin d))
    (r : ℝ) (hr : r ≠ 0) :
    VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)) :=
  localizedDilation M x₀ r hr (ν.real (Metric.closedBall x₀ |r|))⁻¹

theorem variation_massNormalizedDilation_univ
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (x₀ : EuclideanSpace ℝ (Fin d))
    (r : ℝ) (hr : r ≠ 0) (hpos : 0 < ν (Metric.closedBall x₀ |r|)) :
    (massNormalizedDilation M ν x₀ r hr).variation univ =
      M.variation (Metric.closedBall x₀ |r|) / ν (Metric.closedBall x₀ |r|) := by
  rw [massNormalizedDilation, variation_localizedDilation_univ]
  by_cases htop : ν (Metric.closedBall x₀ |r|) = ⊤
  · simp [measureReal_def, htop]
  · have hp : 0 < ν.real (Metric.closedBall x₀ |r|) := ENNReal.toReal_pos hpos.ne' htop
    rw [abs_of_pos (inv_pos.mpr hp), ENNReal.ofReal_inv_of_pos hp,
      measureReal_def, ENNReal.ofReal_toReal htop, div_eq_mul_inv, mul_comm]

end GeometricMeasure
