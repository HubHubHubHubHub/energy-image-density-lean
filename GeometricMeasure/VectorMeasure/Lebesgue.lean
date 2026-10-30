import GeometricMeasure.VectorMeasure.Operations

/-! Lebesgue decomposition obtained from the positive variation and the fixed polar.
The definitions and density estimates are total in the reference measure.
Only recomposition needs `HaveLebesgueDecomposition`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GeometricMeasure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {m : ℕ}

def lebesgueACPart (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    VectorMeasure X (EuclideanSpace ℝ (Fin m)) :=
  (ν.withDensity (M.variation.rnDeriv ν)).withDensityᵥ (polarDensity M)

def lebesgueSingularPart (M : VectorMeasure X (EuclideanSpace ℝ (Fin m)))
    (ν : Measure X) : VectorMeasure X (EuclideanSpace ℝ (Fin m)) :=
  (M.variation.singularPart ν).withDensityᵥ (polarDensity M)

def lebesgueACDensity (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    X → EuclideanSpace ℝ (Fin m) :=
  fun x => (M.variation.rnDeriv ν x).toReal • polarDensity M x

theorem integrable_polarDensity_lebesgueACMeasure
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    Integrable (polarDensity M) (ν.withDensity (M.variation.rnDeriv ν)) :=
  (integrable_polarDensity M).mono_measure (M.variation.withDensity_rnDeriv_le ν)

theorem integrable_polarDensity_lebesgueSingularMeasure
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    Integrable (polarDensity M) (M.variation.singularPart ν) :=
  (integrable_polarDensity M).mono_measure (M.variation.singularPart_le ν)

theorem lebesgueACPart_add_lebesgueSingularPart
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X)
    [M.variation.HaveLebesgueDecomposition ν] :
    lebesgueACPart M ν + lebesgueSingularPart M ν = M := by
  rw [lebesgueACPart, lebesgueSingularPart,
    ← withDensityᵥ_add_measure _ _ (integrable_polarDensity_lebesgueACMeasure M ν)
      (integrable_polarDensity_lebesgueSingularMeasure M ν),
    Measure.rnDeriv_add_singularPart, withDensityᵥ_polarDensity]

theorem measurable_lebesgueACDensity
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    Measurable (lebesgueACDensity M ν) :=
  (M.variation.measurable_rnDeriv ν).ennreal_toReal.smul (measurable_polarDensity M)

theorem integrable_lebesgueACDensity
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    Integrable (lebesgueACDensity M ν) ν :=
  (integrable_withDensity_iff_integrable_smul' (M.variation.measurable_rnDeriv ν)
    (M.variation.rnDeriv_lt_top ν)).mp (integrable_polarDensity_lebesgueACMeasure M ν)

theorem withDensityᵥ_lebesgueACDensity
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    ν.withDensityᵥ (lebesgueACDensity M ν) = lebesgueACPart M ν :=
  withDensityᵥ_smul_eq_withDensityᵥ_withDensity'
    (M.variation.measurable_rnDeriv ν).aemeasurable (M.variation.rnDeriv_lt_top ν)
    (integrable_lebesgueACDensity M ν)

theorem lebesgueACPart_absolutelyContinuous
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    lebesgueACPart M ν ≪ᵥ ν.toENNRealVectorMeasure := by
  rw [← withDensityᵥ_lebesgueACDensity]
  exact withDensityᵥ_absolutelyContinuous_euclidean ν (integrable_lebesgueACDensity M ν)

theorem variation_lebesgueACPart
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    (lebesgueACPart M ν).variation = ν.withDensity (M.variation.rnDeriv ν) := by
  letI := isFiniteMeasure_of_le M.variation (M.variation.withDensity_rnDeriv_le ν)
  exact variation_withDensityᵥ_eq_of_norm_one _
    (measurable_polarDensity M).aestronglyMeasurable
    ((Measure.absolutelyContinuous_of_le (M.variation.withDensity_rnDeriv_le ν)).ae_le
      (norm_polarDensity_ae M))

theorem variation_lebesgueSingularPart
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    (lebesgueSingularPart M ν).variation = M.variation.singularPart ν := by
  letI := isFiniteMeasure_of_le M.variation (M.variation.singularPart_le ν)
  exact variation_withDensityᵥ_eq_of_norm_one _
    (measurable_polarDensity M).aestronglyMeasurable
    ((Measure.absolutelyContinuous_of_le (M.variation.singularPart_le ν)).ae_le
      (norm_polarDensity_ae M))

theorem lebesgueSingularPart_mutuallySingular
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    lebesgueSingularPart M ν ⟂ᵥ ν.toENNRealVectorMeasure := by
  rw [mutuallySingular_iff_variation, variation_lebesgueSingularPart]
  exact M.variation.mutuallySingular_singularPart ν

theorem exists_lebesgueDecomposition
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) [SigmaFinite ν] :
    ∃ g : X → EuclideanSpace ℝ (Fin m), Measurable g ∧ Integrable g ν ∧
      M = ν.withDensityᵥ g + lebesgueSingularPart M ν ∧
      lebesgueSingularPart M ν ⟂ᵥ ν.toENNRealVectorMeasure := by
  refine ⟨lebesgueACDensity M ν, measurable_lebesgueACDensity M ν,
    integrable_lebesgueACDensity M ν, ?_, lebesgueSingularPart_mutuallySingular M ν⟩
  rw [withDensityᵥ_lebesgueACDensity, lebesgueACPart_add_lebesgueSingularPart]

theorem polarDensity_lebesgueACPart
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    polarDensity (lebesgueACPart M ν) =ᵐ[ν.withDensity (M.variation.rnDeriv ν)]
      polarDensity M := by
  have hi : Integrable (polarDensity M) (lebesgueACPart M ν).variation := by
    rw [variation_lebesgueACPart]
    exact integrable_polarDensity_lebesgueACMeasure M ν
  have hr : (lebesgueACPart M ν).variation.withDensityᵥ (polarDensity M) =
      lebesgueACPart M ν := by rw [variation_lebesgueACPart]; rfl
  simpa only [variation_lebesgueACPart] using polarDensity_ae_eq _ hi hr

theorem polarDensity_lebesgueSingularPart
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    polarDensity (lebesgueSingularPart M ν) =ᵐ[M.variation.singularPart ν] polarDensity M := by
  have hi : Integrable (polarDensity M) (lebesgueSingularPart M ν).variation := by
    rw [variation_lebesgueSingularPart]
    exact integrable_polarDensity_lebesgueSingularMeasure M ν
  have hr : (lebesgueSingularPart M ν).variation.withDensityᵥ (polarDensity M) =
      lebesgueSingularPart M ν := by rw [variation_lebesgueSingularPart]; rfl
  simpa only [variation_lebesgueSingularPart] using polarDensity_ae_eq _ hi hr

/-- Abstract uniqueness does not require sigma-finiteness of the reference. -/
theorem lebesgueDecomposition_unique
    {A S A' S' : VectorMeasure X (EuclideanSpace ℝ (Fin m))} {ν : Measure X}
    (h : A + S = A' + S')
    (ha : A ≪ᵥ ν.toENNRealVectorMeasure) (hs : S ⟂ᵥ ν.toENNRealVectorMeasure)
    (ha' : A' ≪ᵥ ν.toENNRealVectorMeasure) (hs' : S' ⟂ᵥ ν.toENNRealVectorMeasure) :
    A = A' ∧ S = S' := by
  have hd : A - A' = S' - S := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using h
  have hz : A - A' = 0 := eq_zero_of_absolutelyContinuous_of_mutuallySingular
    (ha.sub ha') (by rw [hd, sub_eq_add_neg]; exact hs'.add_left hs.neg_left)
  have hA := sub_eq_zero.mp hz
  exact ⟨hA, add_left_cancel (hA ▸ h)⟩

theorem lebesgueACPart_map_equiv
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) [SigmaFinite ν]
    (e : X ≃ᵐ Y) : lebesgueACPart (M.map e) (ν.map e) = (lebesgueACPart M ν).map e := by
  letI := e.sigmaFinite_map (μ := ν)
  apply (lebesgueDecomposition_unique (ν := ν.map e) (S := lebesgueSingularPart (M.map e)
    (ν.map e)) (S' := (lebesgueSingularPart M ν).map e) ?_
    (lebesgueACPart_absolutelyContinuous _ _) (lebesgueSingularPart_mutuallySingular _ _)
    ((absolutelyContinuous_map_equiv_iff _ _ e).mpr (lebesgueACPart_absolutelyContinuous M ν))
    ((mutuallySingular_map_equiv_iff _ _ e).mpr (lebesgueSingularPart_mutuallySingular M ν))).1
  rw [lebesgueACPart_add_lebesgueSingularPart, ← VectorMeasure.map_add,
    lebesgueACPart_add_lebesgueSingularPart]

theorem lebesgueSingularPart_map_equiv
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) [SigmaFinite ν]
    (e : X ≃ᵐ Y) :
    lebesgueSingularPart (M.map e) (ν.map e) = (lebesgueSingularPart M ν).map e := by
  letI := e.sigmaFinite_map (μ := ν)
  apply add_left_cancel (a := lebesgueACPart (M.map e) (ν.map e))
  rw [lebesgueACPart_add_lebesgueSingularPart, lebesgueACPart_map_equiv,
    ← VectorMeasure.map_add, lebesgueACPart_add_lebesgueSingularPart]

@[simp] theorem lebesgueACPart_zero (ν : Measure X) :
    lebesgueACPart (0 : VectorMeasure X (EuclideanSpace ℝ (Fin m))) ν = 0 := by
  apply VectorMeasure.variation_eq_zero.mp
  simp [variation_lebesgueACPart]

@[simp] theorem lebesgueSingularPart_zero (ν : Measure X) :
    lebesgueSingularPart (0 : VectorMeasure X (EuclideanSpace ℝ (Fin m))) ν = 0 := by
  apply VectorMeasure.variation_eq_zero.mp
  simp [variation_lebesgueSingularPart]

@[simp] theorem lebesgueACPart_zero_right
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) : lebesgueACPart M 0 = 0 := by
  apply VectorMeasure.variation_eq_zero.mp
  simp [variation_lebesgueACPart]

@[simp] theorem lebesgueSingularPart_zero_right
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) : lebesgueSingularPart M 0 = M := by
  simp [lebesgueSingularPart, withDensityᵥ_polarDensity]

theorem lebesgueSingularPart_eq_zero_of_absolutelyContinuous
    {M : VectorMeasure X (EuclideanSpace ℝ (Fin m))} {ν : Measure X}
    (h : M ≪ᵥ ν.toENNRealVectorMeasure) : lebesgueSingularPart M ν = 0 := by
  apply VectorMeasure.variation_eq_zero.mp
  rw [variation_lebesgueSingularPart]
  exact Measure.singularPart_eq_zero_of_ac ((absolutelyContinuous_iff_variation M ν).mp h)

theorem lebesgueACPart_eq_self_of_absolutelyContinuous
    {M : VectorMeasure X (EuclideanSpace ℝ (Fin m))} {ν : Measure X}
    [M.variation.HaveLebesgueDecomposition ν]
    (h : M ≪ᵥ ν.toENNRealVectorMeasure) : lebesgueACPart M ν = M := by
  simpa only [lebesgueSingularPart_eq_zero_of_absolutelyContinuous h, add_zero] using
    lebesgueACPart_add_lebesgueSingularPart M ν

theorem lebesgueSingularPart_eq_self_of_mutuallySingular
    {M : VectorMeasure X (EuclideanSpace ℝ (Fin m))} {ν : Measure X}
    (h : M ⟂ᵥ ν.toENNRealVectorMeasure) : lebesgueSingularPart M ν = M := by
  rw [lebesgueSingularPart,
    Measure.singularPart_eq_self.mpr ((mutuallySingular_iff_variation M ν).mp h),
    withDensityᵥ_polarDensity]

theorem lebesgueACPart_eq_zero_of_mutuallySingular
    {M : VectorMeasure X (EuclideanSpace ℝ (Fin m))} {ν : Measure X}
    (h : M ⟂ᵥ ν.toENNRealVectorMeasure) : lebesgueACPart M ν = 0 := by
  apply VectorMeasure.variation_eq_zero.mp
  rw [variation_lebesgueACPart]
  have hz := ((mutuallySingular_iff_variation M ν).mp h).rnDeriv_ae_eq_zero
  simpa using withDensity_congr_ae hz

end GeometricMeasure
