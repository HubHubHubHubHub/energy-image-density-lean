import GeometricMeasure.VectorMeasure.Polar

/-! Absolute continuity and singularity detected by Euclidean variation. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GeometricMeasure

variable {X : Type*} [MeasurableSpace X] {m : ℕ}

theorem absolutelyContinuous_iff_variation
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    M ≪ᵥ ν.toENNRealVectorMeasure ↔ M.variation ≪ ν := by
  constructor
  · intro h
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hν
    apply (VectorMeasure.variation_apply_eq_zero hs).mpr
    intro t hts ht
    apply h
    rw [Measure.toENNRealVectorMeasure_apply_measurable ht]
    exact measure_mono_null hts hν
  · intro h
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro s hs hν
    rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hν
    apply enorm_eq_zero.mp
    exact le_antisymm ((VectorMeasure.enorm_measure_le_variation M s).trans_eq (h hν))
      zero_le

theorem withDensityᵥ_absolutelyContinuous_euclidean
    (ν : Measure X) {f : X → EuclideanSpace ℝ (Fin m)} (hf : Integrable f ν) :
    ν.withDensityᵥ f ≪ᵥ ν.toENNRealVectorMeasure := by
  rw [absolutelyContinuous_iff_variation, Measure.variation_withDensityᵥ hf]
  exact withDensity_absolutelyContinuous _ _

theorem absolutelyContinuous_iff_exists_density
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) [SigmaFinite ν] :
    M ≪ᵥ ν.toENNRealVectorMeasure ↔
      ∃ f : X → EuclideanSpace ℝ (Fin m),
        Measurable f ∧ Integrable f ν ∧ ν.withDensityᵥ f = M := by
  constructor
  · intro h
    exact exists_density_of_coord_absolutelyContinuous M ν (coord_absolutelyContinuous h)
  · rintro ⟨f, _, hf, rfl⟩
    exact withDensityᵥ_absolutelyContinuous_euclidean ν hf

theorem mutuallySingular_iff_variation
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) (ν : Measure X) :
    M ⟂ᵥ ν.toENNRealVectorMeasure ↔ M.variation ⟂ₘ ν := by
  constructor
  · rintro ⟨s, hs, hM, hν⟩
    refine ⟨s, hs, (VectorMeasure.variation_apply_eq_zero hs).mpr ?_, ?_⟩
    · intro t hts _
      exact hM t hts
    · simpa only [Measure.toENNRealVectorMeasure_apply_measurable hs.compl] using
        hν sᶜ Set.Subset.rfl
  · rintro ⟨s, hs, hM, hν⟩
    apply VectorMeasure.MutuallySingular.mk s hs
    · intro t hts ht
      exact (VectorMeasure.variation_apply_eq_zero hs).mp hM t hts ht
    · intro t hts ht
      rw [Measure.toENNRealVectorMeasure_apply_measurable ht]
      exact measure_mono_null hts hν

theorem eq_zero_of_absolutelyContinuous_of_mutuallySingular
    {M : VectorMeasure X (EuclideanSpace ℝ (Fin m))} {ν : Measure X}
    (ha : M ≪ᵥ ν.toENNRealVectorMeasure) (hs : M ⟂ᵥ ν.toENNRealVectorMeasure) :
    M = 0 := by
  apply VectorMeasure.variation_eq_zero.mp
  exact Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular
    ((absolutelyContinuous_iff_variation M ν).mp ha)
    ((mutuallySingular_iff_variation M ν).mp hs)

end GeometricMeasure
