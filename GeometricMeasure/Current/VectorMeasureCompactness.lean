import GeometricMeasure.VectorMeasure.Compactness
import GeometricMeasure.Current.CovectorMass

/-! Simultaneous extraction of finite positive measures and Euclidean RN assembly. -/
noncomputable section
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ} {m : ℕ}

theorem exists_vectorMeasure_weak_subseq_of_codomain
    (Ms : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (C : ℝ≥0)
    (hsupport : ∀ n, (Ms n).variation Kᶜ = 0)
    (hmass : ∀ n, (Ms n).variation univ ≤ (C : ℝ≥0∞)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)),
        M.variation Kᶜ = 0 ∧ M.variation univ ≤ (C : ℝ≥0∞) ∧
        VectorMeasureWeaklyTendsto (Ms ∘ φ) M := by
  obtain ⟨φ, hφ, α, hαmass, hαsupp, hα⟩ := exists_finiteMeasure_family_subseq
    (fun n => coordinateFiniteFamily (Ms n)) hK C
    (fun n i => finiteMeasure_mass_le_of_le _ _ (coordinateFiniteFamily_le_variation _ _) C (hmass n))
    (fun n i => finiteMeasure_compl_eq_zero_of_le _ _ (coordinateFiniteFamily_le_variation _ _)
      (hsupport n))
  let αpos := fun i => α (i, false)
  let αneg := fun i => α (i, true)
  let M := assemblePositiveFamily αpos αneg
  have hconv : VectorMeasureWeaklyTendsto (Ms ∘ φ) M :=
    weaklyTendsto_assemble_of_coordinateParts_tendsto _ αpos αneg
      (fun i => hα (i, false)) (fun i => hα (i, true))
  refine ⟨φ, hφ, M, variation_assemblePositiveFamily_compl αpos αneg
    (fun i => hαsupp (i, false)) (fun i => hαsupp (i, true)), ?_, hconv⟩
  apply (variation_le_liminf_of_weaklyTendsto _ M hconv isOpen_univ).trans
  exact Filter.liminf_le_of_le (by isBoundedDefault) (fun b hb =>
    let ⟨n, hn⟩ := hb.exists
    hn.trans (hmass (φ n)))

theorem exists_vectorMeasure_weak_subseq
    (Ms : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (C : ℝ≥0)
    (hsupport : ∀ n, (Ms n).variation Kᶜ = 0)
    (hmass : ∀ n, (Ms n).variation univ ≤ (C : ℝ≥0∞)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)),
        M.variation Kᶜ = 0 ∧ M.variation univ ≤ (C : ℝ≥0∞) ∧
        VectorMeasureWeaklyTendsto (Ms ∘ φ) M :=
  exists_vectorMeasure_weak_subseq_of_codomain Ms hK C hsupport hmass


end GeometricMeasure
