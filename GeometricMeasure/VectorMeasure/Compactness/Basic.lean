import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import GeometricMeasure.VectorMeasure.WeakConvergence.Basic

/-!
# Simultaneous extraction of finite positive measures

This file contains the definitions and results of the development of
`GeometricMeasure.VectorMeasure.Compactness` that the main statements of the library (the head
theorems listed in the README of the repository) use. `GeometricMeasure.VectorMeasure.Compactness`
imports it and continues the development.

## Main definitions

* `boundedCovectorCoefficient`: The `i`-th coefficient `x ↦ ω x (EuclideanSpace.single i 1)` of a
  bounded covector field.

## Main statements

* `exists_finiteMeasure_family_subseq`: A sequence of finite families of finite measures with mass
  at most `C` and vanishing outside a compact `K` has a subsequence converging to a family with the
  same bound and support.
-/
noncomputable section
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ} {m : ℕ}

/-- The map/comap identity used in Prokhorov, with the support hypothesis explicit. -/
theorem finiteMeasure_map_comap_subtype
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d))) (hμ : μ Kᶜ = 0) :
    (FiniteMeasure.comap (Subtype.val : K → EuclideanSpace ℝ (Fin d)) μ).map
      Subtype.val = μ := by
  let f : K → EuclideanSpace ℝ (Fin d) := Subtype.val
  have hf : Topology.IsClosedEmbedding f := Topology.IsClosedEmbedding.subtypeVal hK.isClosed
  have rf : range f = K := Subtype.range_val
  apply FiniteMeasure.eq_of_forall_toMeasure_apply_eq
  intro s hs
  simp only [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_comap]
  rw [Measure.map_apply measurable_subtype_coe hs,
    Measure.comap_apply _ Subtype.val_injective, image_preimage_eq_inter_range]
  · rw [← Measure.restrict_apply hs, Measure.restrict_eq_self_of_ae_mem]
    apply (FiniteMeasure.null_iff_toMeasure_null μ (range f)ᶜ).mp
    rw [rf]
    exact hμ
  · exact fun t ht => hf.measurableEmbedding.measurableSet_image' ht
  · exact hf.continuous.measurable hs

theorem exists_finiteMeasure_family_subseq
    {ι : Type*} [Fintype ι]
    (μs : ℕ → ι → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (C : ℝ≥0)
    (hmass : ∀ n, ∀ i, (μs n i).mass ≤ C)
    (hsupport : ∀ n, ∀ i, μs n i Kᶜ = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ α : ι → FiniteMeasure (EuclideanSpace ℝ (Fin d)),
        (∀ i, (α i).mass ≤ C) ∧ (∀ i, α i Kᶜ = 0) ∧
        (∀ i, Tendsto (fun j => μs (φ j) i) atTop (𝓝 (α i))) := by
  classical
  by_cases hKe : K = ∅
  · have hz (n : ℕ) (i : ι) : μs n i = 0 := by
      apply (FiniteMeasure.mass_zero_iff _).mp
      have h := hsupport n i
      rw [hKe, compl_empty] at h
      exact h
    refine ⟨id, strictMono_id, fun _ => 0, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro i
      simp only [hz]
      exact tendsto_const_nhds
  haveI : Nonempty K := Set.nonempty_iff_ne_empty.mpr hKe |>.to_subtype
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : (Icc (0 : ℝ≥0) C × ProbabilityMeasure K) →
      FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
    fun z => (z.1.val • z.2.toFiniteMeasure).map Subtype.val
  have hF : Continuous F := by
    apply (FiniteMeasure.continuous_map continuous_subtype_val).comp
    exact (continuous_subtype_val.comp continuous_fst).smul
      ((ProbabilityMeasure.toFiniteMeasure_isEmbedding K).continuous.comp continuous_snd)
  let μK (n : ℕ) (i : ι) := FiniteMeasure.comap
    (Subtype.val : K → EuclideanSpace ℝ (Fin d)) (μs n i)
  let z (n : ℕ) (i : ι) : Icc (0 : ℝ≥0) C × ProbabilityMeasure K :=
    (⟨(μK n i).mass, zero_le, (FiniteMeasure.mass_comap_le _ _).trans (hmass n i)⟩,
      (μK n i).normalize)
  have hz (n : ℕ) (i : ι) : F (z n i) = μs n i := by
    change ((μK n i).mass • (μK n i).normalize.toFiniteMeasure).map _ = _
    rw [← FiniteMeasure.self_eq_mass_smul_normalize]
    exact finiteMeasure_map_comap_subtype hK _ (hsupport n i)
  obtain ⟨a, φ, hφ, ha⟩ := CompactSpace.tendsto_subseq z
  refine ⟨φ, hφ, fun i => F (a i), ?_, ?_, ?_⟩
  · intro i
    apply (FiniteMeasure.mass_map_le _ _).trans
    calc
      _ = (a i).1.val := by
        change ((a i).1.val • (a i).2.toFiniteMeasure) univ = _
        rw [FiniteMeasure.smul_apply]
        change (a i).1.val * (a i).2.toFiniteMeasure.mass = _
        rw [ProbabilityMeasure.mass_toFiniteMeasure, mul_one]
      _ ≤ C := (a i).1.property.2
  · intro i
    apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
    rw [FiniteMeasure.toMeasure_map, Measure.map_apply measurable_subtype_coe hK.measurableSet.compl]
    simp
  · intro i
    have hi := hF.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp ha) i)
    simpa only [Function.comp_def, hz] using hi


/-- The `i`-th coefficient `x ↦ ω x (EuclideanSpace.single i 1)` of a bounded covector field. -/
def boundedCovectorCoefficient (ω : BoundedCovectorField d m) (i : Fin m) :
    BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).compLeftContinuousBounded _ ω

@[simp] theorem boundedCovectorCoefficient_apply
    (ω : BoundedCovectorField d m) (i : Fin m) (x : EuclideanSpace ℝ (Fin d)) :
    boundedCovectorCoefficient ω i x = ω x (EuclideanSpace.single i 1) := rfl

end GeometricMeasure

