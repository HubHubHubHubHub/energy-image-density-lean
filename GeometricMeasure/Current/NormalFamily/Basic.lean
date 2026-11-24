import GeometricMeasure.Analysis.SingularTransfer
import GeometricMeasure.Current.MatrixStructure

/-!
# Absolute continuity from spanning families of normal currents

This file contains the results of the development of `GeometricMeasure.Current.NormalFamily` that
the main statements of the library (the head theorems listed in the README of the repository) use.
`GeometricMeasure.Current.NormalFamily` imports it and continues the development.

## Main statements

* `absolutelyContinuous_volume_of_unit_density`: **Corollary 1.12 (DPR pp. 4–5), polar form**:
  finite masses mᵢ, directions τᵢ unit mᵢ-a.e.
-/
noncomputable section
open MeasureTheory Set

namespace GeometricMeasure
variable {d : ℕ}

/--
DPR arXiv p. 15 (Λ_𝒜 = {rank ≤ d − 1}). If the rows of a Frobenius matrix span ℝᵈ, its determinant
is nonzero.
-/
theorem det_matrixCoordinates_ne_zero_of_span_rows (P : MatrixSpace d)
    (h : Submodule.span ℝ (range fun i => rowCLM i P) = ⊤) :
    (matrixCoordinates P).det ≠ 0 := by
  intro hdet
  obtain ⟨ξ, hξ, hs⟩ := (mem_matrixDivergenceWaveCone_iff _).mpr hdet
  rw [matrixDivergenceSymbol_eq_zero_iff] at hs
  have hrow : ∀ i, inner ℝ (rowCLM i P) ξ = 0 := fun i => by
    rw [← matrixEuclideanCLM_matrixCoordinates, hs]
    rfl
  have hle : Submodule.span ℝ (range fun i => rowCLM i P) ≤
      LinearMap.ker (innerSL ℝ ξ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
      real_inner_comm]
    exact hrow i
  rw [h] at hle
  have hξξ : inner ℝ ξ ξ = (0 : ℝ) := by
    have hm := hle (Submodule.mem_top (x := ξ))
    rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] at hm
  exact hξ (inner_self_eq_zero.mp hξξ)

/--
DPR arXiv p. 15, (3.4): ν-almost everywhere, if the row directions span ℝᵈ, the rows of the matrix
polar also span it (each direction is a scalar multiple of the corresponding row,
`polarDensity_rowMeasure`).
-/
theorem ae_span_rows_matrixPolarDensity
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (hν : ∀ i, ν ≪ (rowMeasure N i).variation)
    (hspan : ∀ᵐ x ∂ν,
      Submodule.span ℝ (range fun i => polarDensity (rowMeasure N i) x) = ⊤) :
    ∀ᵐ x ∂ν, Submodule.span ℝ (range fun i => rowCLM i (matrixPolarDensity N x)) = ⊤ := by
  have hpol : ∀ᵐ x ∂ν, ∀ i, polarDensity (rowMeasure N i) x =
      ‖rowCLM i (matrixPolarDensity N x)‖⁻¹ • rowCLM i (matrixPolarDensity N x) :=
    ae_all_iff.mpr (fun i => (hν i).ae_le (polarDensity_rowMeasure N i))
  filter_upwards [hspan, hpol] with x hx hp
  rw [eq_top_iff, ← hx, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  change polarDensity (rowMeasure N i) x ∈ _
  rw [hp i]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/--
DPR arXiv p. 15, proof of Corollary 1.12: under (i) and (ii), the matrix polar of the stacked
measure has full rank ν-almost everywhere (nonzero determinant).
-/
theorem ae_det_matrixPolarDensity_ne_zero
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (hν : ∀ i, ν ≪ (rowMeasure N i).variation)
    (hspan : ∀ᵐ x ∂ν,
      Submodule.span ℝ (range fun i => polarDensity (rowMeasure N i) x) = ⊤) :
    ∀ᵐ x ∂ν, (matrixCoordinates (matrixPolarDensity N x)).det ≠ 0 := by
  filter_upwards [ae_span_rows_matrixPolarDensity N ν hν hspan] with x hx
  exact det_matrixCoordinates_ne_zero_of_span_rows _ hx

/--
DPR arXiv pp. 4–5, Corollary 1.12, local matrix form on an open set U: if the matrix measure N has
row-wise measure divergence on U, ν ≪ |row i| for every i, and the row directions span ℝᵈ
ν-a.e., then ν⌊U ≪ ℒᵈ.
-/
theorem restrict_absolutelyContinuous_volume_of_matrix_on
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hdiv : HasMatrixMeasureDivergenceOn N D U)
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (hν : ∀ i, ν ≪ (rowMeasure N i).variation)
    (hspan : ∀ᵐ x ∂ν,
      Submodule.span ℝ (range fun i => polarDensity (rowMeasure N i) x) = ⊤) :
    ν.restrict U ≪ volume := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact absolutelyContinuous_volume_of_dimension_zero _
  · have hres : ν.restrict U ≪ ν := Measure.absolutelyContinuous_of_le Measure.restrict_le_self
    have hνN : ν.restrict U ≪ N.variation :=
      hres.trans ((hν ⟨0, hd⟩).trans
        (Measure.absolutelyContinuous_of_le (variation_rowMeasure_le N ⟨0, hd⟩)))
    refine absolutelyContinuous_of_ae_singularPart (μ := N.variation)
      (p := fun x => x ∈ U → (matrixCoordinates (matrixPolarDensity N x)).det = 0)
      hνN (ae_det_matrixPolar_eq_zero_of_on N D hU hdiv) ?_
    filter_upwards [ae_restrict_mem hU.measurableSet,
      hres.ae_le (ae_det_matrixPolarDensity_ne_zero N ν hν hspan)] with x hxU hx h
    exact hx (h hxU)

/--
DPR arXiv pp. 4–5, **Corollary 1.12**, local form on an open set U (DPR p. 4, Theorem 1.10: open Ω):
d finite vector measures Rᵢ on ℝᵈ (normal one-dimensional currents) with measure divergence Dᵢ on U;
arbitrary positive measure ν with ν ≪ |Rᵢ| for every i and span{T⃗ᵢ(x)} = ℝᵈ ν-a.e. (T⃗ᵢ =
`polarDensity (R i)`); then ν⌊U ≪ ℒᵈ.
-/
theorem restrict_absolutelyContinuous_volume_of_span_polar_on
    (R : Fin d → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hdiv : ∀ i, HasMeasureDivergenceOn (R i) (D i) U)
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (hν : ∀ i, ν ≪ (R i).variation)
    (hspan : ∀ᵐ x ∂ν, Submodule.span ℝ (range fun i => polarDensity (R i) x) = ⊤) :
    ν.restrict U ≪ volume := by
  have hrow : ∀ i, rowMeasure (stackRows R) i = R i := rowMeasure_stackRows R
  refine restrict_absolutelyContinuous_volume_of_matrix_on (stackRows R) D hU ?_ ν ?_ ?_
  · intro i
    rw [hrow i]
    exact hdiv i
  · intro i
    rw [hrow i]
    exact hν i
  · simpa only [hrow] using hspan

/--
DPR arXiv pp. 4–5, Corollary 1.12 (printed form, all of ℝᵈ); p. 15, proofs of Theorem 1.10 and
Corollary 1.12; normal currents = finite vector measures with measure divergence. **Head of
Corollary 1.12** (without an alias): for d finite vector measures Rᵢ on ℝᵈ with measure divergence
Dᵢ (normal currents T₁, …, T_d ∈ 𝐍₁(ℝᵈ)) and every positive measure ν with (i) ν ≪ |Rᵢ| for every i
and (ii) span{T⃗₁(x), …, T⃗_d(x)} = ℝᵈ for ν-almost every x, we have ν ≪ ℒᵈ. Every dimension, no
finiteness assumption on ν.
-/
theorem absolutelyContinuous_volume_of_span_polar
    (R : Fin d → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hdiv : ∀ i, HasMeasureDivergence (R i) (D i))
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (hν : ∀ i, ν ≪ (R i).variation)
    (hspan : ∀ᵐ x ∂ν, Submodule.span ℝ (range fun i => polarDensity (R i) x) = ⊤) :
    ν ≪ volume := by
  have h := restrict_absolutelyContinuous_volume_of_span_polar_on R D isOpen_univ
    (fun i φ _ => hdiv i φ) ν hν hspan
  rwa [Measure.restrict_univ] at h

/--
DPR arXiv p. 4 (T = T⃗‖T‖): for an a.e. strongly measurable unit density τ of a finite measure m,
the chosen polar of m.withDensityᵥ τ agrees with τ m-almost everywhere, and the variation is m.
-/
theorem variation_and_polar_of_unit_density
    (m : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure m]
    {τ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hτm : AEStronglyMeasurable τ m) (hτ : ∀ᵐ x ∂m, ‖τ x‖ = 1) :
    (m.withDensityᵥ τ).variation = m ∧ polarDensity (m.withDensityᵥ τ) =ᵐ[m] τ := by
  have hv := variation_withDensityᵥ_eq_of_norm_one m hτm hτ
  refine ⟨hv, ?_⟩
  have h := polarDensity_ae_eq (m.withDensityᵥ τ) (q := τ)
    (by rw [hv]; exact integrable_of_norm_one m hτm hτ) (by rw [hv])
  rwa [hv] at h

/--
DPR arXiv p. 4, T = T⃗‖T‖; the coordinate form is EBM Theorem 1.8.
**Corollary 1.12 (DPR pp. 4–5), polar form**: finite masses mᵢ, directions τᵢ unit mᵢ-a.e. (a.e.
strongly measurable representatives), measure divergence of mᵢ.withDensityᵥ τᵢ, ν ≪ mᵢ, span{τᵢ(x)}
= ℝᵈ ν-a.e. imply ν ≪ ℒᵈ.
-/
theorem absolutelyContinuous_volume_of_unit_density
    (m : Fin d → Measure (EuclideanSpace ℝ (Fin d))) [hm : ∀ i, IsFiniteMeasure (m i)]
    (τ : Fin d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hτm : ∀ i, AEStronglyMeasurable (τ i) (m i)) (hτ : ∀ i, ∀ᵐ x ∂(m i), ‖τ i x‖ = 1)
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hdiv : ∀ i, HasMeasureDivergence ((m i).withDensityᵥ (τ i)) (D i))
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (hν : ∀ i, ν ≪ m i)
    (hspan : ∀ᵐ x ∂ν, Submodule.span ℝ (range fun i => τ i x) = ⊤) :
    ν ≪ volume := by
  have hvp := fun i => variation_and_polar_of_unit_density (m i) (hτm i) (hτ i)
  refine absolutelyContinuous_volume_of_span_polar (fun i => (m i).withDensityᵥ (τ i)) D hdiv ν
    (fun i => by rw [(hvp i).1]; exact hν i) ?_
  have hpol : ∀ᵐ x ∂ν, ∀ i, polarDensity ((m i).withDensityᵥ (τ i)) x = τ i x :=
    ae_all_iff.mpr (fun i => (hν i).ae_le (hvp i).2)
  filter_upwards [hspan, hpol] with x hx hp
  simpa only [hp] using hx

end GeometricMeasure
