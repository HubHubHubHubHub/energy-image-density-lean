import GeometricMeasure.Matrix.RankDeterminant
import GeometricMeasure.Current.RegularPartLimit

/-!
# The singular rank bound for matrix measures

## Main results
A finite square matrix-valued measure whose row-wise divergence is a finite signed measure on
an open set has singular polar rank at most d − 1 there. The determinant and rank statements include
dimension zero; the wave-cone forms assume positive dimension. The measure is unrestricted outside
the open set.

The proof combines the regular resolvent L¹ limit with the contradiction from singular
blow-ups, then converts zero determinant into the rank bound.

References: De Philippis–Rindler, arXiv:1601.06543v2, p. 5, Corollary 1.13; p. 6, §2.1, finite Radon
measures; p. 15, the row-wise divergence wave cone {rank ≤ d − 1}.
The normal-current formulation is De Philippis–Rindler, Corollary 1.12.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace GeometricMeasure
namespace MatrixPolarBlowupData
variable {d : ℕ} {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}

/--
The regular-part L¹ limit contradicts singularity and the positive mass of the blow-up limit, so no
matrix polar blow-up datum exists. Reference: De Philippis–Rindler, arXiv p. 8, after (2.3).
-/
theorem isEmpty_of_regularPart_l1 : IsEmpty (MatrixPolarBlowupData M D x) :=
  ⟨fun b => b.false_of_regularPartL1Limit b.regularPartL1Limit_holds⟩

end MatrixPolarBlowupData

variable {d : ℕ}

/--
DPR arXiv p. 5, Corollary 1.13, and p. 15 (wave cone Λ_𝒜); global form. For a matrix measure with
row-wise measure divergence on ℝᵈ, d ≥ 1, the Frobenius polar lies in the matrix-divergence wave
cone |M|ˢ-almost everywhere.
-/
theorem ae_matrixPolar_mem_waveCone [NeZero d]
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hdiv : HasMatrixMeasureDivergence M D) :
    ∀ᵐ x ∂M.variation.singularPart volume,
      matrixCoordinates (matrixPolarDensity M x) ∈ matrixDivergenceWaveCone d := by
  filter_upwards [ae_nonempty_matrixPolarBlowupData M D hdiv] with x hx
  by_contra hP
  obtain ⟨b⟩ := hx hP
  exact (MatrixPolarBlowupData.isEmpty_of_regularPart_l1 (M := M) (D := D) (x := x)).false b

/--
DPR arXiv p. 5, Corollary 1.13 (determinant form), global, every dimension (in dimension zero, |M|ˢ
= 0).
-/
theorem ae_det_matrixPolar_eq_zero
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hdiv : HasMatrixMeasureDivergence M D) :
    ∀ᵐ x ∂M.variation.singularPart volume,
      (matrixCoordinates (matrixPolarDensity M x)).det = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : M.variation.singularPart volume = 0 := by
      rw [eq_zero_of_matrix_dimension_zero M]
      simp
    rw [h0, ae_zero]
    exact Filter.eventually_bot
  · haveI : NeZero d := ⟨hd.ne'⟩
    filter_upwards [ae_matrixPolar_mem_waveCone M D hdiv] with x hx
    exact (mem_matrixDivergenceWaveCone_iff _).mp hx

/-- DPR arXiv p. 5, Corollary 1.13, printed form rank(dμ/d|μ|) ≤ d − 1, global, every dimension. -/
theorem ae_rank_matrixPolar_le
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hdiv : HasMatrixMeasureDivergence M D) :
    ∀ᵐ x ∂M.variation.singularPart volume,
      (matrixCoordinates (matrixPolarDensity M x)).rank ≤ d - 1 := by
  filter_upwards [ae_det_matrixPolar_eq_zero M D hdiv] with x hx
  have h := (matrix_rank_lt_iff_det_eq_zero _).mpr hx
  omega

end GeometricMeasure

namespace GeometricMeasure
variable {d : ℕ}

/--
DPR arXiv p. 5 (div μ ∈ 𝓜(Ω; ℝᵈ)) and p. 15 (row-wise divergence). Row-wise measure divergence
tested only on tests supported in U.
-/
def HasMatrixMeasureDivergenceOn
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (U : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ i, HasMeasureDivergenceOn (rowMeasure M i) (D i) U

/-- Global divergence yields divergence on every set. -/
theorem HasMatrixMeasureDivergence.hasMatrixMeasureDivergenceOn
    {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
    {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))}
    (hdiv : HasMatrixMeasureDivergence M D) (U : Set (EuclideanSpace ℝ (Fin d))) :
    HasMatrixMeasureDivergenceOn M D U :=
  fun i φ _ => hdiv i φ

/--
Local version of `hasMeasureDivergenceOn_localizedDilation` : the equation on a set U containing the
closed source ball B̄(x₀, |r|) suffices.
-/
theorem hasMeasureDivergenceOn_localizedDilation_of_on
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hdiv : HasMeasureDivergenceOn M D U)
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ)
    (hU : closedBall x₀ |r| ⊆ U) :
    HasMeasureDivergenceOn (localizedDilation M x₀ r hr c)
      ((c * r) • (D.restrict (closedBall x₀ |r|)).map (dilationEquiv x₀ r hr))
      (ball 0 1) := by
  intro φ hφ
  have hs := hφ.trans ball_subset_closedBall
  have hd : tsupport (currentTestDerivative φ : EuclideanSpace ℝ (Fin d) → _) ⊆
      closedBall 0 1 := (tsupport_fderiv_subset ℝ).trans hs
  have hb : oneCurrentBoundary (measureOneCurrent (localizedDilation M x₀ r hr c)) φ =
      -(c * r) * signedTestCurrent D (dilationTest x₀ r hr φ) := by
    rw [oneCurrentBoundary_apply, localizedDilation, measureOneCurrent_smul_map_dilation,
      measureOneCurrent_restrict_of_tsupport_subset _ measurableSet_closedBall _
        (tsupport_dilationTest_subset_closedBall x₀ r hr _ hd)]
    have h := hdiv (dilationTest x₀ r hr φ)
      ((tsupport_dilationTest_subset_closedBall x₀ r hr φ hs).trans hU)
    rw [oneCurrentBoundary_apply, currentTestDerivative_dilationTest,
      measureOneCurrent_smul_test] at h
    rw [h]
    field_simp
  rw [signedTestCurrent_smul, smul_apply, smul_eq_mul,
    signedTestCurrent_map_dilation,
    signedTestCurrent_restrict_of_tsupport_subset _ measurableSet_closedBall _
      (tsupport_dilationTest_subset_closedBall x₀ r hr φ hs), hb]
  ring

/--
Local version of `hasMatrixMeasureDivergenceOn_dilation` : row-wise dilated equation on the open
unit ball whenever B̄(x, |r|) ⊆ U.
-/
theorem hasMatrixMeasureDivergenceOn_dilation_of_on
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hdiv : HasMatrixMeasureDivergenceOn M D U)
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ)
    (hU : closedBall x |r| ⊆ U) (i : Fin d) :
    HasMeasureDivergenceOn (rowMeasure (matrixDilation M x r hr c) i)
      (divergenceDilation (D i) x r hr c) (ball 0 1) := by
  rw [rowMeasure_matrixDilation]
  exact hasMeasureDivergenceOn_localizedDilation_of_on _ _ (hdiv i) x r hr c hU

/--
`exists_positive_tangent_of_goodRadii` with all radii < δ: shifting the sequence of radii leaves the
tangent and its bounds unchanged.
-/
theorem exists_positive_tangent_of_goodRadii_lt
    (s : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure s]
    (x : EuclideanSpace ℝ (Fin d))
    (hgood : ∃ᶠ r in 𝓝[>] (0 : ℝ),
      s (closedBall x r) ≤ 2 ^ d * s (closedBall x (r / 2)))
    (hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < s (closedBall x r))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ rs : ℕ → ℝ, ∃ hrs : ∀ n, 0 < rs n,
      (∀ n, rs n < δ) ∧
      Tendsto rs atTop (𝓝[>] (0 : ℝ)) ∧
      (∀ n, 0 < s (closedBall x (rs n))) ∧
      ∃ ν : FiniteMeasure (EuclideanSpace ℝ (Fin d)),
        ν.mass ≤ 1 ∧ ν (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 ∧
        Tendsto (fun n => normalizedPositiveDilation s x (rs n) (hrs n).ne') atTop (𝓝 ν) ∧
        ((2 : ℝ) ^ d)⁻¹ ≤ ∫ y, tentCutoff y ∂(ν : Measure (EuclideanSpace ℝ (Fin d))) ∧
        0 < (ν : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 1) := by
  obtain ⟨rs, hrs, ht, hp, ν, hm, hs, hconv, hlow, hn⟩ :=
    exists_positive_tangent_of_goodRadii s x hgood hpos
  have hev : ∀ᶠ n in atTop, rs n < δ :=
    (tendsto_nhds_of_tendsto_nhdsWithin ht).eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨fun n => rs (n + N), fun n => hrs (n + N), fun n => hN _ (Nat.le_add_left N n),
    (tendsto_add_atTop_iff_nat N).mpr ht, fun n => hp _, ν, hm, hs, ?_, hlow, hn⟩
  exact (tendsto_add_atTop_iff_nat
    (f := fun n => normalizedPositiveDilation s x (rs n) (hrs n).ne') N).mpr hconv

/--
Local version of `ae_nonempty_matrixPolarBlowupData`; DPR arXiv pp. 7–9: at almost every singular
point of the open set U whose polar lies outside the wave cone, the full matrix polar blow-up
data exists (radii shifted into U).
-/
theorem ae_nonempty_matrixPolarBlowupData_of_on [NeZero d]
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hdiv : HasMatrixMeasureDivergenceOn M D U) :
    ∀ᵐ x ∂M.variation.singularPart volume, x ∈ U →
      matrixCoordinates (matrixPolarDensity M x) ∉ matrixDivergenceWaveCone d →
        Nonempty (MatrixPolarBlowupData M D x) := by
  haveI (i : Fin d) : IsFiniteMeasure (D i).totalVariation := by
    unfold SignedMeasure.totalVariation
    infer_instance
  have hpoints := ae_mem_singularBesicovitchPoints (matrixReindexed M) volume
    (fun i : Fin d => (D i).totalVariation)
  simp only [singularBesicovitchPoints, mem_setOf_eq, variation_matrixReindexed] at hpoints
  have hunit := (Measure.absolutelyContinuous_of_le (M.variation.singularPart_le volume)).ae_le
    (norm_matrixPolarDensity_ae M)
  filter_upwards [hpoints, hunit, ae_tendsto_matrixPolar_singular_error M,
    ae_frequently_closedBall_le_two_pow_mul_half (M.variation.singularPart volume)
      (M.variation.mutuallySingular_singularPart volume)] with x hx hnorm he hgood
  intro hxU hP
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  obtain ⟨-, hpos, ha, hratio, -, -, -, hβ⟩ := hx
  obtain ⟨rs, hrs, hlt, ht, hp, ν, hm, hs, hconv, hlow, hn⟩ :=
    exists_positive_tangent_of_goodRadii_lt (M.variation.singularPart volume) x hgood hpos hδ
  have hsub : ∀ n, closedBall x |rs n| ⊆ U := fun n =>
    (closedBall_subset_ball (by rw [abs_of_pos (hrs n)]; exact hlt n)).trans hball
  obtain ⟨hdet, hell, hbound, hsymbol⟩ :=
    matrixDivergence_ellipticity_of_not_mem (matrixCoordinates (matrixPolarDensity M x)) hP
  refine ⟨{
    radii := rs, radii_pos := hrs, radii_tendsto := ht, mass_pos := hp
    tangent := ν, tangent_mass_le := hm, tangent_support := hs, positive_convergence := hconv
    cutoff_lower_bound := hlow, tangent_nonzero := hn, polar_unit := hnorm
    det_ne_zero := hdet, ellipticity_pos := hell, elliptic_bound := hbound, symbol_bound := hsymbol
    frozen_error := frozenMatrixDefect_tendsto M x rs hrs ht hp he ha
    matrix_mass := matrixDilation_mass_tendsto_one M _ x rs hrs ht hp hratio
    rhs_error := ?_
    equation := fun n i => hasMatrixMeasureDivergenceOn_dilation_of_on M D hdiv x (rs n)
      (hrs n).ne' (blowupScale (M.variation.singularPart volume) x (rs n)) (hsub n) i }⟩
  intro i
  exact divergenceDilation_tendsto_zero _ (D i) x rs hrs ht hp (hβ i).1.ne (hβ i).2.1

/-- DPR arXiv p. 5, Corollary 1.13, and p. 15; local wave-cone form. -/
theorem ae_matrixPolar_mem_waveCone_of_on [NeZero d]
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hdiv : HasMatrixMeasureDivergenceOn M D U) :
    ∀ᵐ x ∂M.variation.singularPart volume, x ∈ U →
      matrixCoordinates (matrixPolarDensity M x) ∈ matrixDivergenceWaveCone d := by
  filter_upwards [ae_nonempty_matrixPolarBlowupData_of_on M D hU hdiv] with x hx hxU
  by_contra hP
  obtain ⟨b⟩ := hx hxU hP
  exact (MatrixPolarBlowupData.isEmpty_of_regularPart_l1 (M := M) (D := D) (x := x)).false b

/-- DPR arXiv p. 5, Corollary 1.13; local determinant form, every dimension. -/
theorem ae_det_matrixPolar_eq_zero_of_on
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hdiv : HasMatrixMeasureDivergenceOn M D U) :
    ∀ᵐ x ∂M.variation.singularPart volume, x ∈ U →
      (matrixCoordinates (matrixPolarDensity M x)).det = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : M.variation.singularPart volume = 0 := by
      rw [eq_zero_of_matrix_dimension_zero M]
      simp
    rw [h0, ae_zero]
    exact Filter.eventually_bot
  · haveI : NeZero d := ⟨hd.ne'⟩
    filter_upwards [ae_matrixPolar_mem_waveCone_of_on M D hU hdiv] with x hx hxU
    exact (mem_matrixDivergenceWaveCone_iff _).mp (hx hxU)

/--
DPR arXiv p. 5, Corollary 1.13 (printed form, local on an open set); p. 15 (Λ_𝒜 = {rank ≤ d − 1});
model by extension by zero. DPR arXiv p. 5, **Corollary 1.13**, local printed form: rank(dμ/d|μ|)(x)
≤ d − 1 for |μ|ˢ-almost every x ∈ Ω (Ω = open U; μ = M, a finite measure on ℝᵈ arbitrary outside U;
div μ = D tested on U; |μ|ˢ = singular part of Frobenius variation with respect to Lebesgue measure,
restricted to U). Every dimension.
-/
theorem ae_rank_matrixPolar_le_of_on
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hdiv : HasMatrixMeasureDivergenceOn M D U) :
    ∀ᵐ x ∂(M.variation.singularPart volume).restrict U,
      (matrixCoordinates (matrixPolarDensity M x)).rank ≤ d - 1 := by
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [ae_det_matrixPolar_eq_zero_of_on M D hU hdiv] with x hx hxU
  have h := (matrix_rank_lt_iff_det_eq_zero _).mpr (hx hxU)
  omega

/-- consistency control: the local form on U = univ recovers the global form. -/
theorem ae_rank_matrixPolar_le_of_global
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hdiv : HasMatrixMeasureDivergence M D) :
    ∀ᵐ x ∂M.variation.singularPart volume,
      (matrixCoordinates (matrixPolarDensity M x)).rank ≤ d - 1 := by
  have h := ae_rank_matrixPolar_le_of_on M D isOpen_univ (hdiv.hasMatrixMeasureDivergenceOn univ)
  rwa [Measure.restrict_univ] at h

/--
fidelity of the “finite measure on ℝᵈ arbitrary outside U” model: the divergence assumption on U
depends only on the restriction of M to U (DPR extension by zero).
-/
theorem hasMatrixMeasureDivergenceOn_restrict_iff
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : MeasurableSet U) :
    HasMatrixMeasureDivergenceOn (M.restrict U) D U ↔ HasMatrixMeasureDivergenceOn M D U := by
  have hrow : ∀ i, rowMeasure (M.restrict U) i = (rowMeasure M i).restrict U := by
    intro i
    apply VectorMeasure.ext
    intro A hA
    rw [rowMeasure_apply, VectorMeasure.restrict_apply _ hU hA,
      VectorMeasure.restrict_apply _ hU hA, rowMeasure_apply]
  have hb : ∀ i (φ : ScalarCurrentTest d),
      tsupport (φ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ U →
      oneCurrentBoundary (measureOneCurrent (rowMeasure (M.restrict U) i)) φ =
        oneCurrentBoundary (measureOneCurrent (rowMeasure M i)) φ := by
    intro i φ hφ
    rw [hrow, oneCurrentBoundary_apply, oneCurrentBoundary_apply,
      measureOneCurrent_restrict_of_tsupport_subset _ hU _
        ((tsupport_fderiv_subset ℝ).trans hφ)]
  constructor
  · intro h i φ hφ
    rw [h i φ hφ, hb i φ hφ]
  · intro h i φ hφ
    rw [h i φ hφ, hb i φ hφ]

/--
DPR arXiv p. 5, Corollary 1.13, literal reading for μ = M⌊U. DPR arXiv p. 5, Corollary 1.13, literal
reading by extension by zero: for μ = M⌊U (a measure in 𝓜(U; ℝ^{d×d}) extended by zero) and div μ =
D on U, the rank of dμ/d|μ| is ≤ d − 1 for |μ|ˢ-almost every x, with |μ| the variation of μ itself.
-/
theorem ae_rank_matrixPolar_restrict_le
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hdiv : HasMatrixMeasureDivergenceOn M D U) :
    ∀ᵐ x ∂(M.restrict U).variation.singularPart volume,
      (matrixCoordinates (matrixPolarDensity (M.restrict U) x)).rank ≤ d - 1 := by
  have h := ae_rank_matrixPolar_le_of_on (M.restrict U) D hU
    ((hasMatrixMeasureDivergenceOn_restrict_iff M D hU.measurableSet).mpr hdiv)
  have hv : (M.restrict U).variation = M.variation.restrict U :=
    VectorMeasure.variation_restrict hU.measurableSet
  have hmem : ∀ᵐ x ∂(M.restrict U).variation.singularPart volume, x ∈ U := by
    apply (Measure.absolutelyContinuous_of_le
      ((M.restrict U).variation.singularPart_le volume)).ae_le
    rw [hv]
    exact ae_restrict_mem hU.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem hmem] at h

end GeometricMeasure
