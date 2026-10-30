import GeometricMeasure.Current.PositiveTangent
import GeometricMeasure.Current.LinearCombinations
import GeometricMeasure.Current.MatrixDivergence
import GeometricMeasure.Matrix.Ellipticity

/-!
# Matrix polar blow-ups and elimination of the polar matrix

## Main results
A common sequence of rescalings for all matrix rows has a positive nonzero limit, small defects and
a local distributional equation. Differentiation of measures bounds the quotient of the divergence
variation by the singular mass. The geometric radius makes the source negligible. After
multiplication by P⁻¹, the equation holds on the open unit ball and the limit has mass at least 2⁻ᵈ
on B(0, 3/4).

Reference: De Philippis–Rindler, pp. 7–9 and 15.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ}

/--
Jordan uniqueness gives the restriction formula; no identification of the two variations. DPR pp.
8–9, 15: signed right-hand side with factor c*r, local equation on B₁.
-/
theorem signedTotalVariation_restrict
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) :
    SignedMeasure.totalVariation (D.restrict A) = D.totalVariation.restrict A := by
  let j : JordanDecomposition (EuclideanSpace ℝ (Fin d)) := {
    posPart := D.toJordanDecomposition.posPart.restrict A
    negPart := D.toJordanDecomposition.negPart.restrict A
    mutuallySingular := (D.toJordanDecomposition.mutuallySingular.restrict A).symm.restrict A |>.symm }
  have hj : j.toSignedMeasure = D.restrict A := by
    conv_rhs => rw [← D.toSignedMeasure_toJordanDecomposition]
    simp only [JordanDecomposition.toSignedMeasure]
    rw [VectorMeasure.restrict_sub,
      VectorMeasure.restrict_toSignedMeasure hA, VectorMeasure.restrict_toSignedMeasure hA]
  rw [← hj, SignedMeasure.totalVariation, JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  exact (Measure.restrict_add _ _ _).symm

/--
The actual localized signed right hand side, with the dilation factor c*r. DPR pp. 8–9, 15: signed
right-hand side with factor c*r, local equation on B₁.
-/
def divergenceDilation (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    SignedMeasure (EuclideanSpace ℝ (Fin d)) :=
  (c * r) • (D.restrict (closedBall x |r|)).map (dilationEquiv x r hr)

/--
Exact total Jordan variation of the right-hand side: |c*r| times its variation on the source ball.
DPR pp. 8–9, 15: signed right-hand side with factor c*r, local equation on B₁.
-/
theorem totalVariation_divergenceDilation_univ
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    (divergenceDilation D x r hr c).totalVariation univ =
      ENNReal.ofReal |c * r| * D.totalVariation (closedBall x |r|) := by
  rw [divergenceDilation, signedTotalVariation_smul, signedTotalVariation_map_equiv,
    signedTotalVariation_restrict D measurableSet_closedBall,
    Measure.smul_apply, (dilationEquiv x r hr).map_apply]
  change (‖c * r‖₊ : ℝ≥0∞) * _ = _
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_eq_abs]
  simp

/--
Each row of the matrix dilation is exactly the localized dilation of that row. DPR pp. 8–9, 15:
signed right-hand side with factor c*r, local equation on B₁.
-/
theorem rowMeasure_matrixDilation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) (i : Fin d) :
    rowMeasure (matrixDilation M x r hr c) i = localizedDilation (rowMeasure M i) x r hr c := by
  apply VectorMeasure.ext
  intro A hA
  rw [rowMeasure_apply, matrixDilation, smul_apply,
    VectorMeasure.map_apply _ (dilationEquiv x r hr).measurable hA,
    VectorMeasure.restrict_apply _ measurableSet_closedBall ((dilationEquiv x r hr).measurable hA),
    map_smul, localizedDilation, smul_apply,
    VectorMeasure.map_apply _ (dilationEquiv x r hr).measurable hA,
    VectorMeasure.restrict_apply _ measurableSet_closedBall ((dilationEquiv x r hr).measurable hA),
    rowMeasure_apply]

/--
Global measure divergence yields the row-wise dilated equation on the open unit ball only. DPR pp.
8–9, 15: signed right-hand side with factor c*r, local equation on B₁.
-/
theorem hasMatrixMeasureDivergenceOn_dilation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hdiv : HasMatrixMeasureDivergence M D)
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) (i : Fin d) :
    HasMeasureDivergenceOn (rowMeasure (matrixDilation M x r hr c) i)
      (divergenceDilation (D i) x r hr c) (ball 0 1) := by
  rw [rowMeasure_matrixDilation]
  exact hasMeasureDivergenceOn_localizedDilation _ _ (hdiv i) x r hr c

/--
Boundary convention: div N = div (N-M) + Q, equivalently B(N)=B(N-M)-Q. DPR pp. 8–9, 15: signed
right-hand side with factor c*r, local equation on B₁.
-/
theorem frozenMatrixDivergence_identity
    (N M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (Q : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hdiv : ∀ i, HasMeasureDivergenceOn (rowMeasure M i) (Q i) (ball 0 1))
    (i : Fin d) (φ : ScalarCurrentTest d)
    (hφ : tsupport (φ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ ball 0 1) :
    oneCurrentBoundary (measureOneCurrent (rowMeasure N i)) φ =
      oneCurrentBoundary (measureOneCurrent (rowMeasure (N - M) i)) φ - signedTestCurrent (Q i) φ := by
  have heq : rowMeasure N i = rowMeasure (N - M) i + rowMeasure M i := by
    apply VectorMeasure.ext
    intro A hA
    simp only [rowMeasure_apply, add_apply, sub_apply, map_sub]
    abel
  rw [hdiv i φ hφ, sub_neg_eq_add]
  conv_lhs => rw [heq, measureOneCurrent_add]
  simp only [oneCurrentBoundary_apply, add_apply]

/--
The localized right-hand side tends to zero in total variation if the source quotient has a finite
limit and the positive radii tend to zero. DPR pp. 8–9, 15: signed right-hand side with factor
c*r, local equation on B₁.
-/
theorem divergenceDilation_tendsto_zero
    (s : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure s]
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) (rs : ℕ → ℝ) (hrs : ∀ n, 0 < rs n)
    (ht : Tendsto rs atTop (𝓝[>] (0 : ℝ)))
    (hp : ∀ n, 0 < s (closedBall x (rs n))) {b : ℝ≥0∞} (hb : b ≠ ⊤)
    (hD : Tendsto (fun r => D.totalVariation (closedBall x r) / s (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 b)) :
    Tendsto (fun n => (divergenceDilation D x (rs n) (hrs n).ne'
      (blowupScale s x (rs n))).totalVariation univ) atTop (𝓝 0) := by
  simpa only [totalVariation_divergenceDilation_univ, abs_of_pos (hrs _)] using
    scaledMass_tendsto_zero s D.totalVariation x rs hrs ht hp hb hD

/--
Unrestricted push-forwards have the same small variation on the fixed unit ball. DPR pp. 8–9, 15:
signed right-hand side with factor c*r, local equation on B₁.
-/
theorem unlocalized_divergenceDilation_tendsto_zero
    (s : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure s]
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) (rs : ℕ → ℝ) (hrs : ∀ n, 0 < rs n)
    (ht : Tendsto rs atTop (𝓝[>] (0 : ℝ)))
    (hp : ∀ n, 0 < s (closedBall x (rs n))) {b : ℝ≥0∞} (hb : b ≠ ⊤)
    (hD : Tendsto (fun r => D.totalVariation (closedBall x r) / s (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 b)) :
    Tendsto (fun n => SignedMeasure.totalVariation
      ((blowupScale s x (rs n) * rs n) • D.map (dilationEquiv x (rs n) (hrs n).ne'))
      (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)) atTop (𝓝 0) := by
  have hh := scaledMass_tendsto_zero s D.totalVariation x rs hrs ht hp hb hD
  apply hh.congr'
  filter_upwards with n
  rw [signedTotalVariation_smul, signedTotalVariation_map_equiv, Measure.smul_apply,
    (dilationEquiv x (rs n) (hrs n).ne').map_apply, preimage_closedBall_dilation,
    mul_one, abs_of_pos (hrs n)]
  change _ = (‖blowupScale s x (rs n) * rs n‖₊ : ℝ≥0∞) * _
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_eq_abs]

/--
Locality: convergence of the total mass controls every subset, with no boundary hypothesis. DPR pp.
8–9, 15: signed right-hand side with factor c*r, local equation on B₁.
-/
theorem variation_on_tendsto_zero_of_univ
    (Ms : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (h : Tendsto (fun n => (Ms n).variation univ) atTop (𝓝 0))
    (A : Set (EuclideanSpace ℝ (Fin d))) :
    Tendsto (fun n => (Ms n).variation A) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun _ => zero_le) (fun _ => measure_mono (subset_univ A))

end GeometricMeasure

namespace GeometricMeasure
variable {d : ℕ}

/--
The blow-up data consists of a fixed matrix, positive nonzero limit, actual rescalings, small total
variations and the local distributional equation. DPR pp. 7–9, 15: common package, constructed
almost everywhere under the displayed assumptions.
-/
structure MatrixPolarBlowupData
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) where
  radii : ℕ → ℝ
  radii_pos : ∀ n, 0 < radii n
  radii_tendsto : Tendsto radii atTop (𝓝[>] (0 : ℝ))
  mass_pos : ∀ n, 0 < (M.variation.singularPart volume) (closedBall x (radii n))
  tangent : FiniteMeasure (EuclideanSpace ℝ (Fin d))
  tangent_mass_le : tangent.mass ≤ 1
  tangent_support : tangent (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0
  positive_convergence : Tendsto (fun n => normalizedPositiveDilation
    (M.variation.singularPart volume) x (radii n) (radii_pos n).ne') atTop (𝓝 tangent)
  cutoff_lower_bound : ((2 : ℝ) ^ d)⁻¹ ≤
    ∫ y, tentCutoff y ∂(tangent : Measure (EuclideanSpace ℝ (Fin d)))
  tangent_nonzero : 0 < (tangent : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 1)
  polar_unit : ‖matrixPolarDensity M x‖ = 1
  det_ne_zero : (matrixCoordinates (matrixPolarDensity M x)).det ≠ 0
  ellipticity_pos : 0 < matrixEllipticityConstant (matrixCoordinates (matrixPolarDensity M x))
  elliptic_bound : ∀ ξ : EuclideanSpace ℝ (Fin d),
    matrixEllipticityConstant (matrixCoordinates (matrixPolarDensity M x)) * ‖ξ‖ ≤
      ‖matrixEuclideanCLM (matrixCoordinates (matrixPolarDensity M x)) ξ‖
  symbol_bound : ∀ ξ : EuclideanSpace ℝ (Fin d),
    (2 * Real.pi * matrixEllipticityConstant (matrixCoordinates (matrixPolarDensity M x))) * ‖ξ‖ ≤
      ‖matrixDivergenceSymbol (matrixCoordinates (matrixPolarDensity M x)) ξ‖
  frozen_error : Tendsto (fun n =>
    ((positiveDilation (M.variation.singularPart volume) x (radii n) (radii_pos n).ne'
      (blowupScale (M.variation.singularPart volume) x (radii n))).withDensityᵥ
        (fun _ => matrixPolarDensity M x) -
      matrixDilation M x (radii n) (radii_pos n).ne'
        (blowupScale (M.variation.singularPart volume) x (radii n))).variation univ)
    atTop (𝓝 0)
  matrix_mass : Tendsto (fun n => (matrixDilation M x (radii n) (radii_pos n).ne'
    (blowupScale (M.variation.singularPart volume) x (radii n))).variation univ) atTop (𝓝 1)
  rhs_error : ∀ i, Tendsto (fun n =>
    (divergenceDilation (D i) x (radii n) (radii_pos n).ne'
      (blowupScale (M.variation.singularPart volume) x (radii n))).totalVariation univ)
    atTop (𝓝 0)
  equation : ∀ n i, HasMeasureDivergenceOn
    (rowMeasure (matrixDilation M x (radii n) (radii_pos n).ne'
      (blowupScale (M.variation.singularPart volume) x (radii n))) i)
    (divergenceDilation (D i) x (radii n) (radii_pos n).ne'
      (blowupScale (M.variation.singularPart volume) x (radii n))) (ball 0 1)

/--
Almost every singular point supplies the entire package whenever its polar is outside the wave cone.
The same radii occur in every field, including every row of the divergence. DPR pp. 7–9, 15: common
package, constructed almost everywhere under the displayed assumptions.
-/
theorem ae_nonempty_matrixPolarBlowupData [NeZero d]
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hdiv : HasMatrixMeasureDivergence M D) :
    ∀ᵐ x ∂M.variation.singularPart volume,
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
  intro hP
  obtain ⟨-, hpos, ha, hratio, -, -, -, hβ⟩ := hx
  obtain ⟨rs, hrs, ht, hp, ν, hm, hs, hconv, hlow, hn⟩ :=
    exists_positive_tangent_of_goodRadii (M.variation.singularPart volume) x hgood hpos
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
    equation := fun n i => hasMatrixMeasureDivergenceOn_dilation M D hdiv x (rs n)
      (hrs n).ne' (blowupScale (M.variation.singularPart volume) x (rs n)) i }⟩
  intro i
  exact divergenceDilation_tendsto_zero _ (D i) x rs hrs ht hp (hβ i).1.ne (hβ i).2.1

namespace MatrixPolarBlowupData
variable {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))}
variable {x : EuclideanSpace ℝ (Fin d)}

/--
Finite positive measure obtained from the package radii and normalized by the singular source mass.
DPR pp. 7–9, 15: common package, constructed almost everywhere under the displayed assumptions.
-/
def positive (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
  normalizedPositiveDilation (M.variation.singularPart volume) x (b.radii n) (b.radii_pos n).ne'

/--
Actual dilation of M with the package radii and singular normalization. DPR pp. 7–9, 15: common
package, constructed almost everywhere under the displayed assumptions.
-/
def matrix (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d) :=
  matrixDilation M x (b.radii n) (b.radii_pos n).ne'
    (blowupScale (M.variation.singularPart volume) x (b.radii n))

/--
Actual signed dilation of the row of D, with the same source restriction and factor c*r. DPR pp.
7–9, 15: common package, constructed almost everywhere under the displayed assumptions.
-/
def rhs (b : MatrixPolarBlowupData M D x) (n : ℕ) (i : Fin d) :
    SignedMeasure (EuclideanSpace ℝ (Fin d)) :=
  divergenceDilation (D i) x (b.radii n) (b.radii_pos n).ne'
    (blowupScale (M.variation.singularPart volume) x (b.radii n))

/--
Frozen defect Pν − M, where P is the polar of M at the fixed point of the package. DPR pp. 7–9, 15:
common package, constructed almost everywhere under the displayed assumptions.
-/
def defect (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d) :=
  (b.positive n : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
    (fun _ => matrixPolarDensity M x) - b.matrix n

/--
Each positive measure in the package has mass exactly one. DPR pp. 7–9, 15: common package,
constructed almost everywhere under the displayed assumptions.
-/
theorem positive_mass (b : MatrixPolarBlowupData M D x) (n : ℕ) : (b.positive n).mass = 1 := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass]
  exact positiveDilation_normalized_univ _ _ _ _
    (by simpa [abs_of_pos (b.radii_pos n)] using b.mass_pos n)

/--
Each positive measure of the sequence is singular with respect to volume; no claim that the limit is
singular. DPR pp. 7–9, 15: common package, constructed almost everywhere under the displayed
assumptions.
-/
theorem positive_singular (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    (b.positive n : Measure (EuclideanSpace ℝ (Fin d))) ⟂ₘ volume :=
  positiveDilation_singular _ (M.variation.mutuallySingular_singularPart volume) _ _ _ _

/--
The positive weak limit of the package has mass exactly one. DPR pp. 7–9, 15: common package,
constructed almost everywhere under the displayed assumptions.
-/
theorem tangent_mass_eq_one (b : MatrixPolarBlowupData M D x) : b.tangent.mass = 1 :=
  normalizedPositiveDilation_limit_mass _ x b.radii b.radii_pos b.mass_pos _ b.positive_convergence

/--
Row-wise frozen identity on tests supported in B₁, in the boundary convention: B(Pν) = B(F) − Q. DPR
pp. 7–9, 15: common package, constructed almost everywhere under the displayed assumptions.
-/
theorem frozen_equation (b : MatrixPolarBlowupData M D x) (n : ℕ) (i : Fin d)
    (φ : ScalarCurrentTest d)
    (hφ : tsupport (φ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ ball 0 1) :
    oneCurrentBoundary (measureOneCurrent (rowMeasure
      ((b.positive n : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
        (fun _ => matrixPolarDensity M x)) i)) φ =
      oneCurrentBoundary (measureOneCurrent (rowMeasure (b.defect n) i)) φ -
        signedTestCurrent (b.rhs n i) φ :=
  frozenMatrixDivergence_identity _ _ _ (b.equation n) i φ hφ

/--
The variation of the defect tends to zero on every set, without boundary or measurability
conditions. DPR pp. 7–9, 15: common package, constructed almost everywhere under the displayed
assumptions.
-/
theorem defect_on_tendsto (b : MatrixPolarBlowupData M D x)
    (A : Set (EuclideanSpace ℝ (Fin d))) :
    Tendsto (fun n => (b.defect n).variation A) atTop (𝓝 0) :=
  variation_on_tendsto_zero_of_univ _ b.frozen_error A

/--
The Jordan variation of every row of the right-hand side tends to zero on every set. DPR pp. 7–9,
15: common package, constructed almost everywhere under the displayed assumptions.
-/
theorem rhs_on_tendsto (b : MatrixPolarBlowupData M D x) (i : Fin d)
    (A : Set (EuclideanSpace ℝ (Fin d))) :
    Tendsto (fun n => (b.rhs n i).totalVariation A) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (b.rhs_error i)
    (fun _ => zero_le) (fun _ => measure_mono (subset_univ A))

/--
The total mass of the matrix dilations is eventually bounded by two. DPR pp. 7–9, 15: common
package, constructed almost everywhere under the displayed assumptions.
-/
theorem eventually_matrix_mass_le_two (b : MatrixPolarBlowupData M D x) :
    ∀ᶠ n in atTop, (b.matrix n).variation univ ≤ 2 :=
  (b.matrix_mass.eventually_lt_const (by norm_num : (1 : ℝ≥0∞) < 2)).mono (fun _ h => h.le)

/--
A fixed interior margin: nonzero mass already in the open ball of radius 3/4. DPR pp. 7–9, 15:
common package, constructed almost everywhere under the displayed assumptions.
-/
theorem tangent_three_quarters_pos (b : MatrixPolarBlowupData M D x) :
    0 < (b.tangent : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 (3 / 4)) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hi : (∫ y, tentCutoff y ∂(b.tangent : Measure (EuclideanSpace ℝ (Fin d)))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with y hy
    rw [mem_ball, dist_zero_right, not_lt] at hy
    rw [tentCutoff_apply, min_eq_right (by linarith), max_eq_left (by linarith)]
    rfl
  have hh := b.cutoff_lower_bound
  rw [hi] at hh
  exact (not_le_of_gt (by positivity : 0 < ((2 : ℝ) ^ d)⁻¹)) hh

end MatrixPolarBlowupData

end GeometricMeasure

namespace GeometricMeasure
variable {d : ℕ}

/--
Left multiplication by a fixed coordinate matrix, assembled from matrix rows. DPR connection pp.
8–9, 15: multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
def matrixLeftMulCLM (A : Matrix (Fin d) (Fin d) ℝ) : MatrixSpace d →L[ℝ] MatrixSpace d :=
  ∑ a : Fin d, ∑ b : Fin d, A a b • (rowInsertCLM a).comp (rowCLM b)

/--
Row a of left multiplication by A is the combination of the rows of Q with coefficients A a b. DPR
connection pp. 8–9, 15: multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
theorem rowCLM_matrixLeftMulCLM (A : Matrix (Fin d) (Fin d) ℝ) (Q : MatrixSpace d) (a : Fin d) :
    rowCLM a (matrixLeftMulCLM A Q) = ∑ b : Fin d, A a b • rowCLM b Q := by
  simp [matrixLeftMulCLM, map_sum, rowCLM_rowInsertCLM]

/--
Continuous multiplication on Frobenius space agrees exactly with coordinate matrix multiplication.
DPR connection pp. 8–9, 15: multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
theorem matrixCoordinates_matrixLeftMulCLM (A : Matrix (Fin d) (Fin d) ℝ) (Q : MatrixSpace d) :
    matrixCoordinates (matrixLeftMulCLM A Q) = A * matrixCoordinates Q := by
  ext a j
  rw [matrixCoordinates_row, rowCLM_matrixLeftMulCLM, Matrix.mul_apply]
  simp [matrixCoordinates_row]

/--
With P invertible in coordinates, P⁻¹P has rows the canonical basis. DPR connection pp. 8–9, 15:
multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
theorem rowCLM_matrixLeftMulCLM_inv_self (P : MatrixSpace d)
    (hP : (matrixCoordinates P).det ≠ 0) (a : Fin d) :
    rowCLM a (matrixLeftMulCLM (matrixCoordinates P)⁻¹ P) = EuclideanSpace.single a 1 := by
  have h := matrixCoordinates_matrixLeftMulCLM (matrixCoordinates P)⁻¹ P
  rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hP)] at h
  ext j
  have hj := congrFun (congrFun h a) j
  rw [matrixCoordinates_row] at hj
  rw [hj, PiLp.single_apply, Matrix.one_apply]
  simp [eq_comm]

/--
Image of a matrix measure under continuous linear left multiplication by a fixed matrix. DPR
connection pp. 8–9, 15: multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
def matrixLeftMul (A : Matrix (Fin d) (Fin d) ℝ)
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)) :
    VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d) :=
  N.mapRange (matrixLeftMulCLM A).toLinearMap.toAddMonoidHom (matrixLeftMulCLM A).continuous

/--
The rows of the multiplied measure are the corresponding finite combinations of the row measures.
DPR connection pp. 8–9, 15: multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
theorem rowMeasure_matrixLeftMul (A : Matrix (Fin d) (Fin d) ℝ)
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)) (a : Fin d) :
    rowMeasure (matrixLeftMul A N) a = ∑ b : Fin d, A a b • rowMeasure N b := by
  apply VectorMeasure.ext
  intro s _
  simp [rowMeasure_apply, matrixLeftMul, rowCLM_matrixLeftMulCLM]

/--
Left multiplication of a matrix measure commutes with subtraction. DPR connection pp. 8–9, 15:
multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
theorem matrixLeftMul_sub (A : Matrix (Fin d) (Fin d) ℝ)
    (N₁ N₂ : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)) :
    matrixLeftMul A (N₁ - N₂) = matrixLeftMul A N₁ - matrixLeftMul A N₂ := by
  apply VectorMeasure.ext
  intro s _
  simp [matrixLeftMul, map_sub]

/--
For a finite positive measure, left multiplication commutes with constant matrix density. DPR
connection pp. 8–9, 15: multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
theorem matrixLeftMul_withDensityᵥ_const (A : Matrix (Fin d) (Fin d) ℝ)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν] (Q : MatrixSpace d) :
    matrixLeftMul A (ν.withDensityᵥ (fun _ => Q)) =
      ν.withDensityᵥ (fun _ => matrixLeftMulCLM A Q) :=
  withDensityᵥ_mapRange ν (integrable_const Q) (matrixLeftMulCLM A)

/--
A row of a constant matrix density is the corresponding constant vector density. DPR connection pp.
8–9, 15: multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
theorem rowMeasure_withDensityᵥ_const (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    (Q : MatrixSpace d) (a : Fin d) :
    rowMeasure (ν.withDensityᵥ (fun _ => Q)) a = ν.withDensityᵥ (fun _ => rowCLM a Q) :=
  withDensityᵥ_mapRange ν (integrable_const Q) (rowCLM a)

/--
Measure domination: variation after multiplication is bounded by the operator norm on Frobenius
space times the initial variation. DPR connection pp. 8–9, 15: multiplication by P⁻¹, equation on B₁
and mass in B(0,3/4).
-/
theorem variation_matrixLeftMul_le (A : Matrix (Fin d) (Fin d) ℝ)
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)) :
    (matrixLeftMul A N).variation ≤ ENNReal.ofReal ‖matrixLeftMulCLM A‖ • N.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro s _
  rw [Measure.smul_apply, smul_eq_mul]
  calc
    ‖matrixLeftMul A N s‖ₑ = ENNReal.ofReal ‖matrixLeftMulCLM A (N s)‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖matrixLeftMulCLM A‖ * ‖N s‖) :=
      ENNReal.ofReal_le_ofReal ((matrixLeftMulCLM A).le_opNorm _)
    _ = ENNReal.ofReal ‖matrixLeftMulCLM A‖ * ‖N s‖ₑ := by
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
    _ ≤ _ := by gcongr; exact VectorMeasure.enorm_measure_le_variation N s

namespace MatrixPolarBlowupData
variable {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))}
variable {x : EuclideanSpace ℝ (Fin d)}

/--
E_j = I ν_j − P⁻¹ M_j, the identity being written P⁻¹P. DPR connection pp. 8–9, 15:
multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
def inverseDefect (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d) :=
  (b.positive n : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
      (fun _ => matrixLeftMulCLM (matrixCoordinates (matrixPolarDensity M x))⁻¹
        (matrixPolarDensity M x)) -
    matrixLeftMul (matrixCoordinates (matrixPolarDensity M x))⁻¹ (b.matrix n)

/--
q_j, row a, equal to Σ_c (P⁻¹)_{ac} Q_{j,c}, with the dilation factor c_j r_j inside Q. DPR
connection pp. 8–9, 15: multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
def inverseRhs (b : MatrixPolarBlowupData M D x) (n : ℕ) (a : Fin d) :
    SignedMeasure (EuclideanSpace ℝ (Fin d)) :=
  ∑ c : Fin d, (matrixCoordinates (matrixPolarDensity M x))⁻¹ a c • b.rhs n c

/--
The defect with P⁻¹ is exactly the image of the frozen defect under left multiplication by P⁻¹. DPR
connection pp. 8–9, 15: multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
theorem inverseDefect_eq (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    b.inverseDefect n =
      matrixLeftMul (matrixCoordinates (matrixPolarDensity M x))⁻¹ (b.defect n) := by
  rw [defect, matrixLeftMul_sub, matrixLeftMul_withDensityᵥ_const]
  rfl

/--
Row a of the identity part is ν_j e_a. DPR connection pp. 8–9, 15: multiplication by P⁻¹, equation
on B₁ and mass in B(0,3/4).
-/
theorem rowMeasure_inverseDefect_identity (b : MatrixPolarBlowupData M D x) (n : ℕ) (a : Fin d) :
    rowMeasure ((b.positive n : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
      (fun _ => matrixLeftMulCLM (matrixCoordinates (matrixPolarDensity M x))⁻¹
        (matrixPolarDensity M x))) a =
      (b.positive n : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
        (fun _ => EuclideanSpace.single a (1 : ℝ)) := by
  rw [rowMeasure_withDensityᵥ_const, rowCLM_matrixLeftMulCLM_inv_self _ b.det_ne_zero]

/--
Local divergence of the measure P⁻¹M: the right-hand side is the combination of rows by P⁻¹, on B₁.
DPR connection pp. 8–9, 15: multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
theorem inverse_equation (b : MatrixPolarBlowupData M D x) (n : ℕ) (a : Fin d) :
    HasMeasureDivergenceOn
      (rowMeasure (matrixLeftMul (matrixCoordinates (matrixPolarDensity M x))⁻¹ (b.matrix n)) a)
      (b.inverseRhs n a) (ball 0 1) := by
  rw [rowMeasure_matrixLeftMul]
  exact hasMeasureDivergenceOn_finset_sum_smul _ _ _ _ _ (fun c => b.equation n c)

/--
∇ν_j = div E_j + q_j in D'(B₁), written in the boundary convention. DPR connection pp. 8–9, 15:
multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
theorem gradient_equation (b : MatrixPolarBlowupData M D x) (n : ℕ) (a : Fin d)
    (φ : ScalarCurrentTest d)
    (hφ : tsupport (φ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ ball 0 1) :
    oneCurrentBoundary (measureOneCurrent
      ((b.positive n : Measure (EuclideanSpace ℝ (Fin d))).withDensityᵥ
        (fun _ => EuclideanSpace.single a (1 : ℝ)))) φ =
      oneCurrentBoundary (measureOneCurrent (rowMeasure (b.inverseDefect n) a)) φ -
        signedTestCurrent (b.inverseRhs n a) φ := by
  rw [← b.rowMeasure_inverseDefect_identity n a]
  exact frozenMatrixDivergence_identity _ _ _ (fun c => b.inverse_equation n c) a φ hφ

/--
|E_j| → 0, with the constant ‖P⁻¹·‖. DPR connection pp. 8–9, 15: multiplication by P⁻¹, equation on
B₁ and mass in B(0,3/4).
-/
theorem inverseDefect_tendsto (b : MatrixPolarBlowupData M D x) :
    Tendsto (fun n => (b.inverseDefect n).variation univ) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.const_mul (b.defect_on_tendsto univ)
    (Or.inr ENNReal.ofReal_ne_top)
    (a := ENNReal.ofReal ‖matrixLeftMulCLM (matrixCoordinates (matrixPolarDensity M x))⁻¹‖)
  rw [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun _ => zero_le) (fun n => ?_)
  rw [b.inverseDefect_eq n]
  exact (variation_matrixLeftMul_le _ _ univ).trans_eq (by rw [Measure.smul_apply, smul_eq_mul])

/--
|q_j| → 0, row by row. DPR connection pp. 8–9, 15: multiplication by P⁻¹, equation on B₁ and mass in
B(0,3/4).
-/
theorem inverseRhs_tendsto (b : MatrixPolarBlowupData M D x) (a : Fin d) :
    Tendsto (fun n => (b.inverseRhs n a).totalVariation univ) atTop (𝓝 0) := by
  have h : Tendsto (fun n => ∑ c : Fin d,
      ENNReal.ofReal |(matrixCoordinates (matrixPolarDensity M x))⁻¹ a c| *
        (b.rhs n c).totalVariation univ) atTop (𝓝 0) := by
    have hs := tendsto_finsetSum (Finset.univ : Finset (Fin d)) (fun c _ =>
      ENNReal.Tendsto.const_mul (b.rhs_error c) (Or.inr ENNReal.ofReal_ne_top)
        (a := ENNReal.ofReal |(matrixCoordinates (matrixPolarDensity M x))⁻¹ a c|))
    simp only [mul_zero, Finset.sum_const_zero] at hs
    exact hs
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    (fun n => signedTotalVariation_finset_sum_smul_le _ _ _ isOpen_univ)

/--
Every νⱼ is carried by the closed unit ball (common compact support). DPR connection pp. 8–9, 15:
multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
theorem positive_support (b : MatrixPolarBlowupData M D x) (n : ℕ) :
    (b.positive n : Measure (EuclideanSpace ℝ (Fin d)))
      (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 :=
  positiveDilation_compl _ _ _ _ _

/--
Quantitative interior mass : ν(B(0,3/4)) ≥ 2⁻ᵈ, open ball. DPR connection pp. 8–9, 15:
multiplication by P⁻¹, equation on B₁ and mass in B(0,3/4).
-/
theorem tangent_three_quarters_ge (b : MatrixPolarBlowupData M D x) :
    ((2 : ℝ) ^ d)⁻¹ ≤
      (b.tangent : Measure (EuclideanSpace ℝ (Fin d))).real (ball 0 (3 / 4)) := by
  refine b.cutoff_lower_bound.trans ?_
  rw [← integral_indicator_one measurableSet_ball]
  apply integral_mono
    ((tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).integrable _)
    ((integrable_const (1 : ℝ)).indicator measurableSet_ball)
  intro y
  by_cases hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (3 / 4)
  · rw [indicator_of_mem hy]
    exact tentCutoff_le_one y
  · rw [indicator_of_notMem hy]
    rw [mem_ball, dist_zero_right, not_lt] at hy
    rw [tentCutoff_apply, min_eq_right (by linarith), max_eq_left (by linarith)]

end MatrixPolarBlowupData

end GeometricMeasure
