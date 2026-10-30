import GeometricMeasure.VectorMeasure.SingularDifferentiation
import GeometricMeasure.VectorMeasure.DilationGeometry
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# exact transport and freezing of the matrix polar

## Main results
De Philippis–Rindler (2016), pp. 7–9. Restriction to the same closed source ball, Frobenius norm and
normalization by the singular part. The limits hold along every admissible sequence; they assume
neither divergence nor ellipticity.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ}

/--
Positive dilation, restricted at the source to the closed ball. DPR pp. 7–9: transport and source
estimate.
-/
def positiveDilation (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  ENNReal.ofReal c • (μ.restrict (closedBall x |r|)).map (dilationEquiv x r hr)

/--
A finite source measure yields a finite positive dilation for every real scalar. DPR pp. 7–9:
transport and source estimate.
-/
instance isFiniteMeasure_positiveDilation (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    IsFiniteMeasure (positiveDilation μ x r hr c) := by
  unfold positiveDilation
  refine ⟨?_⟩
  rw [Measure.smul_apply]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/--
Frobenius-valued version of the localized dilation. DPR pp. 7–9: transport and source estimate.
-/
def matrixDilation (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d) :=
  c • (M.restrict (closedBall x |r|)).map (dilationEquiv x r hr)

/--
Total variation of the matrix dilation: |c| times the variation on the source ball of radius |r|.
DPR pp. 7–9: transport and source estimate.
-/
theorem variation_matrixDilation_univ
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    (matrixDilation M x r hr c).variation univ =
      ENNReal.ofReal |c| * M.variation (closedBall x |r|) := by
  rw [matrixDilation, VectorMeasure.variation_smul,
    (dilationEquiv x r hr).measurableEmbedding.variation_map,
    VectorMeasure.variation_restrict measurableSet_closedBall,
    Measure.smul_apply, (dilationEquiv x r hr).map_apply]
  change (‖c‖₊ : ℝ≥0∞) * _ = _
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_eq_abs]
  simp

/--
Exact total mass: ofReal c times the source mass, without a finiteness assumption. DPR pp. 7–9:
transport and source estimate.
-/
theorem positiveDilation_univ (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    positiveDilation μ x r hr c univ = ENNReal.ofReal c * μ (closedBall x |r|) := by
  simp [positiveDilation, (dilationEquiv x r hr).map_apply]

/--
The positive dilation is supported in the closed unit ball, for every real scalar. DPR pp. 7–9:
transport and source estimate.
-/
theorem positiveDilation_compl (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    positiveDilation μ x r hr c (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 := by
  rw [positiveDilation, Measure.smul_apply, (dilationEquiv x r hr).map_apply,
    preimage_compl, preimage_closedBall_dilation, mul_one,
    Measure.restrict_apply measurableSet_closedBall.compl]
  simp

/--
Transport of a constant matrix density for a finite measure and c ≥ 0; r may be negative. DPR pp.
7–9: transport and source estimate.
-/
theorem constantMatrix_positiveDilation (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (P : MatrixSpace d)
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    (positiveDilation μ x r hr c).withDensityᵥ (fun _ => P) =
      matrixDilation (μ.withDensityᵥ (fun _ => P)) x r hr c := by
  apply VectorMeasure.ext
  intro A hA
  rw [withDensityᵥ_apply (integrable_const P) hA]
  rw [matrixDilation, smul_apply, VectorMeasure.map_apply _
    (dilationEquiv x r hr).measurable hA, VectorMeasure.restrict_apply _
    measurableSet_closedBall ((dilationEquiv x r hr).measurable hA),
    withDensityᵥ_apply (integrable_const P)
      (((dilationEquiv x r hr).measurable hA).inter measurableSet_closedBall)]
  simp only [setIntegral_const, smul_smul]
  congr 1
  simp [positiveDilation, measureReal_def, (dilationEquiv x r hr).map_apply,
    Measure.restrict_apply ((dilationEquiv x r hr).measurable hA),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

/--
The defect Pν − M commutes exactly with dilation when c ≥ 0 and the positive source measure is
finite. DPR pp. 7–9: transport and source estimate.
-/
theorem frozenMatrixDefect_dilation (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (s : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure s] (P : MatrixSpace d)
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    (positiveDilation s x r hr c).withDensityᵥ (fun _ => P) - matrixDilation M x r hr c =
      matrixDilation (s.withDensityᵥ (fun _ => P) - M) x r hr c := by
  rw [constantMatrix_positiveDilation s P x r hr hc]
  unfold matrixDilation
  rw [VectorMeasure.restrict_sub]
  change _ = c • VectorMeasure.mapGm (dilationEquiv x r hr) (_ - _)
  rw [map_sub, smul_sub]
  rfl

/--
The source estimate includes the absolutely continuous mass, as in DPR p. 9. DPR pp. 7–9: transport
and source estimate.
-/
theorem frozenMatrixDefect_variation_le
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (P : MatrixSpace d) (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A) :
    ((M.variation.singularPart volume).withDensityᵥ (fun _ => P) - M).variation A ≤
      (∫⁻ y in A, ‖P - matrixPolarDensity M y‖ₑ ∂M.variation) +
        ‖P‖ₑ * (volume.withDensity (M.variation.rnDeriv volume)) A := by
  let s := M.variation.singularPart volume
  let a := volume.withDensity (M.variation.rnDeriv volume)
  have hsum : M.variation.withDensityᵥ (fun _ => P) =
      s.withDensityᵥ (fun _ => P) + a.withDensityᵥ (fun _ => P) := by
    apply VectorMeasure.ext
    intro B hB
    rw [withDensityᵥ_apply (integrable_const P) hB, add_apply,
      withDensityᵥ_apply (integrable_const P) hB, withDensityᵥ_apply (integrable_const P) hB]
    conv_lhs => rw [M.variation.haveLebesgueDecomposition_add volume,
      Measure.restrict_add, integral_add_measure (integrable_const P) (integrable_const P)]
  have heq : s.withDensityᵥ (fun _ => P) - M =
      M.variation.withDensityᵥ (fun y => P - matrixPolarDensity M y) -
        a.withDensityᵥ (fun _ => P) := by
    rw [withDensityᵥ_sub' (integrable_const P) (integrable_matrixPolarDensity M),
      withDensityᵥ_matrixPolarDensity, hsum]
    abel
  rw [heq]
  apply (VectorMeasure.variation_sub_le A).trans
  rw [Measure.add_apply, Measure.variation_withDensityᵥ
    (show Integrable (fun y => P - matrixPolarDensity M y) M.variation from
      (integrable_const P).sub (integrable_matrixPolarDensity M)),
    Measure.variation_withDensityᵥ (integrable_const P),
    withDensity_apply _ hA, withDensity_apply _ hA]
  simp [a]

end GeometricMeasure

namespace GeometricMeasure
variable {d : ℕ}

/--
The reciprocal normalization for the dilation by singular mass. DPR pp. 7–9: singular normalization
and limits along every admissible sequence.
-/
def blowupScale (s : Measure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) : ℝ :=
  (s.real (closedBall x |r|))⁻¹

/--
The reciprocal real coefficient is always nonnegative, including the zero-real-mass branches. DPR
pp. 7–9: singular normalization and limits along every admissible sequence.
-/
theorem blowupScale_nonneg (s : Measure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) : 0 ≤ blowupScale s x r :=
  inv_nonneg.mpr measureReal_nonneg

/--
The finite-measure wrapper keeps its weak topology explicit. DPR pp. 7–9: singular normalization and
limits along every admissible sequence.
-/
def normalizedPositiveDilation (s : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure s]
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) :
    FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
  ⟨positiveDilation s x r hr (blowupScale s x r), inferInstance⟩

/--
Identification with the ENNReal inverse when the source measure is finite and the ball has strictly
positive mass. DPR pp. 7–9: singular normalization and limits along every admissible sequence.
-/
theorem ofReal_blowupScale (s : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure s]
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hp : 0 < s (closedBall x |r|)) :
    ENNReal.ofReal (blowupScale s x r) = (s (closedBall x |r|))⁻¹ := by
  have ht := measure_ne_top s (closedBall x |r|)
  rw [blowupScale, measureReal_def, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hp.ne' ht),
    ENNReal.ofReal_toReal ht]

/--
Mass one of the normalized dilation under finiteness and positivity of the source ball mass. DPR pp.
7–9: singular normalization and limits along every admissible sequence.
-/
theorem positiveDilation_normalized_univ (s : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure s] (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0)
    (hp : 0 < s (closedBall x |r|)) :
    positiveDilation s x r hr (blowupScale s x r) univ = 1 := by
  rw [positiveDilation_univ, ofReal_blowupScale s x r hp,
    ENNReal.inv_mul_cancel hp.ne' (measure_ne_top _ _)]

/--
Differentiation of the polar transported through the Frobenius isometry, with singular
normalization. DPR pp. 7–9: singular normalization and limits along every admissible sequence.
-/
theorem ae_tendsto_matrixPolar_singular_error
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)) :
    ∀ᵐ x ∂M.variation.singularPart volume, Tendsto
      (fun r => (∫⁻ y in closedBall x r, ‖matrixPolarDensity M x - matrixPolarDensity M y‖ₑ
        ∂M.variation) / (M.variation.singularPart volume) (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := ae_tendsto_polar_singular_closedBall_error_enorm (matrixReindexed M) volume
  simpa only [matrixPolarDensity, ← map_sub, LinearIsometryEquiv.enorm_map,
    variation_matrixReindexed, enorm_sub_rev] using h

/--
Freezing along any admissible sequence; therefore stable under all later subsequences. DPR pp. 7–9:
singular normalization and limits along every admissible sequence.
-/
theorem frozenMatrixDefect_tendsto
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (x : EuclideanSpace ℝ (Fin d)) (rs : ℕ → ℝ) (hrs : ∀ n, 0 < rs n)
    (ht : Tendsto rs atTop (𝓝[>] (0 : ℝ)))
    (hp : ∀ n, 0 < (M.variation.singularPart volume) (closedBall x (rs n)))
    (he : Tendsto (fun r => (∫⁻ y in closedBall x r,
        ‖matrixPolarDensity M x - matrixPolarDensity M y‖ₑ ∂M.variation) /
        (M.variation.singularPart volume) (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (ha : Tendsto (fun r => (volume.withDensity (M.variation.rnDeriv volume)) (closedBall x r) /
        (M.variation.singularPart volume) (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun n =>
      ((positiveDilation (M.variation.singularPart volume) x (rs n) (hrs n).ne'
        (blowupScale (M.variation.singularPart volume) x (rs n))).withDensityᵥ
          (fun _ => matrixPolarDensity M x) -
        matrixDilation M x (rs n) (hrs n).ne'
          (blowupScale (M.variation.singularPart volume) x (rs n))).variation univ)
      atTop (𝓝 0) := by
  have hu := (he.comp ht).add
    (ENNReal.Tendsto.const_mul (a := ‖matrixPolarDensity M x‖ₑ) (ha.comp ht)
      (Or.inr enorm_ne_top))
  simp only [mul_zero, add_zero] at hu
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun _ => zero_le) (fun n => ?_)
  rw [frozenMatrixDefect_dilation M _ _ x (rs n) (hrs n).ne' (blowupScale_nonneg _ _ _),
    variation_matrixDilation_univ, abs_of_nonneg (blowupScale_nonneg _ _ _),
    ofReal_blowupScale _ _ _ (by simpa [abs_of_pos (hrs n)] using hp n),
    abs_of_pos (hrs n)]
  calc
    _ ≤ ((M.variation.singularPart volume) (closedBall x (rs n)))⁻¹ *
        ((∫⁻ y in closedBall x (rs n), ‖matrixPolarDensity M x - matrixPolarDensity M y‖ₑ
          ∂M.variation) + ‖matrixPolarDensity M x‖ₑ *
          (volume.withDensity (M.variation.rnDeriv volume)) (closedBall x (rs n))) :=
      mul_le_mul_right (frozenMatrixDefect_variation_le M _ _ measurableSet_closedBall) _
    _ = _ := by simp only [Function.comp_apply, div_eq_mul_inv]; ring

/--
A finite ratio becomes negligible after multiplying by the geometric radius. DPR pp. 7–9: singular
normalization and limits along every admissible sequence.
-/
theorem scaledMass_tendsto_zero
    (s β : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure s]
    (x : EuclideanSpace ℝ (Fin d)) (rs : ℕ → ℝ) (hrs : ∀ n, 0 < rs n)
    (ht : Tendsto rs atTop (𝓝[>] (0 : ℝ)))
    (hp : ∀ n, 0 < s (closedBall x (rs n))) {b : ℝ≥0∞} (hb : b ≠ ⊤)
    (hβ : Tendsto (fun r => β (closedBall x r) / s (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 b)) :
    Tendsto (fun n => ENNReal.ofReal |blowupScale s x (rs n) * rs n| *
      β (closedBall x (rs n))) atTop (𝓝 0) := by
  have hr0 := (tendsto_nhdsWithin_iff.mp ht).1
  have hh := ENNReal.Tendsto.mul (ENNReal.tendsto_ofReal hr0)
    (Or.inr hb) (hβ.comp ht) (Or.inr (by simp))
  simp only [ENNReal.ofReal_zero, zero_mul] at hh
  apply hh.congr'
  filter_upwards with n
  rw [abs_of_nonneg (mul_nonneg (blowupScale_nonneg _ _ _) (hrs n).le),
    ENNReal.ofReal_mul (blowupScale_nonneg _ _ _),
    ofReal_blowupScale s x (rs n) (by simpa [abs_of_pos (hrs n)] using hp n),
    abs_of_pos (hrs n)]
  simp only [Function.comp_apply, div_eq_mul_inv]
  ring

/--
Singularly normalized blow-up limits without an ellipticity or divergence hypothesis. DPR pp. 7–9:
singular normalization and limits along every admissible sequence.
-/
theorem ae_frozenMatrixDefect_tendsto
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)) :
    ∀ᵐ x ∂M.variation.singularPart volume,
      ∀ (rs : ℕ → ℝ) (hrs : ∀ n, 0 < rs n),
      Tendsto rs atTop (𝓝[>] (0 : ℝ)) →
      (∀ n, 0 < (M.variation.singularPart volume) (closedBall x (rs n))) →
      Tendsto (fun n =>
        ((positiveDilation (M.variation.singularPart volume) x (rs n) (hrs n).ne'
          (blowupScale (M.variation.singularPart volume) x (rs n))).withDensityᵥ
            (fun _ => matrixPolarDensity M x) -
          matrixDilation M x (rs n) (hrs n).ne'
            (blowupScale (M.variation.singularPart volume) x (rs n))).variation univ)
        atTop (𝓝 0) := by
  have ha := ae_tendsto_acPart_singular_closedBall_ratio (matrixReindexed M) volume
  simp only [variation_matrixReindexed] at ha
  filter_upwards [ae_tendsto_matrixPolar_singular_error M, ha] with x he hx
  exact fun rs hrs ht hp => frozenMatrixDefect_tendsto M x rs hrs ht hp he hx

/--
The normalized matrix mass tends to one if the quotient of variation by the normalizing measure
tends to one. DPR pp. 7–9: singular normalization and limits along every admissible sequence.
-/
theorem matrixDilation_mass_tendsto_one
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d))
    (s : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure s]
    (x : EuclideanSpace ℝ (Fin d)) (rs : ℕ → ℝ) (hrs : ∀ n, 0 < rs n)
    (ht : Tendsto rs atTop (𝓝[>] (0 : ℝ))) (hp : ∀ n, 0 < s (closedBall x (rs n)))
    (hratio : Tendsto (fun r => M.variation (closedBall x r) / s (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun n => (matrixDilation M x (rs n) (hrs n).ne'
      (blowupScale s x (rs n))).variation univ) atTop (𝓝 1) := by
  apply (hratio.comp ht).congr'
  filter_upwards with n
  rw [variation_matrixDilation_univ, abs_of_nonneg (blowupScale_nonneg _ _ _),
    ofReal_blowupScale _ _ _ (by simpa [abs_of_pos (hrs n)] using hp n), abs_of_pos (hrs n)]
  simp only [Function.comp_apply, div_eq_mul_inv, mul_comm]

end GeometricMeasure
