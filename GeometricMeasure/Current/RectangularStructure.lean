import GeometricMeasure.VectorMeasure.LinearImage
import GeometricMeasure.Current.MatrixStructure

/-!
# Rectangular Structure

## Main results
Rectangular matrix measures and their singular polar rank bound, globally and on open sets.

Source: De Philippis–Rindler (2016), cor. 1.13, pp. 5 and 15; rectangular extension by linear images
and maximal minors.
-/

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal

namespace GeometricMeasure

variable {X : Type*} [MeasurableSpace X]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/--
Full column rank of a real rectangular matrix yields an injective row selection with nonzero
determinant.
-/
theorem exists_injective_minor_of_rank_eq {r d : ℕ}
    (Q : Matrix (Fin r) (Fin d) ℝ) (hQ : Q.rank = d) :
    ∃ I : Fin d ↪ Fin r, (Q.submatrix I id).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ Q.row
  letI : Fintype κ := Fintype.ofInjective a ha
  have hc : Fintype.card κ = d := by
    rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row, hQ]
  let e : Fin d ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  let I : Fin d ↪ Fin r := ⟨a ∘ e, ha.comp e.injective⟩
  refine ⟨I, ?_⟩
  have hi : LinearIndependent ℝ (Q.submatrix I id).row := hli.comp e e.injective
  have hr : (Q.submatrix I id).rank = d := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hi, Fintype.card_fin]
  intro hz
  have hlt := (matrix_rank_lt_iff_det_eq_zero _).mpr hz
  omega

/--
A real rectangular matrix has rank below its number of columns exactly when every maximal row minor
vanishes, including in dimension zero.
-/
theorem rank_lt_iff_forall_minor_eq_zero {r d : ℕ} (Q : Matrix (Fin r) (Fin d) ℝ) :
    Q.rank < d ↔ ∀ I : Fin d ↪ Fin r, (Q.submatrix I id).det = 0 := by
  constructor
  · intro h I
    apply (matrix_rank_lt_iff_det_eq_zero _).mp
    exact lt_of_le_of_lt (Matrix.rank_submatrix_le Q I id) h
  · intro h
    have hle : Q.rank ≤ d := by simpa using Matrix.rank_le_card_width Q
    by_contra hnot
    have heq : Q.rank = d := by omega
    obtain ⟨I, hI⟩ := exists_injective_minor_of_rank_eq Q heq
    exact hI (h I)

/--
When the number of rows is smaller than the number of columns, rank is at most the number of columns
minus one, without any differential equation.
-/
theorem rank_le_sub_one_of_rows_lt {r d : ℕ} (Q : Matrix (Fin r) (Fin d) ℝ)
    (h : r < d) : Q.rank ≤ d - 1 := by
  have hr : Q.rank ≤ r := by simpa using Matrix.rank_le_card_height Q
  omega

/-- Rectangular values with the Euclidean, hence Frobenius, norm. -/
abbrev RectMatrixSpace (r d : ℕ) := EuclideanSpace ℝ (Fin r × Fin d)

/-- Ordinary matrix coordinates of a rectangular Euclidean value, with the row index first. -/
def RectMatrixSpace.coordinates {r d : ℕ} (P : RectMatrixSpace r d) : Matrix (Fin r) (Fin d) ℝ :=
  fun i j => P (i, j)

/-- Row selection as a continuous linear map from rectangular to square values. -/
def RectMatrixSpace.selectRows {r d : ℕ} (I : Fin d → Fin r) : RectMatrixSpace r d →L[ℝ] MatrixSpace d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun P => WithLp.toLp 2 (fun ij => P (I ij.1, ij.2))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- The entries of the selected square value are the corresponding rectangular entries. -/
@[simp] theorem RectMatrixSpace.selectRows_apply {r d : ℕ} (I : Fin d → Fin r)
    (P : RectMatrixSpace r d) (i j : Fin d) : RectMatrixSpace.selectRows I P (i, j) = P (I i, j) := rfl

/-- Extraction of one rectangular row as a continuous linear map. -/
def RectMatrixSpace.row {r d : ℕ} (i : Fin r) : RectMatrixSpace r d →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun P => WithLp.toLp 2 (fun j => P (i, j))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- The vector measure associated with one rectangular row. -/
def VectorMeasure.rectRow {r d : ℕ} (M : VectorMeasure X (RectMatrixSpace r d)) (i : Fin r) :=
  VectorMeasure.linearImage (RectMatrixSpace.row i) M

/-- Row selection commutes with taking row measures. -/
theorem VectorMeasure.rowMeasure_linearImage_selectRows {r d : ℕ} (M : VectorMeasure X (RectMatrixSpace r d))
    (I : Fin d → Fin r) (i : Fin d) :
    rowMeasure (VectorMeasure.linearImage (RectMatrixSpace.selectRows I) M) i = VectorMeasure.rectRow M (I i) := by
  apply VectorMeasure.ext
  intro s hs
  rfl

/-- Global rectangular divergence given by the existing measure divergence equation on each row. -/
def HasRectMeasureDivergence {r d : ℕ}
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (RectMatrixSpace r d))
    (D : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ i, HasMeasureDivergence (VectorMeasure.rectRow M i) (D i)

/--
Rectangular divergence given by the existing row equations tested only on supports contained in the
specified set.
-/
def HasRectMeasureDivergenceOn {r d : ℕ}
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (RectMatrixSpace r d))
    (D : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (U : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ i, HasMeasureDivergenceOn (VectorMeasure.rectRow M i) (D i) U

/-- Row selection commutes with global measure divergence, without injectivity of the selection. -/
theorem HasRectMeasureDivergence.selectRows {r d : ℕ}
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (RectMatrixSpace r d))
    (D : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hdiv : HasRectMeasureDivergence M D) (I : Fin d → Fin r) :
    HasMatrixMeasureDivergence (VectorMeasure.linearImage (RectMatrixSpace.selectRows I) M) (D ∘ I) := by
  intro i
  simpa only [VectorMeasure.rowMeasure_linearImage_selectRows, Function.comp_apply] using hdiv (I i)

/--
Row selection commutes with measure divergence tested on a set, without injectivity or openness
assumptions.
-/
theorem HasRectMeasureDivergenceOn.selectRows {r d : ℕ}
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (RectMatrixSpace r d))
    (D : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (U : Set (EuclideanSpace ℝ (Fin d)))
    (hdiv : HasRectMeasureDivergenceOn M D U) (I : Fin d → Fin r) :
    HasMatrixMeasureDivergenceOn (VectorMeasure.linearImage (RectMatrixSpace.selectRows I) M) (D ∘ I) U := by
  intro i
  simpa only [VectorMeasure.rowMeasure_linearImage_selectRows, Function.comp_apply] using hdiv (I i)

/--
The chosen square polar agrees with the existing matrix polar almost everywhere for the variation.
-/
theorem VectorMeasure.polar_ae_eq_matrixPolarDensity {d : ℕ} (M : VectorMeasure X (MatrixSpace d)) :
    VectorMeasure.polar M =ᵐ[M.variation] matrixPolarDensity M :=
  VectorMeasure.polar_ae_eq_of_withDensity_eq M (integrable_matrixPolarDensity M) (withDensityᵥ_matrixPolarDensity M)

/--
In positive dimension, the zero determinant set contains zero and is stable under positive real
scaling.
-/
theorem MatrixSpace.zero_mem_and_smul_mem_det_zero {d : ℕ} [NeZero d] :
    (0 : MatrixSpace d) ∈ {P | (matrixCoordinates P).det = 0} ∧
    ∀ a : ℝ, 0 < a → ∀ P ∈ {P : MatrixSpace d | (matrixCoordinates P).det = 0},
      a • P ∈ {P | (matrixCoordinates P).det = 0} := by
  constructor
  · change (0 : Matrix (Fin d) (Fin d) ℝ).det = 0
    exact Matrix.det_zero
  · intro a ha P hP
    change (a • matrixCoordinates P).det = 0
    rw [Matrix.det_smul, hP, mul_zero]

/--
For finite rectangular measures satisfying the row divergence equation on an open set in positive
spatial dimension, each injectively selected maximal polar minor vanishes there almost
everywhere for the singular variation relative to volume.

Source: De Philippis–Rindler (2016), cor. 1.13, pp. 5 and 15; rectangular extension by linear images
and maximal minors.
-/
theorem HasRectMeasureDivergenceOn.ae_det_polar_minor_eq_zero {r d : ℕ} [NeZero d]
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (RectMatrixSpace r d))
    (D : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hdiv : HasRectMeasureDivergenceOn M D U) (I : Fin d ↪ Fin r) :
    ∀ᵐ x ∂M.variation.singularPart volume, x ∈ U →
      ((RectMatrixSpace.coordinates (VectorMeasure.polar M x)).submatrix I id).det = 0 := by
  let N := VectorMeasure.linearImage (RectMatrixSpace.selectRows I) M
  have hs := ae_det_matrixPolar_eq_zero_of_on N (D ∘ I) hU
    (HasRectMeasureDivergenceOn.selectRows M D U hdiv I)
  have hp := (Measure.absolutelyContinuous_of_le (N.variation.singularPart_le volume)).ae_le
    (VectorMeasure.polar_ae_eq_matrixPolarDensity N)
  have hN : ∀ᵐ x ∂N.variation.singularPart volume, x ∈ U →
      VectorMeasure.polar N x ∈ {P : MatrixSpace d | (matrixCoordinates P).det = 0} := by
    filter_upwards [hs, hp] with x hx he hxU
    rw [he]
    exact hx hxU
  exact VectorMeasure.ae_apply_polar_mem_of_polar_linearImage_mem_on (RectMatrixSpace.selectRows I) M volume _ MatrixSpace.zero_mem_and_smul_mem_det_zero.1
    MatrixSpace.zero_mem_and_smul_mem_det_zero.2 U hN

/--
For a finite rectangular measure whose row divergence is a family of finite signed measures on
an open set, the polar rank is at most the spatial dimension minus one almost everywhere for the
singular variation restricted to that set, relative to volume.

Source: De Philippis–Rindler (2016), cor. 1.13, pp. 5 and 15; rectangular extension by linear images
and maximal minors.
-/
theorem HasRectMeasureDivergenceOn.ae_rank_polar_le {r d : ℕ}
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (RectMatrixSpace r d))
    (D : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hdiv : HasRectMeasureDivergenceOn M D U) :
    ∀ᵐ x ∂(M.variation.singularPart volume).restrict U,
      (RectMatrixSpace.coordinates (VectorMeasure.polar M x)).rank ≤ d - 1 := by
  by_cases hd : d = 0
  · subst d
    filter_upwards with x
    simpa using Matrix.rank_le_card_width (RectMatrixSpace.coordinates (VectorMeasure.polar M x))
  by_cases hr : r < d
  · filter_upwards with x using rank_le_sub_one_of_rows_lt _ hr
  haveI : NeZero d := ⟨hd⟩
  have hall : ∀ᵐ x ∂M.variation.singularPart volume, ∀ I : Fin d ↪ Fin r,
      x ∈ U → ((RectMatrixSpace.coordinates (VectorMeasure.polar M x)).submatrix I id).det = 0 :=
    ae_all_iff.mpr (fun I => HasRectMeasureDivergenceOn.ae_det_polar_minor_eq_zero M D hU hdiv I)
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [hall] with x hx hxU
  have hlt := (rank_lt_iff_forall_minor_eq_zero (RectMatrixSpace.coordinates (VectorMeasure.polar M x))).mpr (fun I => hx I hxU)
  omega

/--
For a finite rectangular measure whose global row divergence is a family of finite signed measures,
the polar rank is at most the spatial dimension minus one almost everywhere for the singular
variation relative to volume.

Source: De Philippis–Rindler (2016), cor. 1.13, pp. 5 and 15; rectangular extension by linear images
and maximal minors.
-/
theorem HasRectMeasureDivergence.ae_rank_polar_le {r d : ℕ}
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (RectMatrixSpace r d))
    (D : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hdiv : HasRectMeasureDivergence M D) :
    ∀ᵐ x ∂M.variation.singularPart volume,
      (RectMatrixSpace.coordinates (VectorMeasure.polar M x)).rank ≤ d - 1 := by
  have hlocal : HasRectMeasureDivergenceOn M D univ := by
    intro i φ hφ
    exact hdiv i φ
  simpa using HasRectMeasureDivergenceOn.ae_rank_polar_le M D isOpen_univ hlocal

/-- The zero determinant set in the Euclidean matrix space is measurable. -/
theorem MatrixSpace.measurableSet_det_zero {d : ℕ} :
    MeasurableSet {P : MatrixSpace d | (matrixCoordinates P).det = 0} := by
  apply isClosed_eq _ continuous_const |>.measurableSet
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d × Fin d => ℝ) (i, j)).continuous

end GeometricMeasure
