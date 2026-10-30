import GeometricMeasure.VectorMeasure.Lebesgue

/-!
# Matrix-valued measures with the Frobenius norm

## Main results
A linear isometry identifies matrix-valued measures with Euclidean vector measures while retaining
the matrix index type. Their rows, variation and polar representations are transported through this
identification.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace GeometricMeasure

variable {X : Type*} [MeasurableSpace X]

section LinearMaps

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem variation_mapRange_linearIsometryEquiv (N : VectorMeasure X E) (L : E ≃ₗᵢ[ℝ] F) :
    (N.mapRange L.toLinearEquiv.toLinearMap.toAddMonoidHom L.continuous).variation =
      N.variation := by
  unfold VectorMeasure.variation
  congr 1
  funext s
  exact L.enorm_map (N s)

theorem withDensityᵥ_mapRange [CompleteSpace E] [CompleteSpace F]
    (ν : Measure X) {f : X → E} (hf : Integrable f ν) (L : E →L[ℝ] F) :
    (ν.withDensityᵥ f).mapRange L.toLinearMap.toAddMonoidHom L.continuous =
      ν.withDensityᵥ (fun x => L (f x)) := by
  apply VectorMeasure.ext
  intro s hs
  rw [VectorMeasure.mapRange_apply, withDensityᵥ_apply hf hs,
    withDensityᵥ_apply (L.integrable_comp hf) hs]
  exact (L.integral_comp_comm hf.restrict).symm

end LinearMaps

abbrev MatrixSpace (d : ℕ) := EuclideanSpace ℝ (Fin d × Fin d)

def matrixReindex (d : ℕ) :
    MatrixSpace d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d * d)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finProdFinEquiv

def matrixReindexed {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    VectorMeasure X (EuclideanSpace ℝ (Fin (d * d))) :=
  N.mapRange (matrixReindex d).toLinearEquiv.toLinearMap.toAddMonoidHom
    (matrixReindex d).continuous

@[simp] theorem matrixReindexed_apply {d : ℕ} (N : VectorMeasure X (MatrixSpace d))
    (s : Set X) : matrixReindexed N s = matrixReindex d (N s) := rfl

theorem variation_matrixReindexed {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    (matrixReindexed N).variation = N.variation :=
  variation_mapRange_linearIsometryEquiv N (matrixReindex d)

instance isFiniteMeasure_variation_matrix {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    IsFiniteMeasure N.variation := by
  rw [← variation_matrixReindexed N]
  infer_instance

def matrixPolarDensity {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) : X → MatrixSpace d :=
  fun x => (matrixReindex d).symm (polarDensity (matrixReindexed N) x)

theorem measurable_matrixPolarDensity {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    Measurable (matrixPolarDensity N) :=
  (matrixReindex d).symm.continuous.measurable.comp (measurable_polarDensity _)

theorem integrable_matrixPolarDensity {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    Integrable (matrixPolarDensity N) N.variation := by
  rw [← variation_matrixReindexed N]
  exact (matrixReindex d).symm.toLinearIsometry.toContinuousLinearMap.integrable_comp (integrable_polarDensity _)

theorem withDensityᵥ_matrixPolarDensity {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    N.variation.withDensityᵥ (matrixPolarDensity N) = N := by
  apply VectorMeasure.ext
  intro s hs
  rw [withDensityᵥ_apply (integrable_matrixPolarDensity N) hs]
  change (∫ x in s, (matrixReindex d).symm.toLinearIsometry.toContinuousLinearMap
    (polarDensity (matrixReindexed N) x)
    ∂N.variation) = N s
  rw [← variation_matrixReindexed N,
    (matrixReindex d).symm.toLinearIsometry.toContinuousLinearMap.integral_comp_comm
      (integrable_polarDensity (matrixReindexed N)).restrict]
  have h := congrArg (fun v : VectorMeasure X (EuclideanSpace ℝ (Fin (d * d))) => v s)
    (withDensityᵥ_polarDensity (matrixReindexed N))
  rw [withDensityᵥ_apply (integrable_polarDensity _) hs] at h
  rw [h]
  exact (matrixReindex d).symm_apply_apply (N s)

theorem norm_matrixPolarDensity_ae {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    ∀ᵐ x ∂N.variation, ‖matrixPolarDensity N x‖ = 1 := by
  rw [← variation_matrixReindexed N]
  simpa only [matrixPolarDensity, LinearIsometryEquiv.norm_map] using
    norm_polarDensity_ae (matrixReindexed N)

/-- Isometric currying of a Frobenius matrix into its Euclidean rows. -/
def matrixRows (d : ℕ) :
    MatrixSpace d ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin d => EuclideanSpace ℝ (Fin d)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.sigmaEquivProd (Fin d) (Fin d)).symm).trans
    (LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : Fin d) (_ : Fin d) => ℝ))

def rowCLM {d : ℕ} (i : Fin d) : MatrixSpace d →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => EuclideanSpace ℝ (Fin d)) i).comp
    (matrixRows d).toLinearIsometry.toContinuousLinearMap

@[simp] theorem rowCLM_apply {d : ℕ} (i j : Fin d) (P : MatrixSpace d) :
    rowCLM i P j = P (i, j) := rfl

theorem norm_rowCLM_le {d : ℕ} (i : Fin d) (P : MatrixSpace d) : ‖rowCLM i P‖ ≤ ‖P‖ := by
  change ‖(matrixRows d P) i‖ ≤ ‖P‖
  simpa only [LinearIsometryEquiv.norm_map] using PiLp.norm_apply_le (matrixRows d P) i

theorem matrix_norm_sq_eq_sum_rows {d : ℕ} (P : MatrixSpace d) :
    ‖P‖ ^ 2 = ∑ i : Fin d, ‖rowCLM i P‖ ^ 2 := by
  rw [← (matrixRows d).norm_map P, PiLp.norm_sq_eq_of_L2]
  rfl

theorem matrix_norm_le_sum_rows {d : ℕ} (P : MatrixSpace d) :
    ‖P‖ ≤ ∑ i : Fin d, ‖rowCLM i P‖ := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i : Fin d => ‖rowCLM i P‖) (fun i _ => norm_nonneg _)
  rw [← matrix_norm_sq_eq_sum_rows] at h
  have hn : 0 ≤ ∑ i : Fin d, ‖rowCLM i P‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  nlinarith [norm_nonneg P]

def rowMeasure {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) (i : Fin d) :
    VectorMeasure X (EuclideanSpace ℝ (Fin d)) :=
  N.mapRange (rowCLM i).toLinearMap.toAddMonoidHom (rowCLM i).continuous

@[simp] theorem rowMeasure_apply {d : ℕ} (N : VectorMeasure X (MatrixSpace d))
    (i : Fin d) (s : Set X) : rowMeasure N i s = rowCLM i (N s) := rfl

theorem rowMeasure_eq_withDensityᵥ {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) (i : Fin d) :
    rowMeasure N i = N.variation.withDensityᵥ (fun x => rowCLM i (matrixPolarDensity N x)) := by
  unfold rowMeasure
  conv_lhs => rw [← withDensityᵥ_matrixPolarDensity N]
  exact withDensityᵥ_mapRange _ (integrable_matrixPolarDensity N) (rowCLM i)

theorem variation_rowMeasure {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) (i : Fin d) :
    (rowMeasure N i).variation =
      N.variation.withDensity (fun x => ‖rowCLM i (matrixPolarDensity N x)‖ₑ) := by
  rw [rowMeasure_eq_withDensityᵥ]
  exact Measure.variation_withDensityᵥ
    ((rowCLM i).integrable_comp (integrable_matrixPolarDensity N))

theorem variation_rowMeasure_le {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) (i : Fin d) :
    (rowMeasure N i).variation ≤ N.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro s _
  calc
    ‖rowMeasure N i s‖ₑ ≤ ‖N s‖ₑ := by
      simpa only [rowMeasure_apply, ← ofReal_norm] using ENNReal.ofReal_le_ofReal
        (norm_rowCLM_le i (N s))
    _ ≤ N.variation s := VectorMeasure.enorm_measure_le_variation N s

theorem variation_le_sum_rowMeasure {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    N.variation ≤ ∑ i : Fin d, (rowMeasure N i).variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro s hs
  calc
    ‖N s‖ₑ ≤ ∑ i : Fin d, ‖rowMeasure N i s‖ₑ := by
      simpa only [rowMeasure_apply, ← ofReal_norm,
        ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)] using
          ENNReal.ofReal_le_ofReal (matrix_norm_le_sum_rows (N s))
    _ ≤ ∑ i : Fin d, (rowMeasure N i).variation s :=
      Finset.sum_le_sum (fun i _ => VectorMeasure.enorm_measure_le_variation _ s)
    _ = (∑ i : Fin d, (rowMeasure N i).variation) s := by simp

theorem sum_rowMeasure_le {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    (∑ i : Fin d, (rowMeasure N i).variation) ≤ d • N.variation := by
  calc
    (∑ i : Fin d, (rowMeasure N i).variation) ≤ ∑ _i : Fin d, N.variation :=
      Finset.sum_le_sum (fun i _ => variation_rowMeasure_le N i)
    _ = d • N.variation := by simp


/-- Frobenius norm in ordinary matrix coordinates. -/
theorem matrix_norm_sq_eq_sum_entries {d : ℕ} (P : MatrixSpace d) :
    ‖P‖ ^ 2 = ∑ i : Fin d, ∑ j : Fin d, P (i, j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]

theorem eq_zero_of_matrix_dimension_zero (N : VectorMeasure X (MatrixSpace 0)) :
    N = 0 := by
  apply VectorMeasure.ext
  intro s _
  exact Subsingleton.elim _ _

@[simp] theorem matrixPolarDensity_dimension_zero (N : VectorMeasure X (MatrixSpace 0)) :
    matrixPolarDensity N = 0 := Subsingleton.elim _ _

theorem matrixPolarDensity_zero_ae {d : ℕ} :
    matrixPolarDensity (0 : VectorMeasure X (MatrixSpace d)) =ᵐ[
      (0 : VectorMeasure X (MatrixSpace d)).variation] 0 := by
  simp
  exact Filter.eventually_bot

/-- Cauchy–Schwarz sharpens the sum of row norms. -/
theorem matrix_sum_norm_rows_le_sqrt {d : ℕ} (P : MatrixSpace d) :
    (∑ i : Fin d, ‖rowCLM i P‖) ≤ Real.sqrt d * ‖P‖ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin d => (1 : ℝ)) (fun i : Fin d => ‖rowCLM i P‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, ← matrix_norm_sq_eq_sum_rows] at h
  have hsq : (∑ i : Fin d, ‖rowCLM i P‖) ^ 2 ≤ (Real.sqrt d * ‖P‖) ^ 2 := by
    rwa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  have hn : 0 ≤ Real.sqrt d * ‖P‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith

theorem sum_rowMeasure_le_sqrt {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    (∑ i : Fin d, (rowMeasure N i).variation) ≤ ENNReal.ofReal (Real.sqrt d) • N.variation := by
  have hsum : (∑ i : Fin d, (rowMeasure N i).variation) =
      N.variation.withDensity (fun x => ∑ i : Fin d, ‖rowCLM i (matrixPolarDensity N x)‖ₑ) := by
    simp_rw [variation_rowMeasure]
    have h := (withDensity_tsum (μ := N.variation)
        (fun i : Fin d => ((rowCLM i).continuous.measurable.comp
          (measurable_matrixPolarDensity N)).enorm)).symm
    simp only [Measure.sum_fintype, tsum_fintype, Function.comp_apply] at h
    rw [h]
    congr 1
    funext x
    simp only [Finset.sum_apply]
  rw [hsum, ← withDensity_const]
  apply withDensity_mono
  filter_upwards [norm_matrixPolarDensity_ae N] with x hx
  have h := matrix_sum_norm_rows_le_sqrt (matrixPolarDensity N x)
  rw [hx, mul_one] at h
  simpa only [← ofReal_norm, ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)] using
    ENNReal.ofReal_le_ofReal h

/-- Insert a vector as one row and set all other rows to zero. -/
def rowInsertCLM {d : ℕ} (i : Fin d) : EuclideanSpace ℝ (Fin d) →L[ℝ] MatrixSpace d :=
  (matrixRows d).symm.toLinearIsometry.toContinuousLinearMap.comp
    (((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin d => EuclideanSpace ℝ (Fin d))).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin d => EuclideanSpace ℝ (Fin d)) i))

@[simp] theorem rowCLM_rowInsertCLM {d : ℕ} (i j : Fin d)
    (v : EuclideanSpace ℝ (Fin d)) : rowCLM i (rowInsertCLM j v) = if i = j then v else 0 := by
  change (Pi.single j v : Fin d → EuclideanSpace ℝ (Fin d)) i = _
  by_cases h : i = j
  · subst i; simp
  · simp [h]

/-- Finite sums of row insertions give the inverse to taking rows. -/
def stackRows {d : ℕ} (R : Fin d → VectorMeasure X (EuclideanSpace ℝ (Fin d))) :
    VectorMeasure X (MatrixSpace d) :=
  ∑ i : Fin d, (R i).mapRange (rowInsertCLM i).toLinearMap.toAddMonoidHom
    (rowInsertCLM i).continuous

@[simp] theorem stackRows_apply {d : ℕ}
    (R : Fin d → VectorMeasure X (EuclideanSpace ℝ (Fin d))) (s : Set X) :
    stackRows R s = ∑ i : Fin d, rowInsertCLM i (R i s) := by
  simp [stackRows]

@[simp] theorem rowMeasure_stackRows {d : ℕ}
    (R : Fin d → VectorMeasure X (EuclideanSpace ℝ (Fin d))) (i : Fin d) :
    rowMeasure (stackRows R) i = R i := by
  apply VectorMeasure.ext
  intro s _
  simp [rowMeasure_apply, stackRows_apply, map_sum, rowCLM_rowInsertCLM]

theorem ext_of_rowMeasure_eq {d : ℕ} {N N' : VectorMeasure X (MatrixSpace d)}
    (h : ∀ i : Fin d, rowMeasure N i = rowMeasure N' i) : N = N' := by
  apply VectorMeasure.ext
  intro s _
  ext ij
  have hi := congrArg (fun R : VectorMeasure X (EuclideanSpace ℝ (Fin d)) => R s ij.2) (h ij.1)
  simpa only [rowMeasure_apply, rowCLM_apply] using hi

@[simp] theorem stackRows_rowMeasure {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) :
    stackRows (rowMeasure N) = N := by
  apply ext_of_rowMeasure_eq
  intro i
  exact rowMeasure_stackRows _ i

theorem polarDensity_rowMeasure {d : ℕ} (N : VectorMeasure X (MatrixSpace d)) (i : Fin d) :
    polarDensity (rowMeasure N i) =ᵐ[(rowMeasure N i).variation]
      (fun x => ‖rowCLM i (matrixPolarDensity N x)‖⁻¹ • rowCLM i (matrixPolarDensity N x)) := by
  simpa only [rowMeasure_eq_withDensityᵥ] using
    polar_eq_normalize N.variation ((rowCLM i).integrable_comp (integrable_matrixPolarDensity N))

end GeometricMeasure
