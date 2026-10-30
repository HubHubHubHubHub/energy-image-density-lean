import GeometricMeasure.Current.RectangularStructure
import GeometricMeasure.Current.NormalFamily
import GeometricMeasure.Current.CoordinateNormalFamily

/-!
# First Order Structure

## Main results
First order constant coefficient equations for finite vector measures.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Corollaries 1.12 and 1.13. The
equations use globally finite measures; local conclusions use interior tests.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace GeometricMeasure

/-- A real rectangular matrix loses column rank exactly when its kernel is nontrivial. -/
theorem rank_lt_iff_exists_mulVec_eq_zero {r d : ℕ} (Q : Matrix (Fin r) (Fin d) ℝ) :
    Q.rank < d ↔ ∃ ξ : Fin d → ℝ, ξ ≠ 0 ∧ Q.mulVec ξ = 0 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  constructor
  · intro h
    have hk : LinearMap.ker Q.mulVecLin ≠ ⊥ := by
      intro hz
      rw [hz, finrank_bot] at hrn
      unfold Matrix.rank at h
      omega
    obtain ⟨ξ, hξ, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
    exact ⟨ξ, hn, hξ⟩
  · rintro ⟨ξ, hn, hξ⟩
    have hk : LinearMap.ker Q.mulVecLin ≠ ⊥ := by
      intro hz
      have hm : ξ ∈ LinearMap.ker Q.mulVecLin := hξ
      rw [hz] at hm
      exact hn hm
    have hp : 0 < Module.finrank ℝ (LinearMap.ker Q.mulVecLin) := by
      rw [Nat.pos_iff_ne_zero]
      exact fun h => hk (Submodule.finrank_eq_zero.mp h)
    unfold Matrix.rank
    omega

/-- Constant real coefficients of an operator of order at most one. -/
structure FirstOrderOperator (d m r : ℕ) where
  principal : Fin d → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin r)
  lower : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin r)

namespace FirstOrderOperator
variable {d m r : ℕ} (A : FirstOrderOperator d m r)

/-- The rectangular value map with spatial derivatives indexing columns. -/
def matrix : EuclideanSpace ℝ (Fin m) →L[ℝ] RectMatrixSpace r d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun ij => A.principal ij.2 v ij.1)
      map_add' := by intros; ext ij; simp
      map_smul' := by intros; ext ij; simp }

/-- An entry of the rectangular value map is the corresponding principal coefficient. -/
@[simp] theorem matrix_apply (v : EuclideanSpace ℝ (Fin m)) (a : Fin r) (j : Fin d) :
    A.matrix v (a, j) = A.principal j v a := rfl

/-- The real principal symbol; the common nonzero Fourier factor does not affect its kernel. -/
def symbol (ξ : EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin r) := ∑ j, ξ j • A.principal j v

/-- The wave cone is expressed by a nonzero real frequency. -/
def waveCone : Set (EuclideanSpace ℝ (Fin m)) :=
  {v | ∃ ξ : EuclideanSpace ℝ (Fin d), ξ ≠ 0 ∧ A.symbol ξ v = 0}

/-- Matrix multiplication gives the principal symbol in ordinary coordinates. -/
theorem matrix_mulVec (ξ : EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin m)) :
    (RectMatrixSpace.coordinates (A.matrix v)).mulVec (WithLp.ofLp ξ) =
      WithLp.ofLp (A.symbol ξ v) := by
  ext a
  simp [Matrix.mulVec, dotProduct, RectMatrixSpace.coordinates, symbol, mul_comm]

/-- The rank description of the wave cone, including the empty spatial dimension. -/
theorem mem_waveCone_iff_rank_lt (v : EuclideanSpace ℝ (Fin m)) :
    v ∈ A.waveCone ↔ (RectMatrixSpace.coordinates (A.matrix v)).rank < d := by
  rw [rank_lt_iff_exists_mulVec_eq_zero]
  constructor
  · rintro ⟨ξ, hn, hξ⟩
    refine ⟨WithLp.ofLp ξ, ?_, ?_⟩
    · intro h; apply hn; exact congrArg (WithLp.toLp 2) h
    · rw [A.matrix_mulVec, hξ]; rfl
  · rintro ⟨ξ, hn, hξ⟩
    refine ⟨WithLp.toLp 2 ξ, ?_, ?_⟩
    · intro h; exact hn (congrArg WithLp.ofLp h)
    · exact congrArg (WithLp.toLp 2) ((A.matrix_mulVec (WithLp.toLp 2 ξ) v).symm.trans hξ)

/-- Nonzero frequencies may equivalently be normalized to the unit sphere. -/
theorem mem_waveCone_iff_exists_unit (v : EuclideanSpace ℝ (Fin m)) :
    v ∈ A.waveCone ↔ ∃ ξ : EuclideanSpace ℝ (Fin d), ‖ξ‖ = 1 ∧ A.symbol ξ v = 0 := by
  constructor
  · rintro ⟨ξ, hn, hz⟩
    refine ⟨‖ξ‖⁻¹ • ξ, ?_, ?_⟩
    · simp [norm_smul, norm_ne_zero_iff.mpr hn]
    · have he : A.symbol (‖ξ‖⁻¹ • ξ) v = ‖ξ‖⁻¹ • A.symbol ξ v := by
        simp [symbol, Finset.smul_sum, smul_smul]
      rw [he, hz, smul_zero]
  · rintro ⟨ξ, hn, hz⟩
    exact ⟨ξ, fun h => by simp [h] at hn, hz⟩

end FirstOrderOperator

/-- The general polar and the coordinate polar represent the same almost everywhere class. -/
theorem VectorMeasure.polar_ae_eq_polarDensity {X : Type*} [MeasurableSpace X] {m : ℕ}
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    VectorMeasure.polar M =ᵐ[M.variation] polarDensity M :=
  VectorMeasure.polar_ae_eq_of_withDensity_eq M (integrable_polarDensity M)
    (withDensityᵥ_polarDensity M)

/-- A linear image may be represented using the existing coordinate polar. -/
theorem VectorMeasure.linearImage_eq_withDensity_polarDensity
    {X F : Type*} [MeasurableSpace X] {m : ℕ}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] F)
    (M : VectorMeasure X (EuclideanSpace ℝ (Fin m))) :
    VectorMeasure.linearImage L M = M.variation.withDensityᵥ (fun x => L (polarDensity M x)) := by
  unfold VectorMeasure.linearImage
  conv_lhs => rw [← withDensityᵥ_polarDensity M]
  exact withDensityᵥ_mapRange _ (integrable_polarDensity M) L

/-- Expansion of a Euclidean covector on the standard coordinate vectors. -/
theorem sum_apply_euclideanSingle_mul {d : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    ∑ j, L (WithLp.toLp 2 (Pi.single j (1 : ℝ))) * v j = L v :=
  sum_apply_single_mul
    (L.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap)
    (WithLp.ofLp v)

namespace FirstOrderOperator
variable {d m r : ℕ} (A : FirstOrderOperator d m r)
variable (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))

/-- The scalar zeroth order coefficient in one target coordinate. -/
def lowerCoord (a : Fin r) : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin r => ℝ) a).comp A.lower

/-- Extracting a row of the rectangular image equals the image by the composed row map. -/
theorem rectRow_linearImage_matrix (a : Fin r) :
    VectorMeasure.rectRow (VectorMeasure.linearImage A.matrix M) a =
      VectorMeasure.linearImage ((RectMatrixSpace.row a).comp A.matrix) M := by
  apply MeasureTheory.VectorMeasure.ext
  intro s hs
  rfl

/-- The zeroth order measure is precisely a coordinate of the value image by the lower term. -/
theorem linearImage_lowerCoord (a : Fin r) :
    VectorMeasure.linearImage (A.lowerCoord a) M = coord (VectorMeasure.linearImage A.lower M) a := by
  apply MeasureTheory.VectorMeasure.ext
  intro s hs
  rfl

/-- Testing the lower order image gives the zeroth order integral in the equation. -/
theorem signedTestCurrent_lowerCoord (a : Fin r) (φ : ScalarCurrentTest d) :
    signedTestCurrent (VectorMeasure.linearImage (A.lowerCoord a) M) φ =
      ∫ x, φ x * A.lower (polarDensity M x) a ∂M.variation := by
  rw [VectorMeasure.linearImage_eq_withDensity_polarDensity,
    ← signedMeasurePairing_currentTest, signedMeasurePairing_density _ _
      ((A.lowerCoord a).integrable_comp (integrable_polarDensity M))]
  rfl

/-- Each principal derivative-coordinate integrand is integrable. -/
theorem integrable_principal_test (a : Fin r) (j : Fin d) (φ : ScalarCurrentTest d) :
    Integrable (fun x => fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x
      (WithLp.toLp 2 (Pi.single j (1 : ℝ))) * A.principal j (polarDensity M x) a)
      M.variation := by
  let L := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin r => ℝ) a).comp (A.principal j)
  let e : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Pi.single j 1)
  let ω : BoundedCovectorField d d := currentTestDerivative φ
  have hi : Integrable (fun x => ω x e * L (polarDensity M x)) M.variation := by
    apply (L.integrable_comp (integrable_polarDensity M)).bdd_mul
      (ω.continuous.clm_apply continuous_const).aestronglyMeasurable
    filter_upwards with x
    exact ((ω x).le_opNorm e).trans
      (mul_le_mul_of_nonneg_right (ω.norm_coe_le_norm x) (norm_nonneg e))
  have heq : (fun x => ω x e * L (polarDensity M x)) =
      (fun x => fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x
        (WithLp.toLp 2 (Pi.single j (1 : ℝ))) * A.principal j (polarDensity M x) a) := by
    funext x
    change (currentTestDerivative φ) x e * _ = _
    rw [currentTestDerivative_apply]
    rfl
  exact heq ▸ hi

/-- The boundary of one rectangular row is the sum of the principal derivative integrals. -/
theorem boundary_rectRow_linearImage_matrix (a : Fin r) (φ : ScalarCurrentTest d) :
    oneCurrentBoundary
      (measureOneCurrent (VectorMeasure.rectRow (VectorMeasure.linearImage A.matrix M) a)) φ =
      ∑ j, ∫ x, fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x
        (WithLp.toLp 2 (Pi.single j (1 : ℝ))) * A.principal j (polarDensity M x) a
        ∂M.variation := by
  rw [rectRow_linearImage_matrix, oneCurrentBoundary_apply,
    ← vectorMeasurePairing_currentTest, VectorMeasure.linearImage_eq_withDensity_polarDensity,
    vectorMeasurePairing_withDensityᵥ _
      (((RectMatrixSpace.row a).comp A.matrix).integrable_comp (integrable_polarDensity M))]
  change (∫ x, fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x
    ((RectMatrixSpace.row a) (A.matrix (polarDensity M x))) ∂M.variation) = _
  calc
    _ = ∫ x, ∑ j, fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x
        (WithLp.toLp 2 (Pi.single j (1 : ℝ))) * A.principal j (polarDensity M x) a
        ∂M.variation := by
      apply integral_congr_ae
      filter_upwards with x
      exact (sum_apply_euclideanSingle_mul _ _).symm
    _ = _ := integral_finsetSum _ (fun j _ => A.integrable_principal_test M a j φ)

/-- The first order distributional equation, tested only inside the specified set. -/
def HasEquationOn (σ : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (U : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ a (φ : ScalarCurrentTest d), tsupport (φ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ U →
    (∫ x, φ x * A.lower (polarDensity M x) a ∂M.variation) -
      (∑ j, ∫ x, fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x
        (WithLp.toLp 2 (Pi.single j (1 : ℝ))) * A.principal j (polarDensity M x) a
        ∂M.variation) = signedTestCurrent (σ a) φ

/-- The global distributional equation includes the lower term and a finite measure source. -/
def HasEquation (σ : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d))) : Prop :=
  A.HasEquationOn M σ univ

/-- Moving the lower order measure to the right gives exactly the rectangular divergence. -/
theorem hasEquationOn_iff_hasRectMeasureDivergenceOn
    (σ : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (U : Set (EuclideanSpace ℝ (Fin d))) :
    A.HasEquationOn M σ U ↔
      HasRectMeasureDivergenceOn (VectorMeasure.linearImage A.matrix M)
        (fun a => σ a - coord (VectorMeasure.linearImage A.lower M) a) U := by
  have htest (a : Fin r) (φ : ScalarCurrentTest d) :
      signedTestCurrent (σ a - coord (VectorMeasure.linearImage A.lower M) a) φ =
      signedTestCurrent (σ a) φ - ∫ x, φ x * A.lower (polarDensity M x) a ∂M.variation := by
    rw [← A.linearImage_lowerCoord M, sub_eq_add_neg, signedTestCurrent_add,
      signedTestCurrent_neg, add_apply, neg_apply, A.signedTestCurrent_lowerCoord M]
    rfl
  constructor
  · intro h a φ hφ
    rw [htest, A.boundary_rectRow_linearImage_matrix M]
    linarith [h a φ hφ]
  · intro h a φ hφ
    have hh := h a φ hφ
    rw [htest, A.boundary_rectRow_linearImage_matrix M] at hh
    linarith

/-- Rank deficient rectangular values form a cone containing zero in positive dimension. -/
theorem zero_mem_and_smul_mem_rank_lt [NeZero d] :
    (0 : RectMatrixSpace r d) ∈ {P | (RectMatrixSpace.coordinates P).rank < d} ∧
      ∀ c : ℝ, 0 < c → ∀ P ∈ {P : RectMatrixSpace r d |
        (RectMatrixSpace.coordinates P).rank < d},
        c • P ∈ {P | (RectMatrixSpace.coordinates P).rank < d} := by
  constructor
  · change (0 : Matrix (Fin r) (Fin d) ℝ).rank < d
    simpa using Nat.pos_of_ne_zero (NeZero.ne d)
  · intro c hc P hP
    rw [mem_setOf_eq, rank_lt_iff_forall_minor_eq_zero] at hP ⊢
    intro I
    change (c • (RectMatrixSpace.coordinates P).submatrix I id).det = 0
    rw [Matrix.det_smul, hP, mul_zero]

/--
The singular polar obeys the wave cone constraint on an open set, following DPR's method.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Corollary 1.13.
-/
theorem HasEquationOn.ae_polar_mem_waveCone [NeZero d]
    {σ : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d))}
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (h : A.HasEquationOn M σ U) :
    ∀ᵐ x ∂(M.variation.singularPart volume).restrict U,
      VectorMeasure.polar M x ∈ A.waveCone := by
  let N := VectorMeasure.linearImage A.matrix M
  have hr := HasRectMeasureDivergenceOn.ae_rank_polar_le N _ hU
    ((A.hasEquationOn_iff_hasRectMeasureDivergenceOn M σ U).mp h)
  rw [ae_restrict_iff' hU.measurableSet] at hr ⊢
  have hN : ∀ᵐ x ∂N.variation.singularPart volume, x ∈ U →
      VectorMeasure.polar N x ∈ {P : RectMatrixSpace r d |
        (RectMatrixSpace.coordinates P).rank < d} := by
    filter_upwards [hr] with x hx hxU
    have hp := Nat.pos_of_ne_zero (NeZero.ne d)
    have hb := hx hxU
    change _ < d
    omega
  have ht := VectorMeasure.ae_apply_polar_mem_of_polar_linearImage_mem_on A.matrix M volume _
    (zero_mem_and_smul_mem_rank_lt (r := r) (d := d)).1
    (zero_mem_and_smul_mem_rank_lt (r := r) (d := d)).2 U hN
  filter_upwards [ht] with x hx hxU
  exact (A.mem_waveCone_iff_rank_lt _).mpr (hx hxU)

/--
The finite global wave cone theorem allows both a nonzero lower term and a measure source.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Corollary 1.13.
-/
theorem HasEquation.ae_polar_mem_waveCone [NeZero d]
    {σ : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d))}
    (h : A.HasEquation M σ) :
    ∀ᵐ x ∂M.variation.singularPart volume, VectorMeasure.polar M x ∈ A.waveCone := by
  simpa using HasEquationOn.ae_polar_mem_waveCone A M isOpen_univ h

/--
The local conclusion also holds with the coordinate polar and unit-frequency convention.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Corollary 1.13.
-/
theorem HasEquationOn.ae_polarDensity_symbol_eq_zero [NeZero d]
    {σ : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d))}
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (h : A.HasEquationOn M σ U) :
    ∀ᵐ x ∂(M.variation.singularPart volume).restrict U,
      ∃ ξ : EuclideanSpace ℝ (Fin d), ‖ξ‖ = 1 ∧ A.symbol ξ (polarDensity M x) = 0 := by
  have hp : VectorMeasure.polar M =ᵐ[(M.variation.singularPart volume).restrict U]
      polarDensity M := (Measure.absolutelyContinuous_of_le
    (Measure.restrict_le_self.trans (M.variation.singularPart_le volume))).ae_le
    (VectorMeasure.polar_ae_eq_polarDensity M)
  filter_upwards [HasEquationOn.ae_polar_mem_waveCone A M hU h, hp] with x hx he
  rw [← he]
  exact (A.mem_waveCone_iff_exists_unit _).mp hx

/-- Ellipticity means that the real principal wave cone is reduced to the zero vector. -/
def IsElliptic : Prop := A.waveCone = {0}

/--
An elliptic equation has absolutely continuous variation, with no assumption on the source density.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Corollary 1.13.
-/
theorem HasEquation.variation_absolutelyContinuous [NeZero d]
    {σ : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d))}
    (h : A.HasEquation M σ) (hell : A.IsElliptic) : M.variation ≪ volume := by
  apply absolutelyContinuous_of_ae_singularPart (μ := M.variation)
    (p := fun x => VectorMeasure.polar M x = 0) Measure.AbsolutelyContinuous.rfl
  · simpa only [IsElliptic] using
      (HasEquation.ae_polar_mem_waveCone A M h).mono (fun x hx => by
        rw [hell, mem_singleton_iff] at hx
        exact hx)
  · filter_upwards [VectorMeasure.ae_norm_polar_eq_one M] with x hx hz
    simp [hz] at hx

/--
Ellipticity annihilates the singular variation.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Corollary 1.13.
-/
theorem HasEquation.singularPart_variation_eq_zero [NeZero d]
    {σ : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d))}
    (h : A.HasEquation M σ) (hell : A.IsElliptic) : M.variation.singularPart volume = 0 :=
  Measure.singularPart_eq_zero_of_ac (HasEquation.variation_absolutelyContinuous A M h hell)

/--
The vector measure itself is absolutely continuous in the elliptic case.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Corollary 1.13.
-/
theorem HasEquation.absolutelyContinuous [NeZero d]
    {σ : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d))}
    (h : A.HasEquation M σ) (hell : A.IsElliptic) : M ≪ᵥ volume.toENNRealVectorMeasure :=
  (absolutelyContinuous_iff_variation M volume).mpr
    (HasEquation.variation_absolutelyContinuous A M h hell)

/--
For an elliptic equation on an open set, the variation restricted to that set is absolutely
continuous with respect to volume.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Corollary 1.13.
-/
theorem HasEquationOn.restrict_variation_absolutelyContinuous [NeZero d]
    {σ : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d))}
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (h : A.HasEquationOn M σ U) (hell : A.IsElliptic) : M.variation.restrict U ≪ volume := by
  have hp := HasEquationOn.ae_polar_mem_waveCone A M hU h
  rw [ae_restrict_iff' hU.measurableSet] at hp
  apply absolutelyContinuous_of_ae_singularPart (μ := M.variation)
    (p := fun x => x ∈ U → VectorMeasure.polar M x = 0)
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  · filter_upwards [hp] with x hx hxU
    have hm := hx hxU
    rwa [hell, mem_singleton_iff] at hm
  · filter_upwards [ae_restrict_mem hU.measurableSet,
      ae_restrict_of_ae (VectorMeasure.ae_norm_polar_eq_one M)] with x hx hn hz
    simp [hz hx] at hn

/--
The original singular variation vanishes inside an open elliptic region.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Corollary 1.13.
-/
theorem HasEquationOn.restrict_singularPart_variation_eq_zero [NeZero d]
    {σ : Fin r → SignedMeasure (EuclideanSpace ℝ (Fin d))}
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (h : A.HasEquationOn M σ U) (hell : A.IsElliptic) :
    (M.variation.singularPart volume).restrict U = 0 := by
  have hp := HasEquationOn.ae_polar_mem_waveCone A M hU h
  have hn : ∀ᵐ x ∂(M.variation.singularPart volume).restrict U,
      ‖VectorMeasure.polar M x‖ = 1 :=
    (Measure.absolutelyContinuous_of_le
      (Measure.restrict_le_self.trans (M.variation.singularPart_le volume))).ae_le
      (VectorMeasure.ae_norm_polar_eq_one M)
  have hf : ∀ᵐ x ∂(M.variation.singularPart volume).restrict U, False := by
    filter_upwards [hp, hn] with x hx hnorm
    rw [hell, mem_singleton_iff] at hx
    simp [hx] at hnorm
  apply Measure.measure_univ_eq_zero.mp
  simpa using ae_iff.mp hf

end FirstOrderOperator

end GeometricMeasure
