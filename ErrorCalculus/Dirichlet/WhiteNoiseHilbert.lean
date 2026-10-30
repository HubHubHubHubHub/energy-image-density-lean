import ErrorCalculus.Dirichlet.WhiteNoise
import ErrorCalculus.Dirichlet.ImageCalculus
import Mathlib.MeasureTheory.Function.Holder

/-! Cylindrical Hilbert white noise. A basis of the Bochner L² space is explicit;
no H-valued random variable is asserted to exist. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped InnerProductSpace Topology ENNReal
namespace ErrorCalculus

abbrev WhiteNoiseH := lp (fun _ : ℕ => ℝ) 2

variable {E K : Type*} [MeasurableSpace E] {μ : Measure E}
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Isonormal realization on the entire Bochner Hilbert space. -/
def isonormal (b : HilbertBasis ℕ ℝ (Lp K 2 μ)) :
    Lp K 2 μ →ₗᵢ[ℝ] Lp ℝ 2 Foundations.gaussianInf := whiteNoise b

/-- The elementary tensor is an actual Bochner L² function. -/
def whiteNoiseTensor (f : Lp ℝ 2 μ) (h : K) : Lp K 2 μ :=
  (ContinuousLinearMap.toSpanSingleton ℝ h).compLp f

theorem whiteNoiseTensor_ae (f : Lp ℝ 2 μ) (h : K) :
    whiteNoiseTensor f h =ᵐ[μ] fun x => f x • h :=
  (ContinuousLinearMap.toSpanSingleton ℝ h).coeFn_compLp f

theorem l2_integral_norm_sq (f : Lp K 2 μ) :
    (∫ x, ‖f x‖^2 ∂μ) = ‖f‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem whiteNoiseTensor_norm_sq (f : Lp ℝ 2 μ) (h : K) :
    ‖whiteNoiseTensor f h‖^2 = ‖f‖^2 * ‖h‖^2 := by
  rw [← l2_integral_norm_sq, ← l2_integral_norm_sq f, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [whiteNoiseTensor_ae f h] with x hx
  rw [hx, norm_smul, mul_pow]

/-- The corrected meaning of the pair (f,h) in definition 8.19. -/
def whiteNoisePair (b : HilbertBasis ℕ ℝ (Lp K 2 μ)) (f : Lp ℝ 2 μ) (h : K) :
    Lp ℝ 2 Foundations.gaussianInf := isonormal b (whiteNoiseTensor f h)

theorem whiteNoisePair_gaussian (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (f : Lp ℝ 2 μ) (h : K) :
    Foundations.gaussianInf.map (whiteNoisePair b f h) =
      gaussianReal 0 ⟨‖f‖^2 * ‖h‖^2, mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩ := by
  rw [whiteNoisePair, isonormal, whiteNoise_gaussian]
  congr 1
  exact Subtype.ext (whiteNoiseTensor_norm_sq f h)

theorem whiteNoisePair_sq (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (f : Lp ℝ 2 μ) (h : K) :
    (∫ ω, (whiteNoisePair b f h ω)^2 ∂Foundations.gaussianInf) = ‖f‖^2 * ‖h‖^2 := by
  rw [whiteNoisePair, isonormal, whiteNoise_sq, whiteNoiseTensor_norm_sq]

theorem whiteNoisePair_add_left (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (f g : Lp ℝ 2 μ) (h : K) :
    whiteNoisePair b (f + g) h = whiteNoisePair b f h + whiteNoisePair b g h := by
  change isonormal b ((ContinuousLinearMap.toSpanSingleton ℝ h).compLpL 2 μ (f+g)) = _
  rw [map_add, map_add]
  rfl

theorem whiteNoisePair_add_right (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (f : Lp ℝ 2 μ) (h k : K) :
    whiteNoisePair b f (h+k) = whiteNoisePair b f h + whiteNoisePair b f k := by
  have he : whiteNoiseTensor f (h+k) = whiteNoiseTensor f h + whiteNoiseTensor f k := by
    apply Lp.ext
    filter_upwards [whiteNoiseTensor_ae f (h+k), whiteNoiseTensor_ae f h,
      whiteNoiseTensor_ae f k, Lp.coeFn_add (whiteNoiseTensor f h) (whiteNoiseTensor f k)]
      with x h1 h2 h3 h4
    simp only [h1, h4, Pi.add_apply, h2, h3, smul_add]
  simp only [whiteNoisePair, he, map_add]

/-- Scalar projection (b). -/
def whiteNoiseScalar (b : HilbertBasis ℕ ℝ (Lp K 2 μ)) (h : K) (f : Lp ℝ 2 μ) :=
  whiteNoisePair b f h

/-- Multiplication by a density (a), tested against bounded f. -/
def whiteNoisePair_mul (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (φ : Lp ℝ 2 μ) (f : ImageTest E) (h : K) :=
  whiteNoisePair b (boundedMul f f.memLp_top φ) h

/-- Bounded scalar multiplication on Bochner L². -/
def whiteNoiseFieldMul (f : ImageTest E) : Lp K 2 μ →L[ℝ] Lp K 2 μ :=
  ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] K →L[ℝ] K).holderL μ ∞ 2 2)
    (f.memLp_top.toLp f)

theorem whiteNoiseFieldMul_ae (f : ImageTest E) (ψ : Lp K 2 μ) :
    whiteNoiseFieldMul f ψ =ᵐ[μ] fun x => f x • ψ x := by
  filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] K →L[ℝ] K).coeFn_holder (r := 2)
    (f.memLp_top.toLp f) ψ, f.memLp_top.coeFn_toLp] with x hx hf
  simpa [whiteNoiseFieldMul, hf] using hx

/-- Transformation (c), defined on every square integrable field at once. -/
def whiteNoiseField (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (ψ : Lp K 2 μ) (f : ImageTest E) : Lp ℝ 2 Foundations.gaussianInf :=
  isonormal b (whiteNoiseFieldMul f ψ)

theorem whiteNoiseField_norm (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (ψ : Lp K 2 μ) (f : ImageTest E) :
    (∫ ω, (whiteNoiseField b ψ f ω)^2 ∂Foundations.gaussianInf) =
      ∫ x, (f x)^2 * ‖ψ x‖^2 ∂μ := by
  rw [whiteNoiseField, isonormal, whiteNoise_sq, ← l2_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [whiteNoiseFieldMul_ae f ψ] with x hx
  rw [hx, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- The usual decomposable formula has the full norm, including cross terms. -/
theorem whiteNoiseField_decomposable_norm {ι : Type*} [Fintype ι]
    (b : HilbertBasis ℕ ℝ (Lp K 2 μ)) (ψ : ι → Lp ℝ 2 μ)
    (h : ι → K) (f : ImageTest E) :
    (∫ ω, (whiteNoiseField b (∑ i, whiteNoiseTensor (ψ i) (h i)) f ω)^2
      ∂Foundations.gaussianInf) =
      ∫ x, (f x)^2 * ‖∑ i, ψ i x • h i‖^2 ∂μ := by
  classical
  rw [whiteNoiseField_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => whiteNoiseTensor (ψ i) (h i)),
    ae_all_iff.mpr (fun i => whiteNoiseTensor_ae (ψ i) (h i))] with x hs ht
  simp only [hs, Finset.sum_apply, ht]

/-- On elementary tensors, transformation (c) is exactly (a)+(b). -/
theorem whiteNoiseField_tensor (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (φ : Lp ℝ 2 μ) (h : K) (f : ImageTest E) :
    whiteNoiseField b (whiteNoiseTensor φ h) f = whiteNoisePair_mul b φ f h := by
  apply (isonormal b).congr_arg
  apply Lp.ext
  filter_upwards [whiteNoiseFieldMul_ae f (whiteNoiseTensor φ h),
    whiteNoiseTensor_ae φ h, whiteNoiseTensor_ae (boundedMul f f.memLp_top φ) h,
    coeFn_boundedMul f f.memLp_top φ] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4, smul_smul]

theorem whiteNoiseField_decomposable {ι : Type*} [Fintype ι]
    (b : HilbertBasis ℕ ℝ (Lp K 2 μ)) (ψ : ι → Lp ℝ 2 μ)
    (h : ι → K) (f : ImageTest E) :
    whiteNoiseField b (∑ i, whiteNoiseTensor (ψ i) (h i)) f =
      ∑ i, whiteNoisePair_mul b (ψ i) f (h i) := by
  simp only [whiteNoiseField, map_sum]
  exact Finset.sum_congr rfl (fun i _ => whiteNoiseField_tensor b (ψ i) (h i) f)

/-- The direct construction agrees with every L² approximation by decomposables. -/
theorem whiteNoiseField_tendsto (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (f : ImageTest E) {ψ : ℕ → Lp K 2 μ} {ψ₀ : Lp K 2 μ}
    (hψ : Tendsto ψ atTop (𝓝 ψ₀)) :
    Tendsto (fun n => whiteNoiseField b (ψ n) f) atTop (𝓝 (whiteNoiseField b ψ₀ f)) :=
  ((isonormal b).continuous.comp (whiteNoiseFieldMul f).continuous).tendsto _ |>.comp hψ

/-- Refutation of literal 8.19. Bessel alone contradicts infinitely many equal
positive second moments; neither Gaussianity nor independence is needed. -/
theorem whiteNoiseH_not_in_L2_of_infinite {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (e : ℕ → K) (he : Orthonormal ℝ e) {c : ℝ} (hc : 0 < c) :
    ¬ ∃ v : Ω → K, MemLp v 2 P ∧
      ∀ n, (∫ ω, ⟪e n, v ω⟫_ℝ^2 ∂P) = c := by
  rintro ⟨v, hv, hmom⟩
  have hn : Integrable (fun ω => ‖v ω‖^2) P :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hi (n : ℕ) : Integrable (fun ω => ⟪e n, v ω⟫_ℝ^2) P :=
    ((innerSL ℝ (e n)).comp_memLp' hv).integrable_sq
  have hbound (N : ℕ) : (N : ℝ) * c ≤ ∫ ω, ‖v ω‖^2 ∂P := by
    calc
      _ = ∫ ω, ∑ n ∈ Finset.range N, ⟪e n, v ω⟫_ℝ^2 ∂P := by
        rw [integral_finset_sum _ (fun n _ => hi n)]
        simp [hmom]
      _ ≤ _ := integral_mono (integrable_finset_sum _ (fun n _ => hi n)) hn
        (fun ω => by simpa only [Real.norm_eq_abs, sq_abs] using
          he.sum_inner_products_le (s := Finset.range N) (v ω))
  obtain ⟨N, hN⟩ := exists_nat_gt ((∫ ω, ‖v ω‖^2 ∂P) / c)
  have hlt := (div_lt_iff₀ hc).mp hN
  exact (not_lt_of_ge (hbound N)) hlt

theorem whiteNoiseTensor_inner (f g : Lp ℝ 2 μ) (h k : K) :
    ⟪whiteNoiseTensor f h, whiteNoiseTensor g k⟫_ℝ = ⟪f,g⟫_ℝ * ⟪h,k⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [whiteNoiseTensor_ae f h, whiteNoiseTensor_ae g k] with x hx hy
  simp [hx, hy, inner_smul_left, inner_smul_right, mul_comm, mul_left_comm, mul_assoc]

theorem whiteNoisePair_smul_left (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (a : ℝ) (f : Lp ℝ 2 μ) (h : K) :
    whiteNoisePair b (a • f) h = a • whiteNoisePair b f h := by
  change isonormal b ((ContinuousLinearMap.toSpanSingleton ℝ h).compLpL 2 μ (a • f)) = _
  rw [map_smul, map_smul]
  rfl

theorem whiteNoisePair_smul_right (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (a : ℝ) (f : Lp ℝ 2 μ) (h : K) :
    whiteNoisePair b f (a • h) = a • whiteNoisePair b f h := by
  have he : whiteNoiseTensor f (a • h) = a • whiteNoiseTensor f h := by
    apply Lp.ext
    filter_upwards [whiteNoiseTensor_ae f (a • h), whiteNoiseTensor_ae f h,
      Lp.coeFn_smul a (whiteNoiseTensor f h)] with x h1 h2 h3
    simp only [h1, h3, Pi.smul_apply, h2]
    exact smul_comm _ _ _
  simp only [whiteNoisePair, he, map_smul]

theorem whiteNoiseField_gaussian (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (ψ : Lp K 2 μ) (f : ImageTest E) :
    HasGaussianLaw (whiteNoiseField b ψ f) Foundations.gaussianInf :=
  whiteNoise_hasGaussianLaw b _

variable [IsFiniteMeasure μ]

theorem whiteNoisePair_sigma_additive (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (A : ℕ → Set E) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (Disjoint on A)) (h : K) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      whiteNoisePair b (indicatorConstLp 2 (hA n) (measure_ne_top μ _) (1 : ℝ)) h)
      atTop (𝓝 (whiteNoisePair b (indicatorConstLp 2
        (MeasurableSet.iUnion hA) (measure_ne_top μ _) (1 : ℝ)) h)) := by
  let T := (isonormal b).toContinuousLinearMap.comp
    ((ContinuousLinearMap.toSpanSingleton ℝ h).compLpL 2 μ)
  have ht := T.continuous.tendsto _ |>.comp
    (whiteNoise_indicator_sigma_additive (μ := μ) A hA hdisj)
  have hT (f : Lp ℝ 2 μ) : T f = whiteNoisePair b f h := rfl
  simp only [Function.comp_def, map_sum] at ht
  simpa only [hT] using ht

theorem whiteNoisePair_indep_of_disjoint {ι : Type*}
    (b : HilbertBasis ℕ ℝ (Lp K 2 μ)) (A : ι → Set E)
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A)) (h : ι → K) :
    iIndepFun (fun i => whiteNoisePair b
      (indicatorConstLp 2 (hA i) (measure_ne_top μ _) (1 : ℝ)) (h i))
      Foundations.gaussianInf := by
  apply whiteNoise_indep_of_orthogonal
  intro i j hij
  rw [whiteNoiseTensor_inner, whiteNoise_indicator_orthogonal (hA i) (hA j) (hdisj hij), zero_mul]

theorem whiteNoiseScalar_associated_measure (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (h : K) (A : Set E) (hA : MeasurableSet A) :
    (∫ ω, (whiteNoiseScalar b h
      (indicatorConstLp 2 hA (measure_ne_top μ _) (1 : ℝ)) ω)^2 ∂Foundations.gaussianInf) =
      μ.real A * ‖h‖^2 := by
  rw [whiteNoiseScalar, whiteNoisePair_sq]
  congr 1
  rw [← l2_integral_norm_sq]
  calc
    _ = ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA)
        (hμs := measure_ne_top μ _) (c := (1 : ℝ))] with x hx
      rw [hx]
      by_cases h : x ∈ A <;> simp [h]
    _ = μ.real A := by rw [integral_indicator hA]; simp

/-- Independence of the whole cylindrical processes on disjoint sets. -/
theorem whiteNoisePair_indep_processes {ι : Type*}
    (b : HilbertBasis ℕ ℝ (Lp K 2 μ)) (A : ι → Set E)
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A)) :
    iIndepFun (fun i ω (h : K) => whiteNoisePair b
      (indicatorConstLp 2 (hA i) (measure_ne_top μ _) (1 : ℝ)) h ω)
      Foundations.gaussianInf := by
  apply IsGaussianProcess.iIndepFun_of_covariance_eq_zero
  · exact whiteNoise_isGaussianProcess b (fun p : (i : ι) × K =>
      whiteNoiseTensor (indicatorConstLp 2 (hA p.1) (measure_ne_top μ _) (1 : ℝ)) p.2)
  · intro i h
    exact (Lp.aestronglyMeasurable _).aemeasurable
  · intro i j hij h k
    change cov[whiteNoise b _, whiteNoise b _; Foundations.gaussianInf] = 0
    rw [whiteNoise_covariance, whiteNoiseTensor_inner,
      whiteNoise_indicator_orthogonal (hA i) (hA j) (hdisj hij), zero_mul]

/-- Variance of the multiplied noise, with density φ²‖h‖². -/
theorem whiteNoisePair_mul_sq (b : HilbertBasis ℕ ℝ (Lp K 2 μ))
    (φ : Lp ℝ 2 μ) (f : ImageTest E) (h : K) :
    (∫ ω, (whiteNoisePair_mul b φ f h ω)^2 ∂Foundations.gaussianInf) =
      (∫ x, (f x)^2 * (φ x)^2 ∂μ) * ‖h‖^2 := by
  rw [← whiteNoiseField_tensor, whiteNoiseField_norm, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [whiteNoiseTensor_ae φ h] with x hx
  rw [hx, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

end ErrorCalculus
