import GeometricMeasure.Analysis.SmoothL1Density
import GeometricMeasure.Current.BesselResolvent

/-!
# Convolution of weakly convergent tests with an integrable kernel

## Main results
An L¹ kernel transforms a sequence of smooth tests with common compact support and bounded L¹ norms,
converging against every smooth test to a finite signed measure σ, into a sequence converging in
L¹ to σ ∗ k. The limit measure needs no support assumption.

Reference: De Philippis–Rindler, arXiv p. 12, Lemma 2.1, specialized through the splitting b = b₁,ε
+ b₂,ε. Young estimates and linearity are established for finite positive and signed measures.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped Topology Convolution
namespace GeometricMeasure
namespace KernelCompactness
variable {d : ℕ}

/-- A smooth compactly supported function, viewed as a global scalar test. -/
def smoothCompactTest (κ : EuclideanSpace ℝ (Fin d) → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ) : ScalarCurrentTest d where
  toFun := κ
  contDiff' := hκ
  hasCompactSupport' := hκc
  tsupport_subset' := subset_univ _

/--
Density of smooth compactly supported tests in L¹ (test form of `exists_smooth_compact_l1_approx`).
-/
theorem exists_test_l1_approx {k : EuclideanSpace ℝ (Fin d) → ℝ} (hk : Integrable k)
    {δ : ℝ} (hδ : 0 < δ) : ∃ κ : ScalarCurrentTest d, (∫ x, ‖k x - κ x‖) < δ := by
  obtain ⟨κ, hκ, hκc, hl⟩ := exists_smooth_compact_l1_approx hk hδ
  exact ⟨smoothCompactTest κ hκ hκc, hl⟩

/-- Young (41) for a finite positive measure and an arbitrary integrable kernel. -/
theorem positiveConvolution_l1_le (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    {k : EuclideanSpace ℝ (Fin d) → ℝ} (hk : Integrable k) :
    (∫ x, ‖positiveConvolution μ k x‖) ≤
      (μ : Measure (EuclideanSpace ℝ (Fin d))).real univ * ∫ x, ‖k x‖ := by
  calc (∫ x, ‖positiveConvolution μ k x‖) ≤ ∫ x, positiveConvolution μ (fun y => ‖k y‖) x := by
        apply integral_mono (positiveConvolution_integrable μ k hk).norm
          (positiveConvolution_integrable μ _ hk.norm)
        intro x
        dsimp only
        rw [positiveConvolution_apply, positiveConvolution_apply]
        exact norm_integral_le_integral_norm _
    _ = (μ : Measure (EuclideanSpace ℝ (Fin d))).real univ * ∫ x, ‖k x‖ := by
        have h := integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
          (integrable_const (1 : ℝ) (μ := (μ : Measure (EuclideanSpace ℝ (Fin d))))) hk.norm
        simpa [positiveConvolution] using h

/-- Young (41) for a signed measure, with Jordan variation. -/
theorem signedConvolution_l1_le (σ : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {k : EuclideanSpace ℝ (Fin d) → ℝ} (hk : Integrable k) :
    (∫ x, ‖signedConvolution σ k x‖) ≤ σ.totalVariation.real univ * ∫ x, ‖k x‖ := by
  let μp : FiniteMeasure (EuclideanSpace ℝ (Fin d)) := ⟨σ.toJordanDecomposition.posPart, inferInstance⟩
  let μn : FiniteMeasure (EuclideanSpace ℝ (Fin d)) := ⟨σ.toJordanDecomposition.negPart, inferInstance⟩
  have hp := positiveConvolution_integrable μp k hk
  have hn := positiveConvolution_integrable μn k hk
  have htv : σ.totalVariation.real univ =
      (μp : Measure (EuclideanSpace ℝ (Fin d))).real univ +
        (μn : Measure (EuclideanSpace ℝ (Fin d))).real univ := by
    simp only [SignedMeasure.totalVariation, measureReal_def, Measure.add_apply]
    exact ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
  calc (∫ x, ‖signedConvolution σ k x‖) ≤
      ∫ x, (‖positiveConvolution μp k x‖ + ‖positiveConvolution μn k x‖) := by
        apply integral_mono (signedConvolution_integrable σ k hk).norm (hp.norm.add hn.norm)
        intro x
        exact norm_sub_le _ _
    _ = (∫ x, ‖positiveConvolution μp k x‖) + ∫ x, ‖positiveConvolution μn k x‖ :=
        integral_add hp.norm hn.norm
    _ ≤ (μp : Measure (EuclideanSpace ℝ (Fin d))).real univ * (∫ x, ‖k x‖) +
        (μn : Measure (EuclideanSpace ℝ (Fin d))).real univ * ∫ x, ‖k x‖ :=
        add_le_add (positiveConvolution_l1_le μp hk) (positiveConvolution_l1_le μn hk)
    _ = σ.totalVariation.real univ * ∫ x, ‖k x‖ := by rw [htv, add_mul]

/-- Almost-everywhere linearity of positive-measure convolution in the kernel. -/
theorem positiveConvolution_sub_ae (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    {k κ : EuclideanSpace ℝ (Fin d) → ℝ} (hk : Integrable k) (hκ : Integrable κ) :
    ∀ᵐ x, positiveConvolution μ k x - positiveConvolution μ κ x =
      positiveConvolution μ (k - κ) x := by
  have hi : ∀ {f : EuclideanSpace ℝ (Fin d) → ℝ}, Integrable f →
      ∀ᵐ x, Integrable (fun y => f (x - y)) (μ : Measure (EuclideanSpace ℝ (Fin d))) := by
    intro f hf
    have h := ((integrable_const (1 : ℝ) (μ := (μ : Measure (EuclideanSpace ℝ (Fin d))))).convolution_integrand
      (ContinuousLinearMap.mul ℝ ℝ) hf).prod_right_ae
    filter_upwards [h] with x hx
    simpa using hx
  filter_upwards [hi hk, hi hκ] with x h1 h2
  rw [positiveConvolution_apply, positiveConvolution_apply, positiveConvolution_apply,
    ← integral_sub h1 h2]
  rfl

/-- Almost-everywhere linearity of signed convolution in the kernel. -/
theorem signedConvolution_sub_ae (σ : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {k κ : EuclideanSpace ℝ (Fin d) → ℝ} (hk : Integrable k) (hκ : Integrable κ) :
    ∀ᵐ x, signedConvolution σ k x - signedConvolution σ κ x = signedConvolution σ (k - κ) x := by
  filter_upwards [positiveConvolution_sub_ae ⟨σ.toJordanDecomposition.posPart, inferInstance⟩ hk hκ,
    positiveConvolution_sub_ae ⟨σ.toJordanDecomposition.negPart, inferInstance⟩ hk hκ] with x h1 h2
  simp only [signedConvolution, Pi.sub_apply]
  rw [← h1, ← h2]
  ring

/-- Pointwise linearity of test convolution in the integrable kernel. -/
theorem scalarConvolution_sub_kernel {k κ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hk : Integrable k) (hκ : Integrable κ) (u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    scalarConvolution k u x - scalarConvolution κ u x = scalarConvolution (k - κ) u x := by
  have h1 : Integrable (fun y => k y * u (x - y)) := by
    simpa using (scalarConvolution_exists k hk u x).integrable
  have h2 : Integrable (fun y => κ y * u (x - y)) := by
    simpa using (scalarConvolution_exists κ hκ u x).integrable
  rw [scalarConvolution_apply, scalarConvolution_apply, scalarConvolution_apply, ← integral_sub h1 h2]
  congr 1
  funext y
  simp only [Pi.sub_apply, sub_mul]

/-- Convolution of a test by a test: pairing with the reflected translated kernel. -/
theorem scalarConvolution_test_eq (κ u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    scalarConvolution κ u x = ∫ y, translatedKernelTest κ x y * u y := by
  rw [scalarConvolution_apply]
  have h := integral_sub_left_eq_self (fun y => κ (x - y) * u y)
    (volume : Measure (EuclideanSpace ℝ (Fin d))) x
  simp only [sub_sub_cancel] at h
  rw [h]
  rfl

/-- Vanishing outside B̄(0,R+r) for supports in B̄(0,R) and B̄(0,r). -/
theorem scalarConvolution_test_eq_zero (κ u : ScalarCurrentTest d) {R r : ℝ}
    (hu : tsupport (u : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ closedBall 0 R)
    (hκ : tsupport (κ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ closedBall 0 r)
    {x : EuclideanSpace ℝ (Fin d)} (hx : R + r < ‖x‖) : scalarConvolution κ u x = 0 := by
  rw [scalarConvolution_apply]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  by_cases hy : y ∈ tsupport (κ : EuclideanSpace ℝ (Fin d) → ℝ)
  · have hy' := hκ hy
    rw [mem_closedBall, dist_zero_right] at hy'
    have hxy : x - y ∉ tsupport (u : EuclideanSpace ℝ (Fin d) → ℝ) := by
      intro hm
      have h3 := hu hm
      rw [mem_closedBall, dist_zero_right] at h3
      have h4 := norm_sub_norm_le x y
      linarith
    simp [image_eq_zero_of_notMem_tsupport hxy]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- Uniform bound ‖κ ∗ u‖_∞ ≤ ‖κ‖_∞ ‖u‖₁. -/
theorem scalarConvolution_test_norm_le (κ u : ScalarCurrentTest d) (x : EuclideanSpace ℝ (Fin d)) :
    ‖scalarConvolution κ u x‖ ≤
      ‖(κ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ * ∫ y, ‖u y‖ := by
  rw [scalarConvolution_test_eq]
  calc ‖∫ y, translatedKernelTest κ x y * u y‖ ≤ ∫ y, ‖translatedKernelTest κ x y * u y‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖(κ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ * ‖u y‖ := by
        apply integral_mono
          (integrable_mul_scalarTest (scalarTest_integrable (translatedKernelTest κ x)) u).norm
          ((scalarTest_integrable u).norm.const_mul _)
        intro y
        dsimp only
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          ((κ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).norm_coe_le_norm (x - y))
          (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- For a smooth test kernel: dominated convergence with a common compact support. -/
theorem smooth_kernel_l1_tendsto (κ : ScalarCurrentTest d)
    (u : ℕ → ScalarCurrentTest d) (R C : ℝ)
    (hsupp : ∀ n, tsupport (u n : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ closedBall 0 R)
    (hC : ∀ n, (∫ y, ‖u n y‖) ≤ C)
    (σ : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hσ : ∀ φ : ScalarCurrentTest d,
      Tendsto (fun n => ∫ y, φ y * u n y) atTop (𝓝 (signedTestCurrent σ φ))) :
    Tendsto (fun n => ∫ x, ‖scalarConvolution κ (u n) x - signedConvolution σ κ x‖)
      atTop (𝓝 0) := by
  obtain ⟨r, hr⟩ := κ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  let A := ‖(κ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖ * C
  have hσi := signedConvolution_integrable σ κ (scalarTest_integrable κ)
  let F : EuclideanSpace ℝ (Fin d) → ℝ := fun x =>
    (closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + r)).indicator (fun _ => A) x +
      ‖signedConvolution σ κ x‖
  have hF : Integrable F :=
    ((integrableOn_const (C := A) measure_closedBall_lt_top.ne).integrable_indicator
      measurableSet_closedBall).add hσi.norm
  have hlim := tendsto_integral_of_dominated_convergence
    (F := fun n x => ‖scalarConvolution κ (u n) x - signedConvolution σ κ x‖)
    (f := fun _ => (0 : ℝ)) F
    (fun n => (((u n).hasCompactSupport.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (scalarTest_integrable κ).locallyIntegrable (u n).continuous).sub
      (signedConvolution_smooth σ κ κ.contDiff κ.hasCompactSupport).continuous).norm.aestronglyMeasurable)
    hF
    (fun n => Eventually.of_forall (fun x => by
      rw [norm_norm]
      have hA : ‖scalarConvolution κ (u n) x‖ ≤ A :=
        (scalarConvolution_test_norm_le κ (u n) x).trans
          (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _))
      by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + r)
      · simp only [F, indicator_of_mem hx]
        exact (norm_sub_le _ _).trans (add_le_add hA le_rfl)
      · have hx' : R + r < ‖x‖ := by
          rw [mem_closedBall, dist_zero_right, not_le] at hx
          exact hx
        rw [scalarConvolution_test_eq_zero κ (u n) (hsupp n) hr hx', zero_sub, norm_neg]
        simp only [F, indicator_of_notMem hx, zero_add, le_refl]))
    (Eventually.of_forall (fun x => by
      have h := hσ (translatedKernelTest κ x)
      rw [signedConvolution_translated_test] at h
      have h2 := (h.sub_const (signedConvolution σ κ x)).norm
      simp only [sub_self, norm_zero] at h2
      refine h2.congr' (Eventually.of_forall (fun n => ?_))
      simp only [scalarConvolution_test_eq]))
  simpa only [integral_zero] using hlim

/--
Epsilon criterion: a nonnegative sequence bounded up to ε by sequences tending to zero tends to
zero.
-/
theorem tendsto_zero_of_forall_approx {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (h : ∀ ε > 0, ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧ ∀ n, a n ≤ b n + ε) :
    Tendsto a atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨b, hb, hab⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hb (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  rw [abs_of_nonneg (ha n)]
  have h2 := (abs_lt.mp h1).2
  linarith [hab n]

/--
An integrable kernel k transforms a sequence of smooth tests uₙ supported in a fixed ball, with
bounded L¹ norms and convergence against every smooth test to a finite signed measure σ, into k ∗ uₙ
→ σ ∗ k in L¹. The whole sequence converges; no support assumption on σ is needed. Reference: De
Philippis–Rindler, arXiv p. 12, Lemma 2.1, specialized via b = b₁,ε + b₂,ε.
-/
theorem kernel_l1_tendsto_of_test_tendsto {k : EuclideanSpace ℝ (Fin d) → ℝ} (hk : Integrable k)
    (u : ℕ → ScalarCurrentTest d) (R C : ℝ)
    (hsupp : ∀ n, tsupport (u n : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ closedBall 0 R)
    (hC : ∀ n, (∫ y, ‖u n y‖) ≤ C)
    (σ : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    (hσ : ∀ φ : ScalarCurrentTest d,
      Tendsto (fun n => ∫ y, φ y * u n y) atTop (𝓝 (signedTestCurrent σ φ))) :
    Integrable (signedConvolution σ k) ∧
    Tendsto (fun n => ∫ x, ‖scalarConvolution k (u n) x - signedConvolution σ k x‖)
      atTop (𝓝 0) := by
  refine ⟨signedConvolution_integrable σ k hk, ?_⟩
  apply tendsto_zero_of_forall_approx (fun n => integral_nonneg (fun _ => norm_nonneg _))
  intro ε hε
  set T := σ.totalVariation.real univ with hTdef
  have hT : 0 ≤ T := measureReal_nonneg
  have hC0 : 0 ≤ C := (integral_nonneg (fun _ => norm_nonneg _)).trans (hC 0)
  set δ := ε / (C + T + 1) with hδdef
  have hpos : 0 < C + T + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hpos
  obtain ⟨κ, hκ⟩ := exists_test_l1_approx hk hδ
  have hκi := scalarTest_integrable κ
  have hdi : Integrable (k - (κ : EuclideanSpace ℝ (Fin d) → ℝ)) := hk.sub hκi
  refine ⟨_, smooth_kernel_l1_tendsto κ u R C hsupp hC σ hσ, fun n => ?_⟩
  have hun := scalarTest_integrable (u n)
  have i1 : Integrable (scalarConvolution (k - (κ : EuclideanSpace ℝ (Fin d) → ℝ)) (u n)) :=
    integrable_scalarConvolution hdi hun
  have i2 : Integrable (fun x => scalarConvolution κ (u n) x - signedConvolution σ κ x) :=
    (integrable_scalarConvolution hκi hun).sub (signedConvolution_integrable σ κ hκi)
  have i3 : Integrable (signedConvolution σ (k - (κ : EuclideanSpace ℝ (Fin d) → ℝ))) :=
    signedConvolution_integrable σ _ hdi
  have i0 : Integrable (fun x => scalarConvolution k (u n) x - signedConvolution σ k x) :=
    (integrable_scalarConvolution hk hun).sub (signedConvolution_integrable σ k hk)
  have hpt : ∀ᵐ x, ‖scalarConvolution k (u n) x - signedConvolution σ k x‖ ≤
      ‖scalarConvolution (k - (κ : EuclideanSpace ℝ (Fin d) → ℝ)) (u n) x‖ +
        ‖scalarConvolution κ (u n) x - signedConvolution σ κ x‖ +
        ‖signedConvolution σ (k - (κ : EuclideanSpace ℝ (Fin d) → ℝ)) x‖ := by
    filter_upwards [signedConvolution_sub_ae σ hk hκi] with x hx
    rw [← hx, ← scalarConvolution_sub_kernel hk hκi (u n) x]
    calc ‖scalarConvolution k (u n) x - signedConvolution σ k x‖ =
        ‖(scalarConvolution k (u n) x - scalarConvolution κ (u n) x) +
          (scalarConvolution κ (u n) x - signedConvolution σ κ x) -
          (signedConvolution σ k x - signedConvolution σ κ x)‖ := by ring_nf
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hI0 := integral_mono_ae i0.norm ((i1.norm.add i2.norm).add i3.norm) hpt
  have hsplit : (∫ x, (‖scalarConvolution (k - (κ : EuclideanSpace ℝ (Fin d) → ℝ)) (u n) x‖ +
        ‖scalarConvolution κ (u n) x - signedConvolution σ κ x‖ +
        ‖signedConvolution σ (k - (κ : EuclideanSpace ℝ (Fin d) → ℝ)) x‖)) =
      (∫ x, ‖scalarConvolution (k - (κ : EuclideanSpace ℝ (Fin d) → ℝ)) (u n) x‖) +
        (∫ x, ‖scalarConvolution κ (u n) x - signedConvolution σ κ x‖) +
        ∫ x, ‖signedConvolution σ (k - (κ : EuclideanSpace ℝ (Fin d) → ℝ)) x‖ := by
    rw [integral_add (f := fun x => ‖scalarConvolution (k - (κ : EuclideanSpace ℝ (Fin d) → ℝ)) (u n) x‖ +
        ‖scalarConvolution κ (u n) x - signedConvolution σ κ x‖)
      (g := fun x => ‖signedConvolution σ (k - (κ : EuclideanSpace ℝ (Fin d) → ℝ)) x‖)
      (i1.norm.add i2.norm) i3.norm,
      integral_add (f := fun x => ‖scalarConvolution (k - (κ : EuclideanSpace ℝ (Fin d) → ℝ)) (u n) x‖)
      (g := fun x => ‖scalarConvolution κ (u n) x - signedConvolution σ κ x‖) i1.norm i2.norm]
  have hI := hI0.trans_eq hsplit
  have hd0 : 0 ≤ ∫ x, ‖(k - (κ : EuclideanSpace ℝ (Fin d) → ℝ)) x‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have hdl : (∫ x, ‖(k - (κ : EuclideanSpace ℝ (Fin d) → ℝ)) x‖) ≤ δ := hκ.le
  have h1 := (integral_norm_scalarConvolution_le hdi hun).trans
    (mul_le_mul hdl (hC n) (integral_nonneg (fun _ => norm_nonneg _)) hδ.le)
  have h3 := (signedConvolution_l1_le σ hdi).trans (mul_le_mul_of_nonneg_left hdl hT)
  have hfin : δ * C + T * δ ≤ ε := by
    have he : δ * (C + T + 1) = ε := by
      rw [hδdef]
      field_simp
    nlinarith
  linarith

end KernelCompactness
end GeometricMeasure
