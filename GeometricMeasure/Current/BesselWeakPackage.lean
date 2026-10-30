import GeometricMeasure.Current.BesselWeak
import GeometricMeasure.Current.BesselResolventPackage

/-!
# Convergence estimates for the Bessel error terms

## Main results
For tₙ = −Σ_ab S_ab fₙ,ab with the sum of input L¹ masses tending to zero, the error terms are
integrable, have zero mean, converge globally in measure and against tests, and have negative parts
converging locally in measure. The construction uses the same mollification sequence.

Reference: De Philippis–Rindler, pp. 9–10, (2.9)–(2.12), and Lemma 2.2.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Convolution

namespace GeometricMeasure
variable {d : ℕ}

/--
Finite union of level sets, with constant equal to the number of terms. Source: DPR, local
transcription pp. 9–10 (context).
-/
theorem finite_sum_weak11 {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    {μ : Measure α} (q : ι → α → ℝ) (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    {C : ℝ} (hC : 0 ≤ C)
    (hq : ∀ i, ∀ t : ℝ, 0 < t → μ {x | t < ‖q i x‖} ≤ ENNReal.ofReal (C * m i / t))
    {lam : ℝ} (hlam : 0 < lam) :
    μ {x | lam < ‖∑ i, q i x‖} ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * C * (∑ i, m i) / lam) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    simp [not_lt_of_ge hlam.le]
  | inr hi =>
    have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have ht : 0 < lam / (Fintype.card ι : ℝ) := div_pos hlam hN
    have hs : {x | lam < ‖∑ i, q i x‖} ⊆
        ⋃ i, {x | lam / (Fintype.card ι : ℝ) < ‖q i x‖} := by
      intro x hx
      by_contra hn
      have hi : ∀ i, ‖q i x‖ ≤ lam / (Fintype.card ι : ℝ) := by
        intro i
        exact le_of_not_gt (fun h => hn (mem_iUnion.2 ⟨i, h⟩))
      have hnorm := (norm_sum_le (s := Finset.univ) (f := fun i => q i x)).trans
        (Finset.sum_le_sum (fun i _ => hi i))
      have he : (∑ _ : ι, lam / (Fintype.card ι : ℝ)) = lam := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
      rw [he] at hnorm
      exact (not_lt_of_ge hnorm) hx
    apply (measure_mono hs).trans
    apply (measure_iUnion_le _).trans
    rw [tsum_fintype]
    calc
      _ ≤ ∑ i, ENNReal.ofReal (C * m i / (lam / (Fintype.card ι : ℝ))) :=
        Finset.sum_le_sum (fun i _ => hq i _ ht)
      _ = ENNReal.ofReal (∑ i, C * m i / (lam / (Fintype.card ι : ℝ))) :=
        (ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (mul_nonneg hC (hm i)) ht.le)).symm
      _ = _ := by
        congr 1
        rw [← Finset.sum_div, ← Finset.mul_sum]
        field_simp

/--
Matrix version (54), with t=-Σ_ab S_ab f_ab and N=d². Source: DPR, local transcription pp. 9–10
(context).
-/
theorem resolventError_weak11 (f : Fin d → Fin d → ScalarCurrentTest d)
    {lam : ℝ} (hlam : 0 < lam) :
    volume {x | lam < ‖resolventError f x‖} ≤
      ENNReal.ofReal ((d : ℝ) ^ 2 * besselWeakConstant d *
        (∑ a : Fin d, ∑ b : Fin d, ∫ x, ‖f a b x‖) / lam) := by
  have h := finite_sum_weak11
    (fun p : Fin d × Fin d => besselSecond p.1 p.2 (f p.1 p.2))
    (fun p : Fin d × Fin d => ∫ x, ‖f p.1 p.2 x‖)
    (fun _ => integral_nonneg (fun _ => norm_nonneg _)) (besselWeakConstant_nonneg d)
    (fun p _ ht => besselSecond_weak11 p.1 p.2 (f p.1 p.2) ht) hlam
  simpa only [resolventError_eq_sum, Pi.neg_apply, Finset.sum_apply, norm_neg,
    Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using h

/-- scalar global convergence in measure. Source: DPR, local transcription pp. 9–10 (context). -/
theorem besselSecond_level_tendsto (a b : Fin d) (u : ℕ → ScalarCurrentTest d)
    (hu : Tendsto (fun n => ∫ x, ‖u n x‖) atTop (𝓝 0))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n => volume {x | lam < ‖besselSecond a b (u n) x‖}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun _ => bot_le) (fun n => besselSecond_weak11 a b (u n) hlam)
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((hu.const_mul (besselWeakConstant d)).div_const lam)
  simpa only [Function.comp_def, mul_zero, zero_div, ENNReal.ofReal_zero] using h

/--
distributional convergence independent of the weak bound. Source: DPR, local transcription pp. 9–10
(context).
-/
theorem besselSecond_pairing_tendsto (a b : Fin d) (u : ℕ → ScalarCurrentTest d)
    (hu : Tendsto (fun n => ∫ x, ‖u n x‖) atTop (𝓝 0)) (φ : ScalarCurrentTest d) :
    Tendsto (fun n => ∫ x, besselSecond a b (u n) x * φ x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => besselSecond_pairing_bound a b (u n) φ)
  simpa only [zero_mul] using hu.mul_const
    ‖(cutoffPartialTest (cutoffPartialTest φ a) b :
      BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)‖

/--
The pairing with t is exactly the finite sum of the scalar pairings, with the negative sign in the
resolvent decomposition. Source: DPR, local transcription pp. 9–10 (context).
-/
theorem resolventError_pairing (f : Fin d → Fin d → ScalarCurrentTest d)
    (φ : ScalarCurrentTest d) :
    (∫ x, resolventError f x * φ x) =
      - ∑ a : Fin d, ∑ b : Fin d, ∫ x, besselSecond a b (f a b) x * φ x := by
  simp only [resolventError_eq_sum, Pi.neg_apply, Finset.sum_apply, neg_mul, Finset.sum_mul]
  rw [integral_neg, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    exact integral_finsetSum _ (fun b _ =>
      integrable_mul_scalarTest (integrable_besselSecond a b (f a b)) φ)
  · intro a _
    exact integrable_finsetSum _ (fun b _ =>
      integrable_mul_scalarTest (integrable_besselSecond a b (f a b)) φ)

/--
The L¹ sum assumption implies smallness of each component. Source: DPR, local transcription pp. 9–10
(context).
-/
theorem tendsto_matrix_component_mass
    (f : ℕ → Fin d → Fin d → ScalarCurrentTest d)
    (hf : Tendsto (fun n => ∑ a : Fin d, ∑ b : Fin d, ∫ x, ‖f n a b x‖) atTop (𝓝 0))
    (a b : Fin d) : Tendsto (fun n => ∫ x, ‖f n a b x‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg (fun _ => norm_nonneg _)) _ hf
  intro n
  have h1 : (∫ x, ‖f n a b x‖) ≤ ∑ j : Fin d, ∫ x, ‖f n a j x‖ :=
    Finset.single_le_sum (f := fun j : Fin d => ∫ x, ‖f n a j x‖)
      (fun j _ => integral_nonneg (fun _ => norm_nonneg _)) (Finset.mem_univ b)
  have h2 : (∑ j : Fin d, ∫ x, ‖f n a j x‖) ≤
      ∑ i : Fin d, ∑ j : Fin d, ∫ x, ‖f n i j x‖ :=
    Finset.single_le_sum (f := fun i : Fin d => ∑ j : Fin d, ∫ x, ‖f n i j x‖)
      (fun i _ => Finset.sum_nonneg (fun j _ => integral_nonneg (fun _ => norm_nonneg _)))
      (Finset.mem_univ a)
  exact h1.trans h2

/-- global convergence in measure of t. Source: DPR, local transcription pp. 9–10 (context). -/
theorem resolventError_level_tendsto
    (f : ℕ → Fin d → Fin d → ScalarCurrentTest d)
    (hf : Tendsto (fun n => ∑ a : Fin d, ∑ b : Fin d, ∫ x, ‖f n a b x‖) atTop (𝓝 0))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n => volume {x | lam < ‖resolventError (f n) x‖}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun _ => bot_le) (fun n => resolventError_weak11 (f n) hlam)
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((hf.const_mul ((d : ℝ) ^ 2 * besselWeakConstant d)).div_const lam)
  simpa only [Function.comp_def, mul_zero, zero_div, ENNReal.ofReal_zero] using h

/--
convergence against every test, without assumptions on the derivatives of f_n. Source: DPR, local
transcription pp. 9–10 (context).
-/
theorem resolventError_pairing_tendsto
    (f : ℕ → Fin d → Fin d → ScalarCurrentTest d)
    (hf : Tendsto (fun n => ∑ a : Fin d, ∑ b : Fin d, ∫ x, ‖f n a b x‖) atTop (𝓝 0))
    (φ : ScalarCurrentTest d) :
    Tendsto (fun n => ∫ x, resolventError (f n) x * φ x) atTop (𝓝 0) := by
  simp only [resolventError_pairing]
  have h := (tendsto_finsetSum Finset.univ (fun a _ =>
    tendsto_finsetSum Finset.univ (fun b _ =>
      besselSecond_pairing_tendsto a b (fun n => f n a b)
        (tendsto_matrix_component_mass f hf a b) φ))).neg
  simpa only [Finset.sum_const_zero, neg_zero] using h

/--
Local version for the negative parts, used in the positivity argument. Source: DPR, local
transcription pp. 9–10 (context).
-/
theorem resolventError_negative_local_tendsto
    (f : ℕ → Fin d → Fin d → ScalarCurrentTest d)
    (hf : Tendsto (fun n => ∑ a : Fin d, ∑ b : Fin d, ∫ x, ‖f n a b x‖) atTop (𝓝 0))
    (R : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n => volume {x | x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) R ∧
      lam < max 0 (-resolventError (f n) x)}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (resolventError_level_tendsto f hf hlam) (fun _ => bot_le) ?_
  intro n
  apply measure_mono
  intro x hx
  have hn : max 0 (-resolventError (f n) x) ≤ ‖resolventError (f n) x‖ :=
    max_le (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using neg_le_abs (resolventError (f n) x))
  exact hx.2.trans_le hn

/--
Combined estimates for the positivity argument; no positivity conclusion is assumed. Source:
DPR, local transcription pp. 9–10 (context).
-/
theorem resolventError_estimates
    (f : ℕ → Fin d → Fin d → ScalarCurrentTest d)
    (hf : Tendsto (fun n => ∑ a : Fin d, ∑ b : Fin d, ∫ x, ‖f n a b x‖) atTop (𝓝 0)) :
    (∀ n, Integrable (resolventError (f n)) ∧ (∫ x, resolventError (f n) x) = 0) ∧
    (∀ lam : ℝ, 0 < lam →
      Tendsto (fun n => volume {x | lam < ‖resolventError (f n) x‖}) atTop (𝓝 0)) ∧
    (∀ φ : ScalarCurrentTest d,
      Tendsto (fun n => ∫ x, resolventError (f n) x * φ x) atTop (𝓝 0)) ∧
    (∀ R lam : ℝ, 0 < lam → Tendsto
      (fun n => volume {x | x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) R ∧
        lam < max 0 (-resolventError (f n) x)}) atTop (𝓝 0)) :=
  ⟨fun n => ⟨integrable_resolventError (f n), integral_resolventError (f n)⟩,
    fun _ ht => resolventError_level_tendsto f hf ht,
    resolventError_pairing_tendsto f hf,
    fun R _ ht => resolventError_negative_local_tendsto f hf R ht⟩

namespace MatrixPolarBlowupData
variable {M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (MatrixSpace d)}
variable {D : Fin d → SignedMeasure (EuclideanSpace ℝ (Fin d))}
variable {x : EuclideanSpace ℝ (Fin d)}

/--
Smallness of the sum of localized mollification data components; no new diagonal choice. Source:
DPR, local transcription pp. 9–10 (context).
-/
theorem mollifiedDefectTest_sum_mass_tendsto (b : MatrixPolarBlowupData M D x) :
    Tendsto (fun n => ∑ a : Fin d, ∑ j : Fin d, ∫ y, ‖b.mollifiedDefectTest n a j y‖)
      atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ (fun a _ =>
    tendsto_finsetSum Finset.univ (fun j _ => b.mollifiedDefectTest_L1_tendsto a j))
  simpa only [Finset.sum_const_zero] using h

/--
The convergence estimates applied to the mollified blow-up data. Source: DPR, local transcription
pp. 9–10 (context).
-/
theorem mollified_resolvent_estimates (b : MatrixPolarBlowupData M D x) :
    (∀ n, Integrable (resolventError (b.mollifiedDefectTest n)) ∧
      (∫ y, resolventError (b.mollifiedDefectTest n) y) = 0) ∧
    (∀ lam : ℝ, 0 < lam → Tendsto
      (fun n => volume {y | lam < ‖resolventError (b.mollifiedDefectTest n) y‖}) atTop (𝓝 0)) ∧
    (∀ φ : ScalarCurrentTest d, Tendsto
      (fun n => ∫ y, resolventError (b.mollifiedDefectTest n) y * φ y) atTop (𝓝 0)) ∧
    (∀ R lam : ℝ, 0 < lam → Tendsto
      (fun n => volume {y | y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) R ∧
        lam < max 0 (-resolventError (b.mollifiedDefectTest n) y)}) atTop (𝓝 0)) :=
  resolventError_estimates b.mollifiedDefectTest b.mollifiedDefectTest_sum_mass_tendsto

end MatrixPolarBlowupData
end GeometricMeasure
