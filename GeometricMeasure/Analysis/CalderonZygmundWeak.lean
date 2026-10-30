import GeometricMeasure.Analysis.HeatKernel
import GeometricMeasure.Analysis.CalderonZygmundDecomposition
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# An abstract weak (1,1) convolution criterion

## Main results
A strongly measurable, integrable, bounded kernel satisfying an L² estimate on L¹ ∩ L² and an
integral Hörmander condition obeys a weak (1,1) bound in positive dimension. The constant is 10^d +
4 A² 5^d + 4 H for a strictly positive threshold.

Bibliographic context: De Philippis–Rindler, pp. 9–10, (2.9)–(2.12). The additional page locators,
Annals pp. 1027–1028 and 1032, Hörmander pp. 113–117, and Hart Smith pp. 2–8, are unverified against
those editions.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Convolution

namespace GeometricMeasure.CalderonZygmund
variable {d : ℕ}

/--
Ordinary convolution in the orientation needed for cancellation. Source: DPR, local transcription
pp. 9–10 (context).
-/
theorem convolution_right (k f : Space d → ℝ) (x : Space d) :
    scalarConvolution k f x = ∫ y, k (x - y) * f y := by
  rw [scalarConvolution_apply]
  have h := integral_sub_left_eq_self (fun y => k (x - y) * f y) volume x
  simpa only [sub_sub_cancel] using h

/--
A bounded measurable kernel and an integrable input give an absolutely convergent integral at every
point. Source: DPR, local transcription pp. 9–10 (context).
-/
theorem integrable_convolution_right {k f : Space d → ℝ}
    (hk : StronglyMeasurable k) {M : ℝ} (hM : ∀ x, ‖k x‖ ≤ M)
    (hf : Integrable f) (x : Space d) :
    Integrable (fun y => k (x - y) * f y) := by
  apply (hf.norm.const_mul M).mono'
    ((hk.comp_measurable (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable)
  exact ae_of_all _ (fun y => by
    change ‖k (x - y) * f y‖ ≤ M * ‖f y‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))

/--
Pointwise bound by the L¹ mass of the input, for a bounded measurable kernel. Source: DPR, local
transcription pp. 9–10 (context).
-/
theorem norm_convolution_le_mass {k f : Space d → ℝ}
    (hk : StronglyMeasurable k) {M : ℝ} (hM : ∀ x, ‖k x‖ ≤ M)
    (hf : Integrable f) (x : Space d) :
    ‖scalarConvolution k f x‖ ≤ M * mass f := by
  rw [convolution_right]
  calc _ ≤ ∫ y, ‖k (x - y) * f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, M * ‖f y‖ := integral_mono
      (integrable_convolution_right hk hM hf x).norm (hf.norm.const_mul M)
      (fun y => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
    _ = _ := integral_const_mul _ _

/--
Linearity under differences of integrable inputs, for a fixed bounded measurable kernel. Source:
DPR, local transcription pp. 9–10 (context).
-/
theorem convolution_sub {k f g : Space d → ℝ}
    (hk : StronglyMeasurable k) {M : ℝ} (hM : ∀ x, ‖k x‖ ≤ M)
    (hf : Integrable f) (hg : Integrable g) (x : Space d) :
    scalarConvolution k (f - g) x = scalarConvolution k f x - scalarConvolution k g x := by
  simp only [convolution_right, Pi.sub_apply, mul_sub]
  exact integral_sub (integrable_convolution_right hk hM hf x)
    (integrable_convolution_right hk hM hg x)

/--
Cancellation of a bad piece, without a kernel derivative. Source: DPR, local transcription pp. 9–10
(context).
-/
theorem convolution_cancel {k b : Space d → ℝ}
    (hk : StronglyMeasurable k) {M : ℝ} (hM : ∀ x, ‖k x‖ ≤ M)
    (hb : Integrable b) (hz : (∫ y, b y) = 0) (c x : Space d) :
    scalarConvolution k b x = ∫ y, (k (x - y) - k (x - c)) * b y := by
  simp only [sub_mul]
  rw [integral_sub (integrable_convolution_right hk hM hb x) (hb.const_mul _),
    integral_const_mul, hz, mul_zero, sub_zero, convolution_right]

/--
Markov in extended measure: no conversion of infinite measure to a real number. Source: DPR, local
transcription pp. 9–10 (context).
-/
theorem weak11_measure_level_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {q : α → ℝ} (hq : Integrable q μ) (hn : ∀ x, 0 ≤ q x)
    {lam : ℝ} (hlam : 0 < lam) :
    μ {x | lam < q x} ≤ ENNReal.ofReal ((∫ x, q x ∂μ) / lam) := by
  have h := (hq.div_const lam).measure_le_integral
    (ae_of_all _ (fun x => div_nonneg (hn x) hlam.le))
    (s := {x | lam < q x}) (fun x hx => (le_div_iff₀ hlam).2 (by simpa using hx.le))
  simpa only [integral_div] using h

/--
Chebyshev for the square, with an actual L² assumption. Source: DPR, local transcription pp. 9–10
(context).
-/
theorem measure_norm_level_le_sq {q : Space d → ℝ} (hq : MemLp q 2)
    {lam : ℝ} (hlam : 0 < lam) :
    volume {x | lam < ‖q x‖} ≤ ENNReal.ofReal ((∫ x, q x ^ 2) / lam ^ 2) := by
  have hi := (memLp_two_iff_integrable_sq hq.aestronglyMeasurable).1 hq
  apply (measure_mono (show {x | lam < ‖q x‖} ⊆ {x | lam ^ 2 < q x ^ 2} from ?_)).trans
    (weak11_measure_level_le hi (fun _ => sq_nonneg _) (sq_pos_of_pos hlam))
  intro x hx
  have h := sq_lt_sq₀ hlam.le (norm_nonneg (q x)) |>.2 hx
  simpa only [Set.mem_setOf_eq, Real.norm_eq_abs, sq_abs] using h

/--
Restricted version of Markov, via a measurable indicator. Source: DPR, local transcription pp. 9–10
(context).
-/
theorem measure_norm_level_off_le {q : Space d → ℝ} (hq : Integrable q)
    {E : Set (Space d)} (hE : MeasurableSet E) {lam : ℝ} (hlam : 0 < lam) :
    volume {x | x ∈ E ∧ lam < ‖q x‖} ≤
      ENNReal.ofReal ((∫ x in E, ‖q x‖) / lam) := by
  have h := weak11_measure_level_le (hq.norm.indicator hE)
    (fun x => Set.indicator_nonneg (fun _ _ => norm_nonneg _) x) hlam
  rw [integral_indicator hE] at h
  apply le_trans (measure_mono ?_) h
  intro x hx
  simpa only [Set.mem_setOf_eq, Set.indicator_of_mem hx.1] using hx.2

end GeometricMeasure.CalderonZygmund

namespace GeometricMeasure.CalderonZygmund
variable {d : ℕ}

/--
Change of center in the Hörmander condition. Source: DPR, local transcription pp. 9–10 (context).
-/
theorem hormander_translate {k : Space d → ℝ} {H : ℝ}
    (hH : ∀ h : Space d, (∫ z in {z | 2 * ‖h‖ < ‖z‖}, ‖k (z - h) - k z‖) ≤ H)
    (c y : Space d) :
    (∫ x in {x | 2 * ‖y - c‖ < ‖x - c‖}, ‖k (x - y) - k (x - c)‖) ≤ H := by
  have h := integral_sub_right_eq_self (μ := volume)
    ({z : Space d | 2 * ‖y - c‖ < ‖z‖}.indicator
      (fun z => ‖k (z - (y - c)) - k z‖)) c
  have hm : MeasurableSet {z : Space d | 2 * ‖y - c‖ < ‖z‖} :=
    isOpen_lt continuous_const continuous_norm |>.measurableSet
  have hm' : MeasurableSet {x : Space d | 2 * ‖y - c‖ < ‖x - c‖} :=
    isOpen_lt continuous_const (continuous_id.sub continuous_const).norm |>.measurableSet
  have he : (fun x => ({z : Space d | 2 * ‖y - c‖ < ‖z‖}.indicator
      (fun z => ‖k (z - (y - c)) - k z‖)) (x - c)) =
      {x : Space d | 2 * ‖y - c‖ < ‖x - c‖}.indicator
        (fun x => ‖k (x - y) - k (x - c)‖) := by
    funext x
    simp only [Set.indicator_apply, mem_setOf_eq, sub_sub_sub_cancel_right]
  rw [he, integral_indicator hm', integral_indicator hm] at h
  exact h.le.trans (hH (y - c))

/--
The cancellation estimate on an integrable piece with zero mean. Source: DPR, local transcription
pp. 9–10 (context).
-/
theorem integral_norm_convolution_off_le {k b : Space d → ℝ}
    (hk : StronglyMeasurable k) (hk1 : Integrable k)
    {M : ℝ} (hM : ∀ x, ‖k x‖ ≤ M) {H : ℝ}
    (hH : ∀ h : Space d, (∫ z in {z | 2 * ‖h‖ < ‖z‖}, ‖k (z - h) - k z‖) ≤ H)
    (hb : Integrable b) (hz : (∫ y, b y) = 0) (c : Space d)
    (E : Set (Space d))
    (hfar : ∀ x ∈ E, ∀ y ∈ Function.support b, 2 * ‖y - c‖ < ‖x - c‖) :
    (∫ x in E, ‖scalarConvolution k b x‖) ≤ H * mass b := by
  have hprod : Integrable (fun p : Space d × Space d =>
      (k (p.1 - p.2) - k (p.1 - c)) * b p.2) (volume.prod volume) := by
    have h1 := hb.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hk1
    have h2 := (hk1.comp_sub_right c).mul_prod hb
    apply (h1.sub h2).congr
    exact ae_of_all _ (fun p => by
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Pi.sub_apply]
      ring)
  have hp : Integrable (fun p : Space d × Space d =>
      ‖(k (p.1 - p.2) - k (p.1 - c)) * b p.2‖)
      ((volume.restrict E).prod volume) :=
    hprod.norm.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hy (y : Space d) :
      (∫ x in E, ‖(k (x - y) - k (x - c)) * b y‖) ≤ H * ‖b y‖ := by
    simp only [norm_mul, integral_mul_const]
    by_cases hb0 : b y = 0
    · simp [hb0]
    have hs : y ∈ Function.support b := hb0
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply le_trans _ (hormander_translate hH c y)
    exact integral_mono_measure
      (Measure.restrict_mono (fun x hx => hfar x hx y hs) le_rfl)
      (ae_of_all _ (fun _ => norm_nonneg _))
      (((hk1.comp_sub_right y).sub (hk1.comp_sub_right c)).norm.integrableOn)
  calc
    (∫ x in E, ‖scalarConvolution k b x‖) ≤
        ∫ x in E, ∫ y, ‖(k (x - y) - k (x - c)) * b y‖ := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _)) hp.integral_prod_left
      filter_upwards [] with x
      change ‖scalarConvolution k b x‖ ≤ _
      rw [convolution_cancel hk hM hb hz c x]
      exact norm_integral_le_integral_norm _
    _ = ∫ y, ∫ x in E, ‖(k (x - y) - k (x - c)) * b y‖ :=
      integral_integral_swap hp
    _ ≤ ∫ y, H * ‖b y‖ := integral_mono hp.integral_prod_right (hb.norm.const_mul H) hy
    _ = _ := integral_const_mul _ _

/--
The series of convolutions converges absolutely at every point. Source: DPR, local transcription pp.
9–10 (context).
-/
theorem Decomposition.convolution_summable {f : Space d → ℝ} {lam : ℝ}
    (D : Decomposition d f lam) {k : Space d → ℝ}
    (hk : StronglyMeasurable k) {M : ℝ} (hM : ∀ x, ‖k x‖ ≤ M) (x : Space d) :
    Summable (fun i => ‖scalarConvolution k (D.b i) x‖) := by
  apply (D.bad_summable.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _)
  exact fun i => norm_convolution_le_mass hk hM (D.bad_integrable i) x

/--
Actual interchange of series and convolution; the bound uses M only for a fixed kernel. Source:
DPR, local transcription pp. 9–10 (context).
-/
theorem Decomposition.convolution_tsum {f : Space d → ℝ} {lam : ℝ}
    (D : Decomposition d f lam) {k : Space d → ℝ}
    (hk : StronglyMeasurable k) {M : ℝ} (hM : ∀ x, ‖k x‖ ≤ M) (x : Space d) :
    scalarConvolution k (f - D.g) x = ∑' i, scalarConvolution k (D.b i) x := by
  have hi (i : D.balls.Index) := integrable_convolution_right hk hM (D.bad_integrable i) x
  have hs : Summable (fun i => ∫ y, ‖k (x - y) * D.b i y‖) := by
    apply (D.bad_summable.mul_left M).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    intro i
    calc
      _ ≤ ∫ y, M * ‖D.b i y‖ := by
        apply integral_mono (hi i).norm ((D.bad_integrable i).norm.const_mul M)
        intro y
        dsimp only
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  rw [convolution_right]
  have he : (fun y => k (x - y) * (f - D.g) y) =
      fun y => ∑' i, k (x - y) * D.b i y := by
    funext y
    rw [tsum_mul_left]
    have h := D.pointwise y
    change k (x - y) * (f y - D.g y) = _
    congr 1
    linarith
  rw [he, ← integral_tsum_of_summable_integral_norm hi hs]
  congr 1
  funext i
  exact (convolution_right k (D.b i) x).symm

end GeometricMeasure.CalderonZygmund

namespace GeometricMeasure.CalderonZygmund
variable {d : ℕ}

/--
Summation of the cancellation estimates, with all integrability claims and the series interchange
justified. Source: DPR, local transcription pp. 9–10 (context).
-/
theorem Decomposition.integral_norm_convolution_bad_off_le
    {f : Space d → ℝ} {lam : ℝ} (D : Decomposition d f lam)
    {k : Space d → ℝ} (hk : StronglyMeasurable k) (hk1 : Integrable k)
    {M : ℝ} (hM : ∀ x, ‖k x‖ ≤ M) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : ∀ h : Space d, (∫ z in {z | 2 * ‖h‖ < ‖z‖}, ‖k (z - h) - k z‖) ≤ H) :
    (∫ x in (⋃ i, D.balls.expanded 10 i)ᶜ, ‖scalarConvolution k (f - D.g) x‖) ≤
      2 * H * mass f := by
  let E := (⋃ i, D.balls.expanded 10 i)ᶜ
  have hi (i : D.balls.Index) := integrable_scalarConvolution hk1 (D.bad_integrable i)
  have hib := integrable_scalarConvolution hk1 (D.input_integrable.sub D.good_integrable)
  have hsingle (i : D.balls.Index) :
      (∫ x in E, ‖scalarConvolution k (D.b i) x‖) ≤ H * mass (D.b i) := by
    apply integral_norm_convolution_off_le hk hk1 hM hH (D.bad_integrable i)
      (D.bad_zero i) (D.balls.center i) E
    intro x hx y hy
    simpa only [dist_eq_norm] using D.far_of_mem_support hx i hy
  have hf0 := mass_nonneg f
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2 * H * mass f)).1
  rw [ofReal_integral_eq_lintegral_ofReal hib.norm.integrableOn
    (ae_of_all _ (fun _ => norm_nonneg _))]
  calc
    (∫⁻ x in E, ENNReal.ofReal ‖scalarConvolution k (f - D.g) x‖) ≤
        ∫⁻ x in E, ∑' i, ENNReal.ofReal ‖scalarConvolution k (D.b i) x‖ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [D.convolution_tsum hk hM x, ← ENNReal.ofReal_tsum_of_nonneg
        (fun _ => norm_nonneg _) (D.convolution_summable hk hM x)]
      exact ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm (D.convolution_summable hk hM x))
    _ = ∑' i, ∫⁻ x in E, ENNReal.ofReal ‖scalarConvolution k (D.b i) x‖ :=
      lintegral_tsum (fun i => (hi i).norm.integrableOn.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    _ ≤ ∑' i, ENNReal.ofReal (H * mass (D.b i)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [← ofReal_integral_eq_lintegral_ofReal (hi i).norm.integrableOn
        (ae_of_all _ (fun _ => norm_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (hsingle i)
    _ = ENNReal.ofReal (H * ∑' i, mass (D.b i)) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg hH0 (mass_nonneg _))
        (D.bad_summable.mul_left H), tsum_mul_left]
    _ ≤ ENNReal.ofReal (2 * H * mass f) :=
      ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left D.bad_mass hH0])

end GeometricMeasure.CalderonZygmund

namespace GeometricMeasure.CalderonZygmund
variable {d : ℕ}

/--
Constant of the abstract criterion (40), without the kernel's L¹ and L∞ norms. Source: DPR, local
transcription pp. 9–10 (context).
-/
def weakConstant (d : ℕ) (A H : ℝ) : ℝ :=
  (10 : ℝ) ^ d + 4 * A ^ 2 * (5 : ℝ) ^ d + 4 * H

/--
weak (1,1) criterion for ordinary convolution. Source: DPR, local transcription pp. 9–10 (context).
-/
theorem convolution_weak11 (hd : 1 ≤ d) {k : Space d → ℝ}
    (hk : StronglyMeasurable k) (hk1 : Integrable k)
    (hkB : ∃ M : ℝ, ∀ x, ‖k x‖ ≤ M)
    {A H : ℝ} (_hA : 0 ≤ A) (hH0 : 0 ≤ H)
    (hL2 : ∀ g : Space d → ℝ, Integrable g → MemLp g 2 →
      MemLp (scalarConvolution k g) 2 ∧
      (∫ x, scalarConvolution k g x ^ 2) ≤ A ^ 2 * ∫ x, g x ^ 2)
    (hH : ∀ h : Space d, (∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖k (x - h) - k x‖) ≤ H)
    {f : Space d → ℝ} (hf : Integrable f) {lam : ℝ} (hlam : 0 < lam) :
    volume {x | lam < ‖scalarConvolution k f x‖} ≤
      ENNReal.ofReal (weakConstant d A H * mass f / lam) := by
  have hf0 := mass_nonneg f
  obtain ⟨D⟩ := exists_decomposition hd hf hlam
  obtain ⟨M, hM⟩ := hkB
  let U := ⋃ i, D.balls.expanded 10 i
  have hU : MeasurableSet U := MeasurableSet.iUnion (fun _ => measurableSet_ball)
  have hhalf : 0 < lam / 2 := half_pos hlam
  have hgood := hL2 D.g D.good_integrable D.good_memLp_two
  have hg : volume {x | lam / 2 < ‖scalarConvolution k D.g x‖} ≤
      ENNReal.ofReal ((4 * A ^ 2 * (5 : ℝ) ^ d) * mass f / lam) := by
    apply (measure_norm_level_le_sq hgood.1 hhalf).trans
    apply ENNReal.ofReal_le_ofReal
    have hsq := hgood.2.trans
      (mul_le_mul_of_nonneg_left D.good_square (sq_nonneg A))
    apply (div_le_iff₀ (sq_pos_of_pos hhalf)).2
    calc _ ≤ A ^ 2 * ((5 : ℝ) ^ d * lam * mass f) := hsq
      _ = (4 * A ^ 2 * (5 : ℝ) ^ d * mass f / lam) * (lam / 2) ^ 2 := by
        field_simp
        ring
  have hbad := D.integral_norm_convolution_bad_off_le hk hk1 hM hH0 hH
  have hb : volume {x | x ∈ Uᶜ ∧ lam / 2 < ‖scalarConvolution k (f - D.g) x‖} ≤
      ENNReal.ofReal (4 * H * mass f / lam) := by
    apply (measure_norm_level_off_le (integrable_scalarConvolution hk1
      (hf.sub D.good_integrable)) hU.compl hhalf).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ hhalf).2
    calc _ ≤ 2 * H * mass f := hbad
      _ = (4 * H * mass f / lam) * (lam / 2) := by field_simp; ring
  have hsub : {x | lam < ‖scalarConvolution k f x‖} ⊆
      U ∪ ({x | lam / 2 < ‖scalarConvolution k D.g x‖} ∪
        {x | x ∈ Uᶜ ∧ lam / 2 < ‖scalarConvolution k (f - D.g) x‖}) := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    apply Or.inr
    by_cases hxg : lam / 2 < ‖scalarConvolution k D.g x‖
    · exact Or.inl hxg
    apply Or.inr
    refine ⟨hxU, ?_⟩
    have he : scalarConvolution k f x = scalarConvolution k D.g x +
        scalarConvolution k (f - D.g) x := by
      rw [convolution_sub hk hM hf D.good_integrable x]
      ring
    have hn := norm_add_le (scalarConvolution k D.g x) (scalarConvolution k (f - D.g) x)
    rw [← he] at hn
    exact lt_of_not_ge (fun h => by have := not_lt.mp hxg; change lam < ‖scalarConvolution k f x‖ at hx; linarith)
  calc
    _ ≤ volume (U ∪ ({x | lam / 2 < ‖scalarConvolution k D.g x‖} ∪
        {x | x ∈ Uᶜ ∧ lam / 2 < ‖scalarConvolution k (f - D.g) x‖})) := measure_mono hsub
    _ ≤ volume U + (volume {x | lam / 2 < ‖scalarConvolution k D.g x‖} +
        volume {x | x ∈ Uᶜ ∧ lam / 2 < ‖scalarConvolution k (f - D.g) x‖}) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ENNReal.ofReal ((10 : ℝ) ^ d * mass f / lam) +
        (ENNReal.ofReal ((4 * A ^ 2 * (5 : ℝ) ^ d) * mass f / lam) +
        ENNReal.ofReal (4 * H * mass f / lam)) :=
      add_le_add D.exceptional (add_le_add hg hb)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      unfold weakConstant
      ring

end GeometricMeasure.CalderonZygmund
