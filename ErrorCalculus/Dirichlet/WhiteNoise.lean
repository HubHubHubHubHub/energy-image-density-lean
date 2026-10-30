import Foundations.CameronMartin.GaussianLaw
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# White Noise

## Main results
The real isonormal process, with its Hilbert basis supplied explicitly.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped InnerProductSpace Topology symmDiff
namespace ErrorCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- The auxiliary probability space is the fixed countable Gaussian product. -/
def whiteNoise (b : HilbertBasis ℕ ℝ H) : H →ₗᵢ[ℝ] Lp ℝ 2 Foundations.gaussianInf :=
  Foundations.wienerIntegral.comp b.repr.toLinearIsometry

theorem whiteNoise_hasSum (b : HilbertBasis ℕ ℝ H) (f : H) :
    HasSum (fun n => ⟪b n, f⟫_ℝ • Foundations.gaussianCoordinate n) (whiteNoise b f) := by
  simpa only [whiteNoise, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, HilbertBasis.repr_apply_apply] using Foundations.hasSum_wienerIntegral (b.repr f)

theorem whiteNoise_gaussian (b : HilbertBasis ℕ ℝ H) (f : H) :
    Foundations.gaussianInf.map (whiteNoise b f) =
      gaussianReal 0 ⟨‖f‖^2, sq_nonneg _⟩ := by
  simpa only [whiteNoise, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, b.repr.norm_map, NNReal.mk] using
    Foundations.wienerIntegral_map (b.repr f)

theorem whiteNoise_hasGaussianLaw (b : HilbertBasis ℕ ℝ H) (f : H) :
    HasGaussianLaw (whiteNoise b f) Foundations.gaussianInf :=
  (show HasLaw (whiteNoise b f) (gaussianReal 0 ⟨‖f‖^2, sq_nonneg _⟩)
    Foundations.gaussianInf from ⟨(Lp.aestronglyMeasurable _).aemeasurable,
      whiteNoise_gaussian b f⟩).hasGaussianLaw

theorem whiteNoise_mean (b : HilbertBasis ℕ ℝ H) (f : H) :
    (∫ ω, whiteNoise b f ω ∂Foundations.gaussianInf) = 0 := by
  have h := integral_map (Lp.aestronglyMeasurable (whiteNoise b f)).aemeasurable
    (show AEStronglyMeasurable (fun x : ℝ => x)
      (Foundations.gaussianInf.map (whiteNoise b f)) from aestronglyMeasurable_id)
  rw [whiteNoise_gaussian, integral_id_gaussianReal] at h
  exact h.symm

theorem whiteNoise_cov (b : HilbertBasis ℕ ℝ H) (f g : H) :
    (∫ ω, whiteNoise b f ω * whiteNoise b g ω ∂Foundations.gaussianInf) = ⟪f,g⟫_ℝ := by
  rw [← (whiteNoise b).inner_map_map f g, L2.inner_def]
  congr 1
  funext ω
  simp [mul_comm]

theorem whiteNoise_sq (b : HilbertBasis ℕ ℝ H) (f : H) :
    (∫ ω, (whiteNoise b f ω)^2 ∂Foundations.gaussianInf) = ‖f‖^2 := by
  simpa only [pow_two, real_inner_self_eq_norm_sq] using whiteNoise_cov b f f

theorem whiteNoise_covariance (b : HilbertBasis ℕ ℝ H) (f g : H) :
    cov[whiteNoise b f, whiteNoise b g; Foundations.gaussianInf] = ⟪f,g⟫_ℝ := by
  rw [covariance_eq_sub
    (Lp.memLp _) (Lp.memLp _), whiteNoise_mean, whiteNoise_mean, mul_zero, sub_zero]
  exact whiteNoise_cov b f g

/-- Linear maps carry every convergent Hilbert series to an L² convergent series. -/
theorem whiteNoise_hasSum_map {ι : Type*} (b : HilbertBasis ℕ ℝ H)
    {f : ι → H} {g : H} (h : HasSum f g) :
    HasSum (fun i => whiteNoise b (f i)) (whiteNoise b g) :=
  (whiteNoise b).toContinuousLinearMap.hasSum h

/-- Every finite vector of values is jointly Gaussian, proved by all linear forms. -/
theorem whiteNoise_joint {ι : Type*} [Fintype ι] (b : HilbertBasis ℕ ℝ H)
    (f : ι → H) : HasGaussianLaw (fun ω i => whiteNoise b (f i) ω)
      Foundations.gaussianInf := by
  classical
  constructor
  apply isGaussian_of_isGaussian_map
  intro L
  have hm : AEMeasurable (fun ω i => whiteNoise b (f i) ω) Foundations.gaussianInf :=
    aemeasurable_pi_lambda _ (fun i => (Lp.aestronglyMeasurable _).aemeasurable)
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hm]
  have he : (fun ω => L ((fun i => whiteNoise b (f i) ω))) =ᵐ[Foundations.gaussianInf]
      whiteNoise b (∑ i, L (Pi.single i 1) • f i) := by
    have heq : whiteNoise b (∑ i, L (Pi.single i 1) • f i) =
        ∑ i, L (Pi.single i 1) • whiteNoise b (f i) := by simp
    rw [heq]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i => L (Pi.single i 1) • whiteNoise b (f i)),
      ae_all_iff.mpr (fun i => Lp.coeFn_smul (L (Pi.single i 1)) (whiteNoise b (f i)))]
      with ω hs hc
    rw [hs]
    change L (fun i => whiteNoise b (f i) ω) = _
    conv_lhs => rw [← Finset.univ_sum_single (fun i => whiteNoise b (f i) ω)]
    rw [map_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc i]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show Pi.single i (whiteNoise b (f i) ω) =
      whiteNoise b (f i) ω • Pi.single i (1 : ℝ) by
        ext j
        by_cases hj : j = i <;> simp [hj], map_smul]
    simp [mul_comm]
  change IsGaussian (Foundations.gaussianInf.map (fun ω => L (fun i => whiteNoise b (f i) ω)))
  rw [Measure.map_congr he]
  exact (whiteNoise_hasGaussianLaw b _).isGaussian_map

/-- Joint Gaussianity plus orthogonality gives mutual independence (finite families). -/
theorem whiteNoise_indep_of_orthogonal {ι : Type*}
    (b : HilbertBasis ℕ ℝ H) (f : ι → H)
    (hf : Pairwise (fun i j => ⟪f i, f j⟫_ℝ = 0)) :
    iIndepFun (fun i => whiteNoise b (f i)) Foundations.gaussianInf := by
  rw [iIndepFun_iff_finset]
  intro s
  apply (whiteNoise_joint b (s.restrict f)).iIndepFun_of_covariance_eq_zero
  intro i j hij
  rw [whiteNoise_covariance]
  exact hf (Subtype.coe_injective.ne hij)

/-- The entire indexed isonormal family is a Gaussian process. -/
theorem whiteNoise_isGaussianProcess {ι : Type*} (b : HilbertBasis ℕ ℝ H) (f : ι → H) :
    IsGaussianProcess (fun i => whiteNoise b (f i)) Foundations.gaussianInf where
  hasGaussianLaw s := whiteNoise_joint b (s.restrict f)

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

/-- Values on measurable sets are values at their L² indicator. -/
def whiteNoise_set (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (A : Set E)
    (hA : MeasurableSet A) : Lp ℝ 2 Foundations.gaussianInf :=
  whiteNoise b (indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ))

theorem whiteNoise_associated_measure (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ))
    (A : Set E) (hA : MeasurableSet A) :
    (∫ ω, (whiteNoise_set b A hA ω)^2 ∂Foundations.gaussianInf) = μ.real A := by
  rw [whiteNoise_set, whiteNoise_sq, ← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA)
        (hμs := measure_ne_top μ A) (c := (1 : ℝ))] with x hx
      rw [hx]
      by_cases h : x ∈ A <;> simp [h]
    _ = μ.real A := by rw [integral_indicator hA]; simp

theorem whiteNoise_set_gaussian (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ))
    (A : Set E) (hA : MeasurableSet A) :
    Foundations.gaussianInf.map (whiteNoise_set b A hA) =
      gaussianReal 0 (μ A).toNNReal := by
  rw [whiteNoise_set, whiteNoise_gaussian]
  congr 1
  apply Subtype.ext
  change ‖indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)‖^2 = μ.real A
  rw [← whiteNoise_sq b]
  exact whiteNoise_associated_measure b A hA

/-- Orthogonality of disjoint indicators; no independence assumption is used. -/
theorem whiteNoise_indicator_orthogonal {A B : Set E} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B) :
    ⟪indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ),
      indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)⟫_ℝ = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA)
    (hμs := measure_ne_top μ A) (c := (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (hs := hB)
    (hμs := measure_ne_top μ B) (c := (1 : ℝ))] with x hx hy
  rw [hx, hy]
  have hab := Set.disjoint_left.mp hAB
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp_all

theorem whiteNoise_indep_of_disjoint {ι : Type*}
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (A : ι → Set E)
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A)) :
    iIndepFun (fun i => whiteNoise_set b (A i) (hA i)) Foundations.gaussianInf := by
  apply whiteNoise_indep_of_orthogonal
  intro i j hij
  exact whiteNoise_indicator_orthogonal (hA i) (hA j) (hdisj hij)

/-- Countable additivity in L², stated as convergence of partial sums. -/
theorem whiteNoise_indicator_sigma_additive
    (A : ℕ → Set E) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (Disjoint on A)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      indicatorConstLp 2 (hA n) (measure_ne_top μ _) (1 : ℝ))
      atTop (𝓝 (indicatorConstLp 2 (MeasurableSet.iUnion hA) (measure_ne_top μ _) (1 : ℝ))) := by
  classical
  have hfin (s : Finset ℕ) :
      indicatorConstLp 2 (s.measurableSet_biUnion (fun n _ => hA n))
        (measure_ne_top μ _) (1 : ℝ) =
      ∑ n ∈ s, indicatorConstLp 2 (hA n) (measure_ne_top μ _) (1 : ℝ) := by
    induction s using Finset.induction_on with
    | empty => simp [indicatorConstLp_empty]
    | @insert n s hn ih =>
      have hd : Disjoint (A n) (⋃ i ∈ s, A i) := by
        rw [Set.disjoint_iUnion_right]
        intro i
        rw [Set.disjoint_iUnion_right]
        intro hi
        exact hdisj (by intro he; subst i; exact hn hi)
      simpa only [Finset.set_biUnion_insert, Finset.sum_insert hn] using
        (indicatorConstLp_disjoint_union (p := 2) (hA n)
          (s.measurableSet_biUnion (fun n _ => hA n)) hd
          (hμs := measure_ne_top μ _) (hμt := measure_ne_top μ _) (c := (1 : ℝ))).trans
          (congrArg (fun z => indicatorConstLp 2 (hA n) (measure_ne_top μ _) (1 : ℝ) + z) ih)
  have ht : Tendsto (fun N => μ ((⋃ n ∈ Finset.range N, A n) ∆ (⋃ n, A n)))
      atTop (𝓝 0) := by
    have htail := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
      (μ := μ) (fun n => (hA n).nullMeasurableSet) hdisj
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun _ => bot_le) (fun N => measure_mono (show ((⋃ n ∈ Finset.range N, A n) ∆ (⋃ n, A n)) ⊆
        ⋃ n ∈ Ici N, A n from by
          intro x hx
          simp only [mem_symmDiff, mem_iUnion, Finset.mem_range, mem_Ici] at hx ⊢
          grind))
  have hlim := tendsto_indicatorConstLp_set (p := 2) (μ := μ)
    (hs := MeasurableSet.iUnion hA) (hμs := measure_ne_top μ _)
    (ht := fun N => (Finset.range N).measurableSet_biUnion (fun n _ => hA n))
    (hμt := fun _ => measure_ne_top μ _) (c := (1 : ℝ)) (by norm_num) ht
  simpa only [hfin] using hlim

/-- Countable additivity of the real white noise in L². -/
theorem whiteNoise_sigma_additive (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ))
    (A : ℕ → Set E) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (Disjoint on A)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, whiteNoise_set b (A n) (hA n))
      atTop (𝓝 (whiteNoise_set b (⋃ n, A n) (MeasurableSet.iUnion hA))) := by
  simpa only [Function.comp_def, map_sum, whiteNoise_set] using
    ((whiteNoise b).continuous.tendsto _ |>.comp
      (whiteNoise_indicator_sigma_additive (μ := μ) A hA hdisj))

end ErrorCalculus
