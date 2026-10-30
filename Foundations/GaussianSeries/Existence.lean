import Foundations.GaussianSeries.Uniform
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Foundations

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Lévy--Ciesielski: Gaussian independent coefficients produce a Brownian motion on `[0,1]`.
There is no remaining convergence assumption. -/
theorem isBrownianOn_schauderSeriesLimit {ξ : SchauderIndex → Ω → ℝ}
    (hξ : iIndepFun ξ P) (hLaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P) :
    IsBrownianOn (Icc 0 1) (schauderSeriesLimit ξ) P :=
  isBrownianOn_of_schauder_series hξ hLaw (ae_tendstoUniformlyOn_schauder_series hLaw)

/-- The canonical probability space of independent standard normal coefficients. -/
noncomputable def schauderGaussianMeasure : Measure (SchauderIndex → ℝ) :=
  Measure.infinitePi (fun _ => gaussianReal 0 1)

instance : IsProbabilityMeasure schauderGaussianMeasure := by
  unfold schauderGaussianMeasure
  infer_instance

/-- On the canonical product space the explicit series limit is Brownian on `[0,1]`. -/
theorem isBrownianOn_schauderSeriesLimit_infinitePi :
    IsBrownianOn (Icc 0 1) (schauderSeriesLimit (fun i ω => ω i)) schauderGaussianMeasure := by
  apply isBrownianOn_schauderSeriesLimit
  · exact iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  · intro i
    exact (measurePreserving_eval_infinitePi (fun _ : SchauderIndex => gaussianReal 0 1) i).hasLaw

/-- Existence of a continuous Brownian motion on `[0,1]`, on the countable Gaussian product. -/
theorem exists_isBrownianOn_Icc :
    ∃ B : ℝ≥0 → (SchauderIndex → ℝ) → ℝ,
      IsBrownianOn (Icc 0 1) B (Measure.infinitePi (fun _ => gaussianReal 0 1)) :=
  ⟨schauderSeriesLimit (fun i ω => ω i), isBrownianOn_schauderSeriesLimit_infinitePi⟩

omit [MeasurableSpace Ω] in
/-- The series starts at zero for every sample, including the exceptional set. -/
@[simp] theorem schauderSeriesLimit_zero (ξ : SchauderIndex → Ω → ℝ) (ω : Ω) :
    schauderSeriesLimit ξ 0 ω = 0 := by
  simp [schauderSeriesLimit, schauderLevelSum, schauder]

omit [IsProbabilityMeasure P] in
/-- Evaluation of a local pre-Brownian motion has its prescribed Gaussian law. -/
theorem IsPreBrownianOn.hasLaw_eval {T : Set ℝ≥0} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianOn T B P) {t : ℝ≥0} (ht : t ∈ T) :
    HasLaw (B t) (gaussianReal 0 t) P := by
  classical
  exact (BrownianReal.measurePreserving_eval_projectiveFamily ⟨t, by simp⟩).hasLaw.comp
    (hB {t} (by simpa using ht))

/-- One-time marginals of the series limit, including both endpoints. -/
theorem hasLaw_schauderSeriesLimit {ξ : SchauderIndex → Ω → ℝ}
    (hξ : iIndepFun ξ P) (hLaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P)
    {t : ℝ≥0} (ht : t ≤ 1) :
    HasLaw (schauderSeriesLimit ξ t) (gaussianReal 0 t) P :=
  (isBrownianOn_schauderSeriesLimit hξ hLaw).1.hasLaw_eval ⟨zero_le, ht⟩

end Foundations
