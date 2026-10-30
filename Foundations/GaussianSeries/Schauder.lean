import Foundations.GaussianSeries.Law
import Foundations.Haar.Covariance

/-!
# Schauder

## Main results
Conditional specialization to the level exhaustion of Haar–Schauder.
-/

open MeasureTheory ProbabilityTheory Filter WithLp Set
open scoped BigOperators Topology NNReal Classical

namespace Foundations

/-- a constant coordinate, followed by the finite Haar levels. -/
abbrev SchauderIndex := Option (Σ j : ℕ, Fin (2^j))

/-- The exhaustion consists of the constant coordinate and exactly the levels j<N. -/
noncomputable def schauderIndices (N : ℕ) : Finset SchauderIndex :=
  insert none (((Finset.range N).sigma (fun _ => Finset.univ : (j : ℕ) → Finset (Fin (2^j)))).map
    Function.Embedding.some)

/-- The constant coordinate is present even at level zero. -/
@[simp] theorem none_mem_schauderIndices (N : ℕ) : none ∈ schauderIndices N := by
  simp [schauderIndices]

/-- An indexed Haar coordinate is present exactly when its level is below N. -/
@[simp] theorem some_mem_schauderIndices (N j : ℕ) (k : Fin (2^j)) :
    some ⟨j,k⟩ ∈ schauderIndices N ↔ j < N := by
  simp [schauderIndices]

/-- The finite sets form an increasing sequence. -/
theorem monotone_schauderIndices : Monotone schauderIndices := by
  intro N M hNM i hi
  cases i with
  | none => simp
  | some p =>
    rw [some_mem_schauderIndices] at hi ⊢
    exact lt_of_lt_of_le hi hNM

/-- The level sets exhaust all coordinates. -/
theorem exists_mem_schauderIndices (i : SchauderIndex) : ∃ N, i ∈ schauderIndices N := by
  cases i with
  | none => exact ⟨0, by simp⟩
  | some p =>
    rcases p with ⟨j,k⟩
    exact ⟨j+1, by simp⟩

/-- The deterministic coefficient, on nonnegative times. -/
noncomputable def schauderCoefficient : SchauderIndex → ℝ≥0 → ℝ
  | none, t => t
  | some p, t => schauder p.1 p.2 t

/-- Every deterministic Schauder coefficient is continuous. -/
theorem continuous_schauderCoefficient (i : SchauderIndex) : Continuous (schauderCoefficient i) := by
  cases i with
  | none => exact NNReal.continuous_coe
  | some p => exact (continuous_schauder p.1 p.2).comp NNReal.continuous_coe

/-- Reindexing a sum along the explicit level exhaustion. -/
theorem sum_schauderIndices (N : ℕ) (f : SchauderIndex → ℝ) :
    ∑ i ∈ schauderIndices N, f i = f none +
      ∑ j ∈ Finset.range N, ∑ k : Fin (2^j), f (some ⟨j,k⟩) := by
  simp [schauderIndices, Finset.sum_sigma]

/-- The covariance of the level exhaustion equals the finite Haar–Schauder covariance sum. -/
theorem sum_schauderCoefficient_mul (N : ℕ) (s t : ℝ≥0) :
    ∑ i ∈ schauderIndices N, schauderCoefficient i s * schauderCoefficient i t =
      schauderSum N s t := by
  rw [sum_schauderIndices]
  simp only [schauderCoefficient, schauderSum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact Fin.sum_univ_eq_sum_range (fun k => schauder j k s * schauder j k t) (2^j)

/-- For s, t ∈ [0, 1], the finite Haar–Schauder covariance sums converge to min(s, t). -/
theorem tendsto_schauderCoefficient_covariance {s t : ℝ≥0}
    (hs : s ∈ Icc (0:ℝ≥0) 1) (ht : t ∈ Icc (0:ℝ≥0) 1) :
    Tendsto (fun N => ∑ i ∈ schauderIndices N, schauderCoefficient i s * schauderCoefficient i t)
      atTop (𝓝 (min (s:ℝ) (t:ℝ))) := by
  simp_rw [sum_schauderCoefficient_mul]
  exact tendsto_schauderSum ⟨s.coe_nonneg, by exact_mod_cast hs.2⟩
    ⟨t.coe_nonneg, by exact_mod_cast ht.2⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/--
The random partial sum expressed as a constant-coordinate term followed by the finite Haar levels.
-/
theorem gaussianSeriesPartial_schauder (ξ : SchauderIndex → Ω → ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    gaussianSeriesPartial ξ schauderCoefficient schauderIndices N t ω =
      ξ none ω * (t:ℝ) + ∑ j ∈ Finset.range N, ∑ k : Fin (2^j), ξ (some ⟨j,k⟩) ω * schauder j k t := by
  rw [gaussianSeriesPartial, sum_schauderIndices]
  rfl

/-- conditional Brownian finite-dimensional laws for the Schauder series. -/
theorem isPreBrownianOn_of_schauder_series {ξ : SchauderIndex → Ω → ℝ}
    (hξ : iIndepFun ξ P) (hLaw : ∀ n, HasLaw (ξ n) (gaussianReal 0 1) P)
    {B : ℝ≥0 → Ω → ℝ}
    (hS : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0:ℝ≥0) 1,
      Tendsto (fun N => gaussianSeriesPartial ξ schauderCoefficient schauderIndices N t ω)
        atTop (𝓝 (B t ω))) : IsPreBrownianOn (Icc 0 1) B P := by
  exact isPreBrownianOn_of_series hξ hLaw
    (fun _ hs _ ht => tendsto_schauderCoefficient_covariance hs ht) hS

/--
Independent standard Gaussian coefficients and almost-sure uniform convergence of the Haar–Schauder
series on [0, 1] give a Brownian process on [0, 1].
-/
theorem isBrownianOn_of_schauder_series {ξ : SchauderIndex → Ω → ℝ}
    (hξ : iIndepFun ξ P) (hLaw : ∀ n, HasLaw (ξ n) (gaussianReal 0 1) P)
    {B : ℝ≥0 → Ω → ℝ}
    (hU : ∀ᵐ ω ∂P, TendstoUniformlyOn
      (fun N t => gaussianSeriesPartial ξ schauderCoefficient schauderIndices N t ω)
      (fun t => B t ω) atTop (Icc (0:ℝ≥0) 1)) : IsBrownianOn (Icc 0 1) B P := by
  exact isBrownianOn_of_series hξ hLaw (fun n => (continuous_schauderCoefficient n).continuousOn)
    (fun _ hs _ ht => tendsto_schauderCoefficient_covariance hs ht) hU

end Foundations
