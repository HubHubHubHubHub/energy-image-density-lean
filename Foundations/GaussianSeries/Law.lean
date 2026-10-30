import Foundations.GaussianSeries.Limit
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Law

## Main results
Gaussian laws, Brownian laws on a set, and continuous paths.
-/

open MeasureTheory ProbabilityTheory Filter WithLp Set
open scoped BigOperators Topology NNReal Classical

namespace Foundations

variable {Ω ι d : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- identification of the finite-dimensional law by uniqueness of characteristic functions. -/
theorem gaussianSeries_map_eq_multivariateGaussian [Fintype d] {ξ : ι → Ω → ℝ}
    (hξ : iIndepFun ξ P) (hLaw : ∀ n, HasLaw (ξ n) (gaussianReal 0 1) P)
    {a : ι → d → ℝ} {F : ℕ → Finset ι} {B : d → Ω → ℝ} {C : Matrix d d ℝ}
    (hC : ∀ i j, Tendsto (fun N => ∑ n ∈ F N, a n i*a n j) atTop (𝓝 (C i j)))
    (hS : ∀ᵐ ω ∂P, ∀ i, Tendsto (fun N => gaussianSeriesPartial ξ a F N i ω) atTop (𝓝 (B i ω))) :
    P.map (fun ω => toLp 2 (fun i => B i ω)) = multivariateGaussian 0 C := by
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_gaussianSeries_limit hξ hLaw hC hS,
    charFun_multivariateGaussian (posSemidef_gaussianSeries_limit a F C hC)]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, neg_div]

/-- The law statement also records the measurability obtained from the limit. -/
theorem hasLaw_gaussianSeries_limit [Fintype d] {ξ : ι → Ω → ℝ}
    (hξ : iIndepFun ξ P) (hLaw : ∀ n, HasLaw (ξ n) (gaussianReal 0 1) P)
    {a : ι → d → ℝ} {F : ℕ → Finset ι} {B : d → Ω → ℝ} {C : Matrix d d ℝ}
    (hC : ∀ i j, Tendsto (fun N => ∑ n ∈ F N, a n i*a n j) atTop (𝓝 (C i j)))
    (hS : ∀ᵐ ω ∂P, ∀ i, Tendsto (fun N => gaussianSeriesPartial ξ a F N i ω) atTop (𝓝 (B i ω))) :
    HasLaw (fun ω => toLp 2 (fun i => B i ω)) (multivariateGaussian 0 C) P :=
  ⟨aemeasurable_gaussianSeries_limit (fun n => (hLaw n).aemeasurable) hS,
    gaussianSeries_map_eq_multivariateGaussian hξ hLaw hC hS⟩

/-- arbitrary finite samples of the limiting process have the announced covariance law. -/
theorem hasLaw_gaussianSeries_finite_marginal {τ : Type*} [Fintype d] {ξ : ι → Ω → ℝ}
    (hξ : iIndepFun ξ P) (hLaw : ∀ n, HasLaw (ξ n) (gaussianReal 0 1) P)
    {a : ι → τ → ℝ} {F : ℕ → Finset ι} {B : τ → Ω → ℝ} {T : Set τ} {c : τ → τ → ℝ}
    (hC : ∀ s ∈ T, ∀ t ∈ T, Tendsto (fun N => ∑ n ∈ F N, a n s*a n t) atTop (𝓝 (c s t)))
    (hS : ∀ᵐ ω ∂P, ∀ t ∈ T, Tendsto (fun N => gaussianSeriesPartial ξ a F N t ω) atTop (𝓝 (B t ω)))
    (v : d → τ) (hv : ∀ i, v i ∈ T) :
    HasLaw (fun ω => toLp 2 (fun i => B (v i) ω))
      (multivariateGaussian 0 (fun i j => c (v i) (v j))) P := by
  apply hasLaw_gaussianSeries_limit hξ hLaw (a := fun n i => a n (v i))
    (F := F) (fun i j => hC _ (hv i) _ (hv j))
  filter_upwards [hS] with ω hω
  exact fun i => hω _ (hv i)

/-- finite-dimensional Brownian laws on a set of nonnegative times. -/
def IsPreBrownianOn (T : Set ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ I : Finset ℝ≥0, (↑I : Set ℝ≥0) ⊆ T →
    HasLaw (fun ω => I.restrict (B · ω)) (BrownianReal.projectiveFamily I) P

omit [IsProbabilityMeasure P] in
/-- The local definition agrees with Mathlib's definition when the time set is unrestricted. -/
theorem isPreBrownianOn_univ_iff (B : ℝ≥0 → Ω → ℝ) :
    IsPreBrownianOn univ B P ↔ IsPreBrownianReal B P := by
  constructor
  · intro h
    exact ⟨fun I => h I (subset_univ _)⟩
  · intro h I _
    exact h.hasLaw I

/-- covariance min and almost sure series convergence give Brownian finite-dimensional laws. -/
theorem isPreBrownianOn_of_series {ξ : ι → Ω → ℝ}
    (hξ : iIndepFun ξ P) (hLaw : ∀ n, HasLaw (ξ n) (gaussianReal 0 1) P)
    {a : ι → ℝ≥0 → ℝ} {F : ℕ → Finset ι} {B : ℝ≥0 → Ω → ℝ} {T : Set ℝ≥0}
    (hC : ∀ s ∈ T, ∀ t ∈ T, Tendsto (fun N => ∑ n ∈ F N, a n s*a n t)
      atTop (𝓝 (min (s:ℝ) (t:ℝ))))
    (hS : ∀ᵐ ω ∂P, ∀ t ∈ T, Tendsto (fun N => gaussianSeriesPartial ξ a F N t ω) atTop (𝓝 (B t ω))) :
    IsPreBrownianOn T B P := by
  intro I hIT
  have hc : ∀ i j : I, Tendsto (fun N => ∑ n ∈ F N, a n i.1*a n j.1)
      atTop (𝓝 (BrownianReal.covMatrix I i j)) := by
    intro i j
    exact hC i.1 (hIT i.2) j.1 (hIT j.2)
  have hs : ∀ᵐ ω ∂P, ∀ i : I,
      Tendsto (fun N => gaussianSeriesPartial ξ (fun n (i : I) => a n i.1) F N i ω)
        atTop (𝓝 (B i.1 ω)) := by
    filter_upwards [hS] with ω hω
    exact fun i => hω i.1 (hIT i.2)
  have h := hasLaw_gaussianSeries_limit hξ hLaw hc hs
  exact (BrownianReal.measurePreserving_ofLp_multivariateGaussian I).fun_comp_hasLaw h

/-- Local Brownian laws and almost surely continuous paths. -/
def IsBrownianOn (T : Set ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop :=
  IsPreBrownianOn T B P ∧ ∀ᵐ ω ∂P, ContinuousOn (fun t => B t ω) T

omit [IsProbabilityMeasure P] in
/-- continuity of a series limit follows from uniform convergence on the time set. -/
theorem continuousOn_of_gaussianSeries_uniform {τ : Type*} [TopologicalSpace τ]
    (ξ : ι → Ω → ℝ) {a : ι → τ → ℝ} (F : ℕ → Finset ι) {B : τ → Ω → ℝ} {T : Set τ}
    (ha : ∀ n, ContinuousOn (a n) T)
    (hU : ∀ᵐ ω ∂P, TendstoUniformlyOn (fun N t => gaussianSeriesPartial ξ a F N t ω)
      (fun t => B t ω) atTop T) :
    ∀ᵐ ω ∂P, ContinuousOn (fun t => B t ω) T := by
  filter_upwards [hU] with ω hω
  apply hω.continuousOn
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro N
  exact continuousOn_finsetSum _ (fun n _ => continuousOn_const.mul (ha n))

/-- The abstract uniform series theorem on any set of nonnegative times. -/
theorem isBrownianOn_of_series {ξ : ι → Ω → ℝ}
    (hξ : iIndepFun ξ P) (hLaw : ∀ n, HasLaw (ξ n) (gaussianReal 0 1) P)
    {a : ι → ℝ≥0 → ℝ} {F : ℕ → Finset ι} {B : ℝ≥0 → Ω → ℝ} {T : Set ℝ≥0}
    (ha : ∀ n, ContinuousOn (a n) T)
    (hC : ∀ s ∈ T, ∀ t ∈ T, Tendsto (fun N => ∑ n ∈ F N, a n s*a n t)
      atTop (𝓝 (min (s:ℝ) (t:ℝ))))
    (hU : ∀ᵐ ω ∂P, TendstoUniformlyOn (fun N t => gaussianSeriesPartial ξ a F N t ω)
      (fun t => B t ω) atTop T) : IsBrownianOn T B P := by
  refine ⟨isPreBrownianOn_of_series hξ hLaw hC ?_, continuousOn_of_gaussianSeries_uniform ξ F ha hU⟩
  filter_upwards [hU] with ω hω
  exact fun t ht => hω.tendsto_at ht

end Foundations
