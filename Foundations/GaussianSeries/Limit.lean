import Foundations.GaussianSeries.Gram
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Limit

## Main results
Dominated convergence of characteristic functions.
-/

open MeasureTheory ProbabilityTheory Filter WithLp Matrix
open scoped BigOperators Topology

namespace Foundations

variable {Ω ι d : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- an almost sure limit preserves characteristic functions by bounded convergence. -/
theorem tendsto_charFun_map_of_ae_tendsto [IsFiniteMeasure P]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {X : ℕ → Ω → E} {Y : Ω → E} (hX : ∀ N, AEMeasurable (X N) P)
    (hS : ∀ᵐ ω ∂P, Tendsto (fun N => X N ω) atTop (𝓝 (Y ω))) (x : E) :
    Tendsto (fun N => charFun (P.map (X N)) x) atTop (𝓝 (charFun (P.map Y) x)) := by
  have hY := aemeasurable_of_tendsto_metrizable_ae atTop hX hS
  have hc : Continuous (fun y : E => Complex.exp ((inner ℝ y x : ℝ) * Complex.I)) := by fun_prop
  have he {Z : Ω → E} (hZ : AEMeasurable Z P) :
      charFun (P.map Z) x = ∫ ω, Complex.exp ((inner ℝ (Z ω) x : ℝ) * Complex.I) ∂P := by
    rw [charFun_apply, integral_map hZ hc.aestronglyMeasurable]
  simp_rw [he (hX _), he hY]
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro N
    exact (hc.measurable.comp_aemeasurable (hX N)).aestronglyMeasurable
  · exact integrable_const 1
  · intro N
    exact Filter.Eventually.of_forall (fun ω => by rw [Complex.norm_exp_ofReal_mul_I])
  · filter_upwards [hS] with ω hω
    exact hc.continuousAt.tendsto.comp hω

/-- The Euclidean vector of partial sums is almost everywhere measurable. -/
theorem aemeasurable_gaussianSeries_vector [Fintype d] {ξ : ι → Ω → ℝ}
    (hξ : ∀ n, AEMeasurable (ξ n) P) (a : ι → d → ℝ) (F : ℕ → Finset ι) (N : ℕ) :
    AEMeasurable (fun ω => toLp 2 (fun i => gaussianSeriesPartial ξ a F N i ω)) P :=
  (WithLp.measurable_toLp 2 (d → ℝ)).comp_aemeasurable
    (aemeasurable_pi_lambda _ (fun i => aemeasurable_gaussianSeriesPartial hξ a F N i))

/-- Coordinatewise convergence on a finite set gives Euclidean convergence. -/
theorem tendsto_gaussianSeries_vector [Fintype d] {ξ : ι → Ω → ℝ}
    {a : ι → d → ℝ} {F : ℕ → Finset ι} {B : d → Ω → ℝ}
    (hS : ∀ᵐ ω ∂P, ∀ i, Tendsto (fun N => gaussianSeriesPartial ξ a F N i ω) atTop (𝓝 (B i ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun N => toLp 2 (fun i => gaussianSeriesPartial ξ a F N i ω))
      atTop (𝓝 (toLp 2 (fun i => B i ω))) := by
  filter_upwards [hS] with ω hω
  exact (PiLp.continuous_toLp 2 (fun _ : d => ℝ)).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hω)

/-- The limiting vector needs no additional measurability hypothesis. -/
theorem aemeasurable_gaussianSeries_limit [Fintype d] {ξ : ι → Ω → ℝ}
    (hξ : ∀ n, AEMeasurable (ξ n) P) {a : ι → d → ℝ} {F : ℕ → Finset ι} {B : d → Ω → ℝ}
    (hS : ∀ᵐ ω ∂P, ∀ i, Tendsto (fun N => gaussianSeriesPartial ξ a F N i ω) atTop (𝓝 (B i ω))) :
    AEMeasurable (fun ω => toLp 2 (fun i => B i ω)) P :=
  aemeasurable_of_tendsto_metrizable_ae atTop (aemeasurable_gaussianSeries_vector hξ a F)
    (tendsto_gaussianSeries_vector hS)

/-- characteristic function of the limiting Gaussian series. -/
theorem charFun_gaussianSeries_limit [IsFiniteMeasure P] [Fintype d] {ξ : ι → Ω → ℝ}
    (hξ : iIndepFun ξ P) (hLaw : ∀ n, HasLaw (ξ n) (gaussianReal 0 1) P)
    {a : ι → d → ℝ} {F : ℕ → Finset ι} {B : d → Ω → ℝ} {C : Matrix d d ℝ}
    (hC : ∀ i j, Tendsto (fun N => ∑ n ∈ F N, a n i*a n j) atTop (𝓝 (C i j)))
    (hS : ∀ᵐ ω ∂P, ∀ i, Tendsto (fun N => gaussianSeriesPartial ξ a F N i ω) atTop (𝓝 (B i ω)))
    (x : EuclideanSpace ℝ d) :
    charFun (P.map (fun ω => toLp 2 (fun i => B i ω))) x =
      Complex.exp (-((x ⬝ᵥ (C *ᵥ x) : ℝ) : ℂ)/2) := by
  have hlim := tendsto_charFun_map_of_ae_tendsto
    (aemeasurable_gaussianSeries_vector (fun n => (hLaw n).aemeasurable) a F)
    (tendsto_gaussianSeries_vector hS) x
  simp_rw [charFun_gaussianSeriesPartial hξ hLaw] at hlim
  apply tendsto_nhds_unique hlim
  have hc : Continuous (fun r : ℝ => Complex.exp (-(r:ℂ)/2)) := by fun_prop
  exact hc.continuousAt.tendsto.comp (tendsto_gaussianSeries_gram a F C hC x)

end Foundations
