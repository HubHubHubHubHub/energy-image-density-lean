import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic

/-!
# Char Fun

## Main results
Characteristic functions of finite Gaussian series.
-/

open MeasureTheory ProbabilityTheory Filter WithLp
open scoped BigOperators Topology

namespace Foundations

variable {Ω ι τ d : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- partial sums along an arbitrary sequence of finite sets. -/
noncomputable def gaussianSeriesPartial (ξ : ι → Ω → ℝ) (a : ι → τ → ℝ)
    (F : ℕ → Finset ι) (N : ℕ) (t : τ) (ω : Ω) : ℝ := ∑ n ∈ F N, ξ n ω * a n t

/-- Every finite partial sum is almost everywhere measurable. -/
theorem aemeasurable_gaussianSeriesPartial {ξ : ι → Ω → ℝ}
    (hξ : ∀ n, AEMeasurable (ξ n) P) (a : ι → τ → ℝ) (F : ℕ → Finset ι) (N : ℕ) (t : τ) :
    AEMeasurable (gaussianSeriesPartial ξ a F N t) P := by
  unfold gaussianSeriesPartial
  fun_prop

/-- product formula for a finite linear combination of standard independent Gaussians. -/
theorem charFun_gaussian_weighted_sum {ξ : ι → Ω → ℝ}
    (hξ : iIndepFun ξ P) (hLaw : ∀ n, HasLaw (ξ n) (gaussianReal 0 1) P)
    (F : Finset ι) (c : ι → ℝ) (u : ℝ) :
    charFun (P.map (fun ω => ∑ n ∈ F, c n * ξ n ω)) u =
      Complex.exp (-((∑ n ∈ F, (c n*u)^2 : ℝ) : ℂ)/2) := by
  have hind : iIndepFun (fun n ω => c n * ξ n ω) P := hξ.comp (fun n y => c n*y) (by fun_prop)
  have hm (n : ι) : AEMeasurable (fun ω => c n * ξ n ω) P := (hLaw n).aemeasurable.const_mul _
  rw [(hind.restrict F).charFun_map_fun_finsetSum_eq_prod (fun n _ => hm n)]
  simp only [Finset.prod_apply]
  simp_rw [charFun_map_mul_comp (hLaw _).aemeasurable, (hLaw _).map_eq, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, NNReal.coe_one, Complex.ofReal_one, mul_zero, zero_mul,
    one_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_mul,
    Finset.sum_neg_distrib, ← Finset.sum_div, neg_div]

/-- Characteristic functions of finite-dimensional laws are scalar characteristic functions. -/
theorem charFun_map_toLp_eq_scalar [Fintype d] {X : Ω → d → ℝ}
    (hX : AEMeasurable X P) (x : EuclideanSpace ℝ d) :
    charFun (P.map (fun ω => toLp 2 (X ω))) x =
      charFun (P.map (fun ω => ∑ l, x l * X ω l)) 1 := by
  have hL : AEMeasurable (fun ω => toLp 2 (X ω)) P :=
    (WithLp.measurable_toLp 2 (d → ℝ)).comp_aemeasurable hX
  have hR : AEMeasurable (fun ω => ∑ l, x l * X ω l) P := by fun_prop
  rw [charFun_apply, integral_map hL (by fun_prop), charFun_apply_real,
    integral_map hR (by fun_prop)]
  simp [PiLp.inner_apply, mul_comm]

/-- vector partial sums have the finite Gram characteristic function. -/
theorem charFun_gaussianSeriesPartial [Fintype d] {ξ : ι → Ω → ℝ}
    (hξ : iIndepFun ξ P) (hLaw : ∀ n, HasLaw (ξ n) (gaussianReal 0 1) P)
    (a : ι → d → ℝ) (F : ℕ → Finset ι) (N : ℕ) (x : EuclideanSpace ℝ d) :
    charFun (P.map (fun ω => toLp 2 (fun l => gaussianSeriesPartial ξ a F N l ω))) x =
      Complex.exp (-((∑ n ∈ F N, (∑ l, x l * a n l)^2 : ℝ) : ℂ)/2) := by
  rw [charFun_map_toLp_eq_scalar (by
    exact aemeasurable_pi_lambda _ (fun l =>
      aemeasurable_gaussianSeriesPartial (fun n => (hLaw n).aemeasurable) a F N l))]
  have he : (fun ω => ∑ l, x l * gaussianSeriesPartial ξ a F N l ω) =
      (fun ω => ∑ n ∈ F N, (∑ l, x l * a n l) * ξ n ω) := by
    funext ω
    simp only [gaussianSeriesPartial, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [he, charFun_gaussian_weighted_sum hξ hLaw]
  simp only [mul_one]

end Foundations
