import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

namespace Foundations

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Chernoff bound for the upper tail of a standard normal random variable. -/
theorem gaussianReal_upper_tail_le {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 1) P) {x : ℝ} (hx : 0 ≤ x) :
    P {ω | x ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-x^2 / 2)) := by
  have hi : Integrable (fun ω => Real.exp (x * X ω)) P := by
    rw [← mgf_pos_iff, mgf_gaussianReal hX.map_eq]
    exact Real.exp_pos _
  have h := measure_ge_le_exp_mul_mgf x hx hi
  rw [mgf_gaussianReal hX.map_eq] at h
  simp only [zero_mul, NNReal.coe_one, one_mul, zero_add] at h
  rw [← Real.exp_add] at h
  have he : -x * x + x ^ 2 / 2 = -x^2 / 2 := by ring
  rw [he] at h
  rw [← ofReal_measureReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal h

/-- Two-sided Gaussian tail, obtained by Chernoff and symmetry. -/
theorem gaussianReal_tail_le {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 1) P) {x : ℝ} (hx : 0 ≤ x) :
    P {ω | x ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-x^2 / 2)) := by
  have hn : HasLaw (fun ω => -X ω) (gaussianReal 0 1) P := by
    simpa only [Pi.neg_def, neg_zero] using gaussianReal_neg hX
  have hs : {ω | x ≤ |X ω|} = {ω | x ≤ X ω} ∪ {ω | x ≤ -X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [hs]
  calc
    _ ≤ P {ω | x ≤ X ω} + P {ω | x ≤ -X ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-x^2 / 2)) +
        ENNReal.ofReal (Real.exp (-x^2 / 2)) :=
      add_le_add (gaussianReal_upper_tail_le hX hx) (gaussianReal_upper_tail_le hn hx)
    _ = _ := by rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; congr 1; ring

end Foundations
