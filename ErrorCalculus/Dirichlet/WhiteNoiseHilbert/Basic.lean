import ErrorCalculus.Dirichlet.ImageCalculus
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Tactic
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# White noise on a Hilbert space

This file contains the results of the development of `ErrorCalculus.Dirichlet.WhiteNoiseHilbert`
that the main statements of the library (the head theorems listed in the README of the repository)
use. `ErrorCalculus.Dirichlet.WhiteNoiseHilbert` imports it and continues the development.

## Main statements

* `l2_integral_norm_sq`: For `f : Lp K 2 μ` with values in a real Hilbert space `K`, `∫ x, ‖f x‖ ^ 2
  ∂μ = ‖f‖ ^ 2`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped InnerProductSpace Topology ENNReal
namespace ErrorCalculus

variable {E K : Type*} [MeasurableSpace E] {μ : Measure E}
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

theorem l2_integral_norm_sq (f : Lp K 2 μ) :
    (∫ x, ‖f x‖^2 ∂μ) = ‖f‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

end ErrorCalculus
