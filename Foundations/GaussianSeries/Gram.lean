import Foundations.GaussianSeries.CharFun

/-! # Finite Gram forms and their positive semidefinite limits. -/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators Topology

namespace Foundations

variable {ι d : Type*} [Fintype d]

/-- Expansion of the finite Gram quadratic form. -/
theorem gaussianSeries_gram_identity (a : ι → d → ℝ) (F : Finset ι) (x : d → ℝ) :
    ∑ n ∈ F, (∑ i, x i * a n i)^2 =
      ∑ i, ∑ j, x i * x j * (∑ n ∈ F, a n i * a n j) := by
  calc
    _ = ∑ n ∈ F, ∑ i, ∑ j, x i*x j*(a n i*a n j) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

/-- Coordinate expansion of the quadratic form used by Mathlib's Gaussian law. -/
theorem gaussianSeries_matrix_quadratic (C : Matrix d d ℝ) (x : d → ℝ) :
    x ⬝ᵥ (C *ᵥ x) = ∑ i, ∑ j, x i*x j*C i j := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Entrywise covariance convergence implies convergence of every finite quadratic form. -/
theorem tendsto_gaussianSeries_gram (a : ι → d → ℝ) (F : ℕ → Finset ι) (C : Matrix d d ℝ)
    (hC : ∀ i j, Tendsto (fun N => ∑ n ∈ F N, a n i*a n j) atTop (𝓝 (C i j))) (x : d → ℝ) :
    Tendsto (fun N => ∑ n ∈ F N, (∑ i, x i*a n i)^2) atTop (𝓝 (x ⬝ᵥ (C *ᵥ x))) := by
  simp_rw [gaussianSeries_gram_identity, gaussianSeries_matrix_quadratic]
  exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => (hC i j).const_mul _))

/-- a limit of finite Gram covariance matrices is positive semidefinite. -/
theorem posSemidef_gaussianSeries_limit (a : ι → d → ℝ) (F : ℕ → Finset ι) (C : Matrix d d ℝ)
    (hC : ∀ i j, Tendsto (fun N => ∑ n ∈ F N, a n i*a n j) atTop (𝓝 (C i j))) :
    C.PosSemidef := by
  have hsym (i j : d) : C i j = C j i := by
    apply tendsto_nhds_unique (hC i j)
    simpa only [mul_comm] using hC j i
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using hsym j i
  · intro x
    simp only [star_trivial]
    exact ge_of_tendsto (tendsto_gaussianSeries_gram a F C hC x)
      (Filter.Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end Foundations
