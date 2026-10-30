import ErrorCalculus.Dirichlet.MatrixSqrtMeasurable

/-!
# Matrix Functional Measurable

## Main results
Measurable functional calculus for continuous scalar functions on real symmetric matrices.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder
namespace ErrorCalculus
variable {d : ℕ}

/-- Weierstrass approximants on symmetric expanding intervals. -/
def functionalPolynomial (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) : Polynomial ℝ :=
  (exists_polynomial_near_of_continuousOn (-(n + 1)) (n + 1) f
    hf.continuousOn (1 / (n + 1)) (by positivity)).choose

theorem functionalPolynomial_tendsto (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
    Tendsto (fun n => (functionalPolynomial f hf n).eval t) atTop (𝓝 (f t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N, hN⟩ := exists_nat_gt |t|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hb : |t| ≤ (n : ℝ) + 1 := hN.le.trans (by exact_mod_cast (by omega : N ≤ n + 1))
  exact ((exists_polynomial_near_of_continuousOn (-(n + 1)) (n + 1) f
    hf.continuousOn (1 / (n + 1)) (by positivity)).choose_spec t (abs_le.mp hb)).le

theorem measurable_matrix_cfc (f : ℝ → ℝ) (hf : Continuous f) :
    Measurable (fun A : Matrix (Fin d) (Fin d) ℝ => cfc f A) := by
  classical
  let g (n : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) :=
    if A.IsHermitian then Polynomial.aeval A (functionalPolynomial f hf n) else 0
  apply measurable_of_tendsto_metrizable (f := g)
  · intro n
    exact Measurable.ite (isClosed_eq continuous_star continuous_id).measurableSet
      (functionalPolynomial f hf n).continuous_aeval.measurable measurable_const
  · apply tendsto_pi_nhds.mpr
    intro A
    by_cases hA : A.IsHermitian
    · have ht := matrix_cfc_tendsto hA (f := fun n => (functionalPolynomial f hf n).eval) (g := f) (fun i => functionalPolynomial_tendsto f hf (hA.eigenvalues i))
      have he : (fun n => cfc ((functionalPolynomial f hf n).eval) A) = (fun n => g n A) := by
        funext n
        simp only [g, if_pos hA]
        exact cfc_polynomial _ _ hA
      rwa [he] at ht
    · rw [cfc_apply_of_not_predicate (p := IsSelfAdjoint) (f := f) A hA]
      simp only [g, if_neg hA]
      exact tendsto_const_nhds

/-- Every function is continuous on the finite spectrum of a real matrix. -/
theorem matrix_continuousOn_spectrum (A : Matrix (Fin d) (Fin d) ℝ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) := by
  rw [continuousOn_iff_continuous_restrict]
  fun_prop

/-- Multiplication under the finite spectral calculus, including discontinuous scalar functions. -/
theorem matrix_cfc_mul (A : Matrix (Fin d) (Fin d) ℝ) (f g : ℝ → ℝ) :
    cfc f A * cfc g A = cfc (fun t => f t * g t) A :=
  (cfc_mul f g A (matrix_continuousOn_spectrum A f) (matrix_continuousOn_spectrum A g)).symm

end ErrorCalculus
