import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Matrix Sqrt Measurable

## Main results
The positive symmetric square root and a single polynomial approximation sequence. The matrix
functional calculus in Mathlib is constructed from the spectral theorem.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder
namespace ErrorCalculus
variable {d : ℕ}

instance matrixMeasurableSpace : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

instance matrixBorelSpace : BorelSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))

/-- Positive symmetric square root, with value zero outside the positive cone. -/
def psdSqrt (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ := CFC.sqrt A

theorem psdSqrt_mul_self {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) :
    psdSqrt A * psdSqrt A = A := CFC.sqrt_mul_sqrt_self A hA.nonneg

theorem psdSqrt_posSemidef (A : Matrix (Fin d) (Fin d) ℝ) :
    (psdSqrt A).PosSemidef := (CFC.sqrt_nonneg A).posSemidef

theorem psdSqrt_isSymm (A : Matrix (Fin d) (Fin d) ℝ) : (psdSqrt A).IsSymm := by
  simpa only [Matrix.isHermitian_iff_isSymm] using
    (psdSqrt_posSemidef A).isHermitian

theorem psdSqrt_eq_zero_of_not_posSemidef {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : ¬ A.PosSemidef) : psdSqrt A = 0 := by
  rw [psdSqrt, CFC.sqrt_eq_cfc]
  exact cfc_apply_of_not_predicate A (fun h => hA h.posSemidef)

theorem psdSqrt_eq_cfc {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) :
    psdSqrt A = cfc Real.sqrt A := by
  rw [psdSqrt, CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ A]
  congr 1
  funext x
  simp only [Real.coe_sqrt, Real.coe_toNNReal']
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
  · rw [max_eq_right (le_of_not_ge hx), Real.sqrt_zero,
      Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx)]

/-- The spectral formula, including repeated and zero eigenvalues. -/
theorem psdSqrt_spectral {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) :
    psdSqrt A = hA.isHermitian.cfc Real.sqrt := by
  rw [psdSqrt_eq_cfc hA, hA.isHermitian.cfc_eq]

/-- Finite spectrum makes pointwise convergence sufficient for matrix functional calculus. -/
theorem matrix_cfc_tendsto {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (h : ∀ i, Tendsto (fun n => f n (hA.eigenvalues i)) atTop
      (𝓝 (g (hA.eigenvalues i)))) :
    Tendsto (fun n => cfc (f n) A) atTop (𝓝 (cfc g A)) := by
  simp only [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have hv := (tendsto_pi_nhds.mpr h)
  have hc : Continuous (fun v : Fin d → ℝ =>
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) * Matrix.diagonal v *
        star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) := by fun_prop
  simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
    hc.continuousAt.tendsto.comp hv

/-- Fixed scalar approximants on expanding intervals; the shift avoids division by zero. -/
def sqrtPolynomial (n : ℕ) : Polynomial ℝ :=
  (exists_polynomial_near_of_continuousOn 0 (n + 1) Real.sqrt
    Real.continuous_sqrt.continuousOn (1 / (n + 1)) (by positivity)).choose

theorem sqrtPolynomial_error (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 ((n : ℝ) + 1)) :
    |(sqrtPolynomial n).eval t - Real.sqrt t| < 1 / (n + 1) :=
  (exists_polynomial_near_of_continuousOn 0 (n + 1) Real.sqrt
    Real.continuous_sqrt.continuousOn (1 / (n + 1)) (by positivity)).choose_spec t ht

theorem sqrtPolynomial_tendsto {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => (sqrtPolynomial n).eval t) atTop (𝓝 (Real.sqrt t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N, hN⟩ := exists_nat_gt t
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (sqrtPolynomial_error n
    ⟨ht, by exact le_trans hN.le (by exact_mod_cast (by omega : N ≤ n + 1))⟩).le

/-- The same polynomials work for every finite dimension and every positive matrix. -/
theorem psdSqrt_eq_lim_polynomial {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) :
    Tendsto (fun n => Polynomial.aeval A (sqrtPolynomial n)) atTop (𝓝 (psdSqrt A)) := by
  rw [psdSqrt_eq_cfc hA]
  have h := matrix_cfc_tendsto hA.isHermitian (f := fun n => (sqrtPolynomial n).eval)
    (fun i => sqrtPolynomial_tendsto (hA.eigenvalues_nonneg i))
  have he : (fun n => cfc ((sqrtPolynomial n).eval) A) =
      (fun n => Polynomial.aeval A (sqrtPolynomial n)) := by
    funext n
    exact cfc_polynomial _ _ hA.isHermitian
  rw [he] at h
  exact h

/-- Entrywise measurability is preserved by the square root on the positive cone.
This proof uses the fixed polynomial sequence, not a choice of measurable eigenvectors. -/
theorem measurable_psdSqrt_comp {α : Type*} [MeasurableSpace α]
    {A : α → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A)
    (hpos : ∀ x, (A x).PosSemidef) : Measurable (fun x => psdSqrt (A x)) := by
  exact measurable_of_tendsto_metrizable
    (fun n => (sqrtPolynomial n).continuous_aeval.measurable.comp hA)
    (tendsto_pi_nhds.mpr fun x => psdSqrt_eq_lim_polynomial (hpos x))

theorem isClosed_posSemidef : IsClosed {A : Matrix (Fin d) (Fin d) ℝ | A.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.setOf_and, Set.setOf_forall]
  exact (isClosed_eq continuous_star continuous_id).inter
    (isClosed_iInter fun v => isClosed_le continuous_const (by fun_prop))

/-- Measurability also includes the prescribed zero value outside the positive cone. -/
theorem measurable_psdSqrt : Measurable (psdSqrt (d := d)) := by
  classical
  let f (n : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) :=
    if A.PosSemidef then Polynomial.aeval A (sqrtPolynomial n) else 0
  apply measurable_of_tendsto_metrizable (f := f)
  · intro n
    exact Measurable.ite (isClosed_posSemidef (d := d)).measurableSet
      (sqrtPolynomial n).continuous_aeval.measurable measurable_const
  · apply tendsto_pi_nhds.mpr
    intro A
    by_cases hA : A.PosSemidef
    · simpa only [f, if_pos hA] using psdSqrt_eq_lim_polynomial hA
    · simpa only [f, if_neg hA, psdSqrt_eq_zero_of_not_posSemidef hA] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Matrix (Fin d) (Fin d) ℝ)) atTop (𝓝 0))

end ErrorCalculus
