import Foundations.Hermite.Span
import Foundations.Hermite.Complete

noncomputable section
open Filter Topology Set MeasureTheory Polynomial
open scoped InnerProductSpace
namespace Foundations

theorem orthogonal_span_hermite_eq_bot :
    (Submodule.span ℝ (range hermiteLp))ᗮ = ⊥ := by
  apply bot_unique
  intro f hf
  change f = 0
  apply Lp.ext
  have hh : ∀ n, ⟪f, hermiteLp n⟫_ℝ = 0 := fun n =>
    (Submodule.mem_orthogonal' _ _).mp hf _ (Submodule.subset_span (mem_range_self n))
  have hz := hermite_complete (Lp.memLp f) ((hermite_inner_eq_zero_iff_moments f).mp hh)
  filter_upwards [hz, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := standardGaussian)] with x hx h0
  simpa [h0] using hx

theorem dense_span_hermite :
    (Submodule.span ℝ (range hermiteLp)).topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, orthogonal_span_hermite_eq_bot,
    Submodule.bot_orthogonal_eq_top]

def hermiteBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 standardGaussian) :=
  HilbertBasis.mk orthonormal_hermiteNormalized
    (by rw [span_hermiteNormalized_eq, dense_span_hermite])

@[simp] theorem hermiteBasis_apply (n : ℕ) : hermiteBasis n = hermiteNormalized n :=
  congrFun (HilbertBasis.coe_mk _ _) n

def hermite_coeff (f : Lp ℝ 2 standardGaussian) (n : ℕ) : ℝ := ⟪f, hermiteNormalized n⟫_ℝ

theorem hermite_coeff_eq_integral (f : Lp ℝ 2 standardGaussian) (n : ℕ) :
    hermite_coeff f n = (Real.sqrt (n.factorial : ℝ))⁻¹ *
      ∫ x, f x * hermiteFun n x ∂standardGaussian := by
  rw [hermite_coeff, hermiteNormalized, inner_smul_right]
  congr 1
  exact inner_polynomialLp f (hermitePolynomial n)

theorem hasSum_hermite_expansion (f : Lp ℝ 2 standardGaussian) :
    HasSum (fun n => hermite_coeff f n • hermiteNormalized n) f := by
  simpa [HilbertBasis.repr_apply_apply, hermite_coeff, real_inner_comm] using hermiteBasis.hasSum_repr f

theorem tsum_hermite_expansion (f : Lp ℝ 2 standardGaussian) :
    ∑' n, hermite_coeff f n • hermiteNormalized n = f := (hasSum_hermite_expansion f).tsum_eq

theorem sum_sq_hermite_coeff (f : Lp ℝ 2 standardGaussian) :
    ∑' n, (hermite_coeff f n)^2 = ‖f‖^2 := by
  simpa [pow_two, hermite_coeff, real_inner_comm, real_inner_self_eq_norm_sq] using
    hermiteBasis.tsum_inner_mul_inner f f

theorem dense_polynomials_gaussian : Dense (range polynomialLp) := by
  change Dense (range (polynomialLpLinear : ℝ[X] → Lp ℝ 2 standardGaussian))
  rw [← LinearMap.coe_range polynomialLpLinear]
  rw [← span_hermiteLp_eq_polynomial_range]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr dense_span_hermite

end Foundations
