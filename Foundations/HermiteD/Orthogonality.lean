import Foundations.HermiteD.Basic

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace
namespace Foundations
variable {ι : Type*} [Fintype ι]

@[simp] theorem hermiteUnit_zero (x : ℝ) : hermiteUnit 0 x = 1 := by
  simp [hermiteUnit, hermiteFun]

theorem integral_hermiteUnit_mul (m n : ℕ) :
    (∫ x, hermiteUnit m x * hermiteUnit n x ∂standardGaussian) = if m = n then 1 else 0 := by
  rw [← orthonormal_iff_ite.mp orthonormal_hermiteNormalized m n, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_hermiteNormalized m, coe_hermiteNormalized n] with x hm hn
  simp [hm, hn, real_inner_comm, mul_comm]

theorem integral_hermiteD_mul (α β : ι → ℕ) :
    (∫ x, hermiteD α x * hermiteD β x ∂gaussianProduct ι) =
      if α = β then ∏ i, ((α i).factorial : ℝ) else 0 := by
  classical
  simp_rw [hermiteD, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => hermiteFun (α i) x * hermiteFun (β i) x)]
  simp_rw [integral_hermite_mul_hermite]
  by_cases h : α = β
  · subst β; simp
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem orthonormal_hermiteNormalizedD :
    Orthonormal ℝ (hermiteNormalizedD : (ι → ℕ) → Lp ℝ 2 (gaussianProduct ι)) := by
  classical
  rw [orthonormal_iff_ite]
  intro α β
  have he : ⟪hermiteNormalizedD α, hermiteNormalizedD β⟫_ℝ =
      ∫ x, hermiteNormalizedFunD α x * hermiteNormalizedFunD β x ∂gaussianProduct ι := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coe_hermiteNormalizedD α, coe_hermiteNormalizedD β] with x hα hβ
    simp [hα,hβ,mul_comm]
  rw [he]
  simp_rw [hermiteNormalizedFunD, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => hermiteUnit (α i) x * hermiteUnit (β i) x)]
  simp_rw [integral_hermiteUnit_mul]
  by_cases h : α = β
  · subst β; simp
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

def hermiteFactorD (α : ι → ℕ) : ℝ := ∏ i, Real.sqrt ((α i).factorial : ℝ)

theorem hermiteFactorD_pos (α : ι → ℕ) : 0 < hermiteFactorD α :=
  Finset.prod_pos fun i _ => Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos _))

theorem hermiteNormalizedFunD_eq (α : ι → ℕ) (x : ι → ℝ) :
    hermiteNormalizedFunD α x = (hermiteFactorD α)⁻¹ * hermiteD α x := by
  simp [hermiteNormalizedFunD, hermiteUnit, hermiteFactorD, hermiteD, Finset.prod_mul_distrib]

theorem hermiteNormalizedD_eq (α : ι → ℕ) :
    hermiteNormalizedD α = (hermiteFactorD α)⁻¹ • hermiteLpD α := by
  apply Lp.ext
  filter_upwards [coe_hermiteNormalizedD α, coe_hermiteLpD α,
    Lp.coeFn_smul (hermiteFactorD α)⁻¹ (hermiteLpD α)] with x hn hh hs
  simp only [hn,hs,Pi.smul_apply,smul_eq_mul,hh,hermiteNormalizedFunD_eq]

theorem hermiteLpD_eq (α : ι → ℕ) :
    hermiteLpD α = hermiteFactorD α • hermiteNormalizedD α := by
  rw [hermiteNormalizedD_eq,smul_smul,mul_inv_cancel₀ (hermiteFactorD_pos α).ne',one_smul]

end Foundations
