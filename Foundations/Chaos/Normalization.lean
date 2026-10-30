import Foundations.Chaos.Basis

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace Foundations

/-- The product normalisation is exactly the square root of the multi-factorial. -/
theorem hermiteFactorD_eq_sqrt {ι : Type*} [Fintype ι] (α : ι → ℕ) :
    hermiteFactorD α = Real.sqrt (∏ i, ((α i).factorial : ℝ)) := by
  exact (Real.sqrt_prod Finset.univ (fun _ _ => Nat.cast_nonneg _)).symm

theorem hermiteFactorInf_eq_sqrt (α : ℕ →₀ ℕ) :
    hermiteFactorInf α = Real.sqrt (α.prod (fun _ n => (n.factorial : ℝ))) := by
  exact (Real.sqrt_prod α.support (fun _ _ => Nat.cast_nonneg _)).symm

def hermiteLpInf (α : ℕ →₀ ℕ) : Lp ℝ 2 gaussianInf := (memLp_hermiteInfFun α).toLp _

theorem coe_hermiteLpInf (α : ℕ →₀ ℕ) : hermiteLpInf α =ᵐ[gaussianInf] hermiteInfFun α :=
  (memLp_hermiteInfFun α).coeFn_toLp

theorem hermiteInf_eq_normalized (α : ℕ →₀ ℕ) :
    hermiteInf α = (hermiteFactorInf α)⁻¹ • hermiteLpInf α := by
  apply Lp.ext
  filter_upwards [coe_hermiteInf α,coe_hermiteLpInf α,
    Lp.coeFn_smul (hermiteFactorInf α)⁻¹ (hermiteLpInf α)] with x hn hh hs
  simp only [hn,hs,Pi.smul_apply,smul_eq_mul,hh,hermiteNormalizedFunInf_eq]

theorem hermiteInf_coeff_eq_integral (f : Lp ℝ 2 gaussianInf) (α : ℕ →₀ ℕ) :
    hermiteInf_coeff f α = (hermiteFactorInf α)⁻¹ *
      ∫ x, f x * hermiteInfFun α x ∂gaussianInf := by
  rw [hermiteInf_coeff,hermiteInf_eq_normalized,inner_smul_right]
  congr 1
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_hermiteLpInf α] with x hx
  simp [hx,mul_comm]

theorem hermite_completeInf_raw (f : Lp ℝ 2 gaussianInf)
    (hf : ∀ α, ⟪f,hermiteLpInf α⟫_ℝ = 0) : f = 0 := by
  apply hermite_completeInf
  intro α
  rw [hermiteInf_eq_normalized,inner_smul_right,hf,mul_zero]

end Foundations
