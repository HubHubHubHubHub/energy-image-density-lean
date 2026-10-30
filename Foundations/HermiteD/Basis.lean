import Foundations.HermiteD.Uniqueness

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace Foundations
variable {ι : Type*} [Fintype ι]

theorem gaussianDot_dual [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    gaussianDot (fun i => L (Pi.single i 1)) x = L x := by
  classical
  rw [gaussianDot, ← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => ℝ) L x]
  apply Finset.sum_congr rfl
  intro i _
  change L (Pi.single i 1) * x i = L (Pi.single i (x i))
  rw [mul_comm]
  have hs : Pi.single i (x i) = x i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
    ext j
    by_cases h : j = i <;> simp [Pi.single_apply,h]
  rw [hs,map_smul]
  rfl

/-- Finite-dimensional completeness, by polynomial moments and uniqueness of charFunDual. -/
theorem hermite_completeD (f : Lp ℝ 2 (gaussianProduct ι))
    (hf : ∀ α : ι → ℕ, ⟪f,hermiteLpD α⟫_ℝ = 0) : f = 0 := by
  classical
  have hz : (fun x => f x) =ᵐ[gaussianProduct ι] 0 := by
    apply ae_eq_zero_of_integral_mul_dualCharacter_eq_zero ((Lp.memLp f).integrable (by norm_num))
    intro L
    simpa only [gaussianDot_dual] using integral_mul_exp_gaussianDot_eq_zero (Lp.memLp f)
      (integral_mul_mvPolynomial_eq_zero f hf) (fun i => L (Pi.single i 1))
  apply Lp.ext
  filter_upwards [hz,Lp.coeFn_zero (E := ℝ) (p := 2) (μ := gaussianProduct ι)] with x hx h0
  simpa [h0] using hx

theorem orthogonal_span_hermiteNormalizedD_eq_bot :
    (Submodule.span ℝ (range (hermiteNormalizedD : (ι → ℕ) → Lp ℝ 2 (gaussianProduct ι))))ᗮ = ⊥ := by
  apply bot_unique
  intro f hf
  change f = 0
  apply hermite_completeD
  intro α
  rw [hermiteLpD_eq,inner_smul_right]
  have hz := (Submodule.mem_orthogonal' _ _).mp hf _
    (Submodule.subset_span (mem_range_self α))
  rw [hz,mul_zero]

theorem dense_span_hermiteD :
    (Submodule.span ℝ (range (hermiteNormalizedD : (ι → ℕ) → Lp ℝ 2 (gaussianProduct ι)))).topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure,orthogonal_span_hermiteNormalizedD_eq_bot,
    Submodule.bot_orthogonal_eq_top]

def hermiteBasisD : HilbertBasis (ι → ℕ) ℝ (Lp ℝ 2 (gaussianProduct ι)) :=
  HilbertBasis.mk orthonormal_hermiteNormalizedD (by rw [dense_span_hermiteD])

@[simp] theorem hermiteBasisD_apply (α : ι → ℕ) : hermiteBasisD α = hermiteNormalizedD α :=
  congrFun (HilbertBasis.coe_mk _ _) α

def hermiteD_coeff (f : Lp ℝ 2 (gaussianProduct ι)) (α : ι → ℕ) : ℝ :=
  ⟪f,hermiteNormalizedD α⟫_ℝ

theorem hermiteD_coeff_eq_integral (f : Lp ℝ 2 (gaussianProduct ι)) (α : ι → ℕ) :
    hermiteD_coeff f α = (hermiteFactorD α)⁻¹ *
      ∫ x, f x * hermiteD α x ∂gaussianProduct ι := by
  rw [hermiteD_coeff,hermiteNormalizedD_eq,inner_smul_right,← mvPolynomialLp_hermite,
    inner_mvPolynomialLp]
  simp only [eval_hermitePolynomialD]

theorem hasSum_hermiteD_expansion (f : Lp ℝ 2 (gaussianProduct ι)) :
    HasSum (fun α => hermiteD_coeff f α • hermiteNormalizedD α) f := by
  simpa [HilbertBasis.repr_apply_apply,hermiteD_coeff,real_inner_comm] using hermiteBasisD.hasSum_repr f

theorem sum_sq_hermiteD_coeff (f : Lp ℝ 2 (gaussianProduct ι)) :
    ∑' α, (hermiteD_coeff f α)^2 = ‖f‖^2 := by
  simpa [pow_two,hermiteD_coeff,real_inner_comm,real_inner_self_eq_norm_sq] using
    hermiteBasisD.tsum_inner_mul_inner f f

theorem dense_mvPolynomial_gaussianPi : Dense (range (mvPolynomialLp : MvPolynomial ι ℝ → Lp ℝ 2 (gaussianProduct ι))) := by
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr (dense_span_hermiteD (ι := ι))
  have hle : Submodule.span ℝ (range (hermiteNormalizedD : (ι → ℕ) → Lp ℝ 2 (gaussianProduct ι))) ≤
      LinearMap.range mvPolynomialLpLinear := by
    apply Submodule.span_le.mpr
    rintro f ⟨α,rfl⟩
    rw [hermiteNormalizedD_eq,← mvPolynomialLp_hermite]
    exact Submodule.smul_mem _ _ ⟨hermitePolynomialD α,rfl⟩
  exact hd.mono hle

end Foundations
