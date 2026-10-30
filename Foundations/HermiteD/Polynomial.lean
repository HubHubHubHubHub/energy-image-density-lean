import Foundations.HermiteD.Orthogonality
import Mathlib.Topology.Algebra.MvPolynomial

noncomputable section
open MeasureTheory Set Polynomial
open scoped InnerProductSpace
namespace Foundations
variable {ι : Type*} [Fintype ι]

theorem monomial_eq_smul_tensorPolynomialD (s : ι →₀ ℕ) (a : ℝ) :
    MvPolynomial.monomial s a = a • tensorPolynomialD (fun i => X ^ s i) := by
  classical
  simp [MvPolynomial.monomial_eq, tensorPolynomialD, Finsupp.prod_fintype,
    MvPolynomial.smul_eq_C_mul]

theorem span_hermitePolynomialD :
    Submodule.span ℝ (range (hermitePolynomialD : (ι → ℕ) → MvPolynomial ι ℝ)) = ⊤ := by
  classical
  let W := Submodule.span ℝ (range (hermitePolynomialD : (ι → ℕ) → MvPolynomial ι ℝ))
  have hQ : W.mkQ.compMultilinearMap tensorPolynomialD = 0 := by
    apply MultilinearMap.ext_of_span_eq_top
      (g := fun {_ : ι} n => hermitePolynomial n) (fun _ => span_hermitePolynomial)
    intro α
    change W.mkQ (hermitePolynomialD α) = 0
    exact (Submodule.Quotient.mk_eq_zero W).mpr (Submodule.subset_span (mem_range_self α))
  have ht (p : ι → ℝ[X]) : tensorPolynomialD p ∈ W := by
    have H := congrArg (fun F : MultilinearMap ℝ (fun _ : ι => ℝ[X]) (MvPolynomial ι ℝ ⧸ W) => F p) hQ
    exact (Submodule.Quotient.mk_eq_zero W).mp H
  apply top_unique
  intro p hp
  clear hp
  change p ∈ W
  induction p using MvPolynomial.induction_on' with
  | monomial s a => rw [monomial_eq_smul_tensorPolynomialD]; exact W.smul_mem _ (ht _)
  | add p q hp hq => exact W.add_mem hp hq

theorem memLp_mvPolynomial_gaussianProduct (p : MvPolynomial ι ℝ) :
    MemLp (fun x => MvPolynomial.eval x p) 2 (gaussianProduct ι) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simpa only [map_add,Pi.add_def] using hp.add hq
  | monomial s a =>
    have H : MemLp (fun x : ι → ℝ => ∏ i, x i ^ s i) 2 (gaussianProduct ι) := by
      apply memLp_two_gaussianProduct_prod (g := fun i (x : ℝ) => x ^ s i)
      · intro i; fun_prop
      · intro i; simpa using memLp_polynomial_gaussian (X ^ s i)
    simpa [MvPolynomial.eval_monomial, Finsupp.prod_fintype] using H.const_mul a

def mvPolynomialLp (p : MvPolynomial ι ℝ) : Lp ℝ 2 (gaussianProduct ι) :=
  (memLp_mvPolynomial_gaussianProduct p).toLp (fun x => MvPolynomial.eval x p)

theorem coe_mvPolynomialLp (p : MvPolynomial ι ℝ) :
    mvPolynomialLp p =ᵐ[gaussianProduct ι] fun x => MvPolynomial.eval x p :=
  (memLp_mvPolynomial_gaussianProduct p).coeFn_toLp

def mvPolynomialLpLinear : MvPolynomial ι ℝ →ₗ[ℝ] Lp ℝ 2 (gaussianProduct ι) where
  toFun := mvPolynomialLp
  map_add' p q := by
    apply Lp.ext
    filter_upwards [coe_mvPolynomialLp (p+q), coe_mvPolynomialLp p, coe_mvPolynomialLp q,
      Lp.coeFn_add (mvPolynomialLp p) (mvPolynomialLp q)] with x ha hp hq hs
    change (mvPolynomialLp (p+q)) x = (mvPolynomialLp p + mvPolynomialLp q) x
    rw [ha,hs]
    simp only [Pi.add_apply,hp,hq,map_add]
  map_smul' a p := by
    apply Lp.ext
    filter_upwards [coe_mvPolynomialLp (a • p), coe_mvPolynomialLp p,
      Lp.coeFn_smul a (mvPolynomialLp p)] with x ha hp hs
    simp [ha,hs,hp]

theorem mvPolynomialLp_hermite (α : ι → ℕ) :
    mvPolynomialLp (hermitePolynomialD α) = hermiteLpD α := by
  apply Lp.ext
  filter_upwards [coe_mvPolynomialLp (hermitePolynomialD α), coe_hermiteLpD α] with x hp hh
  rw [hp,hh,eval_hermitePolynomialD]

theorem inner_mvPolynomialLp (f : Lp ℝ 2 (gaussianProduct ι)) (p : MvPolynomial ι ℝ) :
    ⟪f,mvPolynomialLp p⟫_ℝ = ∫ x, f x * MvPolynomial.eval x p ∂gaussianProduct ι := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_mvPolynomialLp p] with x hx
  simp [hx,mul_comm]

theorem integral_mul_mvPolynomial_eq_zero (f : Lp ℝ 2 (gaussianProduct ι))
    (hf : ∀ α : ι → ℕ, ⟪f,hermiteLpD α⟫_ℝ = 0) (p : MvPolynomial ι ℝ) :
    (∫ x, f x * MvPolynomial.eval x p ∂gaussianProduct ι) = 0 := by
  let L : MvPolynomial ι ℝ →ₗ[ℝ] ℝ := (innerSL ℝ f).toLinearMap.comp mvPolynomialLpLinear
  have hk : Submodule.span ℝ (range (hermitePolynomialD : (ι → ℕ) → MvPolynomial ι ℝ)) ≤
      LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro q ⟨α,rfl⟩
    change ⟪f,mvPolynomialLp (hermitePolynomialD α)⟫_ℝ = 0
    rw [mvPolynomialLp_hermite]
    exact hf α
  have h := LinearMap.mem_ker.mp (hk (show p ∈ _ from by rw [span_hermitePolynomialD]; trivial))
  change ⟪f,mvPolynomialLp p⟫_ℝ = 0 at h
  rwa [inner_mvPolynomialLp] at h

end Foundations
