import ErrorCalculus.Dirichlet.QuadForm
import Mathlib.Tactic.Linarith

noncomputable section
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (Q : QuadForm H)

/-- a separate domain type carries the form norm, without changing the ambient norm. -/
def FormSpace : Type _ := Q.dom
instance formAddCommGroup : AddCommGroup Q.FormSpace := inferInstanceAs (AddCommGroup Q.dom)
instance formModule : Module ℝ Q.FormSpace := inferInstanceAs (Module ℝ Q.dom)

/-- algebraic identification of the form-norm domain. -/
def formToDomain : Q.FormSpace ≃ₗ[ℝ] Q.dom where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The graph inner product is positive definite. -/
@[implicit_reducible] def formCore : InnerProductSpace.Core ℝ Q.FormSpace where
  inner x y := inner ℝ (Q.formToDomain x : H) (Q.formToDomain y : H) +
    Q.E (Q.formToDomain x) (Q.formToDomain y)
  conj_inner_symm x y := by simp [real_inner_comm, Q.symm]
  re_inner_nonneg x := add_nonneg real_inner_self_nonneg (Q.nonneg _)
  add_left x y z := by simp [inner_add_left, add_assoc, add_left_comm, add_comm]
  smul_left x y c := by simp [real_inner_smul_left, mul_add]
  definite x hx := by
    have h0 : ‖(Q.formToDomain x : H)‖ ^ 2 = 0 := by
      have he := Q.nonneg (Q.formToDomain x)
      rw [real_inner_self_eq_norm_sq] at hx
      nlinarith [sq_nonneg ‖(Q.formToDomain x : H)‖]
    have hz : (Q.formToDomain x : H) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
    apply Q.formToDomain.injective
    apply Subtype.ext
    simpa using hz

instance formNormed : NormedAddCommGroup Q.FormSpace :=
  letI := Q.formCore
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
instance formInner : InnerProductSpace ℝ Q.FormSpace :=
  InnerProductSpace.ofCore Q.formCore.toCore
instance formNormedSpace : NormedSpace ℝ Q.FormSpace :=
  letI := Q.formCore
  InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ)

/-- The form norm itself. -/
def formNorm (u : Q.dom) : ℝ := ‖Q.formToDomain.symm u‖

/-- The square of the form norm is exactly ambient norm squared plus energy. -/
theorem formNorm_sq (u : Q.dom) : Q.formNorm u ^ 2 = ‖(u : H)‖ ^ 2 + Q.E u u := by
  rw [formNorm, norm_sq_eq_re_inner (𝕜 := ℝ)]
  change inner ℝ (u : H) (u : H) + Q.E u u = _
  rw [real_inner_self_eq_norm_sq]

/-- positive definiteness of the form norm. -/
theorem formNorm_eq_zero (u : Q.dom) : Q.formNorm u = 0 ↔ u = 0 := by
  simp [formNorm]

/-- The form norm triangle inequality. -/
theorem formNorm_add (u v : Q.dom) : Q.formNorm (u + v) ≤ Q.formNorm u + Q.formNorm v := by
  simpa only [formNorm, map_add] using norm_add_le (Q.formToDomain.symm u) (Q.formToDomain.symm v)

/-- homogeneity of the form norm. -/
theorem formNorm_smul (c : ℝ) (u : Q.dom) : Q.formNorm (c • u) = |c| * Q.formNorm u := by
  simp [formNorm, norm_smul, Real.norm_eq_abs]

end ErrorCalculus.QuadForm
