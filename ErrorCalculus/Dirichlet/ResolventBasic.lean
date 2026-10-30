import ErrorCalculus.Dirichlet.FormSpace
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (Q : QuadForm H)

/-- The inclusion is contractive pointwise. -/
theorem norm_formInclusion_le (x : Q.FormSpace) : ‖Q.formInclusion x‖ ≤ ‖x‖ := by
  simpa using Q.formInclusion.le_of_opNorm_le Q.formInclusion_norm_le x

/-- The bounded shifted form, on the fixed graph Hilbert space. -/
def formBilin (β : ℝ) : Q.FormSpace →L[ℝ] Q.FormSpace →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun x y => inner ℝ x y + (β-1) *
      inner ℝ (Q.formInclusion x) (Q.formInclusion y))
      (by intros; simp [inner_add_left]; ring)
      (by intros; simp [real_inner_smul_left]; ring)
      (by intros; simp [inner_add_right]; ring)
      (by intros; simp [inner_smul_right]; ring))
    (1 + |β-1|) (by
      intro x y
      change |inner ℝ x y + (β-1) * inner ℝ (Q.formInclusion x) (Q.formInclusion y)| ≤ _
      calc
        _ ≤ |inner ℝ x y| + |β-1| * |inner ℝ (Q.formInclusion x) (Q.formInclusion y)| := by
          simpa only [abs_mul] using abs_add_le (inner ℝ x y)
            ((β-1) * inner ℝ (Q.formInclusion x) (Q.formInclusion y))
        _ ≤ ‖x‖ * ‖y‖ + |β-1| * (‖x‖ * ‖y‖) := by
          gcongr
          · exact abs_real_inner_le_norm _ _
          · exact (abs_real_inner_le_norm _ _).trans
              (mul_le_mul (Q.norm_formInclusion_le x) (Q.norm_formInclusion_le y)
                (norm_nonneg _) (norm_nonneg _))
        _ = _ := by ring)

/-- The bounded form is exactly E + beta times the ambient inner product. -/
@[simp] theorem formBilin_apply (β : ℝ) (x y : Q.FormSpace) :
    Q.formBilin β x y = Q.E (Q.formToDomain x) (Q.formToDomain y) +
      β * inner ℝ (Q.formInclusion x) (Q.formInclusion y) := by
  change (inner ℝ (Q.formToDomain x : H) (Q.formToDomain y : H) +
    Q.E (Q.formToDomain x) (Q.formToDomain y)) + (β-1) *
    inner ℝ (Q.formToDomain x : H) (Q.formToDomain y : H) = _
  change _ = Q.E (Q.formToDomain x) (Q.formToDomain y) +
    β * inner ℝ (Q.formToDomain x : H) (Q.formToDomain y : H)
  ring

/-- The sharp lower diagonal bound in the graph norm. -/
theorem formBilin_lower (β : ℝ) (x : Q.FormSpace) :
    min 1 β * ‖x‖ ^ 2 ≤ Q.formBilin β x x := by
  rw [Q.formSpace_norm_sq, Q.formBilin_apply, real_inner_self_eq_norm_sq]
  change _ ≤ Q.E (Q.formToDomain x) (Q.formToDomain x) + β * ‖(Q.formToDomain x : H)‖ ^ 2
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) β) (Q.nonneg (Q.formToDomain x))
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) β) (sq_nonneg ‖(Q.formToDomain x : H)‖)
  nlinarith

/-- The sharp upper diagonal bound. -/
theorem formBilin_upper (β : ℝ) (x : Q.FormSpace) :
    Q.formBilin β x x ≤ max 1 β * ‖x‖ ^ 2 := by
  rw [Q.formSpace_norm_sq, Q.formBilin_apply, real_inner_self_eq_norm_sq]
  change Q.E (Q.formToDomain x) (Q.formToDomain x) + β * ‖(Q.formToDomain x : H)‖ ^ 2 ≤ _
  have h₁ := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) β) (Q.nonneg (Q.formToDomain x))
  have h₂ := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) β) (sq_nonneg ‖(Q.formToDomain x : H)‖)
  nlinarith

/-- coercivity does not require density. -/
theorem formBilin_isCoercive {β : ℝ} (hβ : 0 < β) : IsCoercive (Q.formBilin β) :=
  ⟨min 1 β, lt_min zero_lt_one hβ, fun x => by simpa only [pow_two, mul_assoc] using Q.formBilin_lower β x⟩

variable [CompleteSpace H] (hQ : Q.IsClosed)

/-- Mathlib's Lax--Milgram equivalence represents the form, not its inverse. -/
def laxMilgram (β : ℝ) (hβ : 0 < β) : Q.FormSpace ≃L[ℝ] Q.FormSpace :=
  letI := hQ.completeSpace_formSpace
  (Q.formBilin_isCoercive hβ).continuousLinearEquivOfBilin

/-- The Riesz representative is the adjoint of the inclusion. -/
def formRiesz : H →L[ℝ] Q.FormSpace :=
  letI := hQ.completeSpace_formSpace
  Q.formInclusion.adjoint

/-- domain-valued solution, obtained by the inverse Lax--Milgram equivalence. -/
def resolventDom (β : ℝ) (hβ : 0 < β) : H →ₗ[ℝ] Q.dom :=
  Q.formToDomain.toLinearMap.comp
    ((Q.laxMilgram hQ β hβ).symm.toContinuousLinearMap.comp (Q.formRiesz hQ)).toLinearMap

/-- The continuous ambient resolvent. -/
def resolvent (β : ℝ) (hβ : 0 < β) : H →L[ℝ] H :=
  Q.formInclusion.comp ((Q.laxMilgram hQ β hβ).symm.toContinuousLinearMap.comp (Q.formRiesz hQ))

@[simp] theorem coe_resolventDom (β : ℝ) (hβ : 0 < β) (f : H) :
    (Q.resolventDom hQ β hβ f : H) = Q.resolvent hQ β hβ f := rfl

/-- The variational characterization. -/
theorem resolvent_spec (β : ℝ) (hβ : 0 < β) (f : H) (v : Q.dom) :
    Q.E (Q.resolventDom hQ β hβ f) v +
      β * inner ℝ (Q.resolvent hQ β hβ f) (v : H) = inner ℝ f (v : H) := by
  letI := hQ.completeSpace_formSpace
  have hh := (Q.formBilin_isCoercive hβ).continuousLinearEquivOfBilin_apply
    ((Q.laxMilgram hQ β hβ).symm (Q.formRiesz hQ f)) (Q.formToDomain.symm v)
  change inner ℝ ((Q.laxMilgram hQ β hβ) ((Q.laxMilgram hQ β hβ).symm
    (Q.formRiesz hQ f))) (Q.formToDomain.symm v) = _ at hh
  rw [ContinuousLinearEquiv.apply_symm_apply, Q.formBilin_apply] at hh
  exact hh.symm.trans (Q.formInclusion.adjoint_inner_left (Q.formToDomain.symm v) f)

/-- uniqueness by strict positivity of the shifted form. -/
theorem resolvent_unique (β : ℝ) (hβ : 0 < β) (f : H) (u : Q.dom)
    (hu : ∀ v : Q.dom, Q.E u v + β * inner ℝ (u : H) (v : H) = inner ℝ f (v : H)) :
    u = Q.resolventDom hQ β hβ f := by
  let w := u - Q.resolventDom hQ β hβ f
  have he := Q.resolvent_spec hQ β hβ f w
  have hh := hu w
  have hz : Q.E w w + β * ‖(w : H)‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [w, map_sub, LinearMap.sub_apply, Submodule.coe_sub, inner_sub_left,
      inner_sub_right, coe_resolventDom] at he hh ⊢
    linarith
  have hn : ‖(w : H)‖ ^ 2 = 0 := by nlinarith [Q.nonneg w, sq_nonneg ‖(w : H)‖]
  apply sub_eq_zero.mp
  apply Subtype.ext
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

/-- symmetry. -/
theorem resolvent_symm (β : ℝ) (hβ : 0 < β) (f g : H) :
    inner ℝ (Q.resolvent hQ β hβ f) g = inner ℝ f (Q.resolvent hQ β hβ g) := by
  have hf := Q.resolvent_spec hQ β hβ f (Q.resolventDom hQ β hβ g)
  have hg := Q.resolvent_spec hQ β hβ g (Q.resolventDom hQ β hβ f)
  rw [Q.symm] at hg
  simp only [coe_resolventDom] at hf hg
  have hi : inner ℝ (Q.resolvent hQ β hβ g) (Q.resolvent hQ β hβ f) =
      inner ℝ (Q.resolvent hQ β hβ f) (Q.resolvent hQ β hβ g) := real_inner_comm _ _
  rw [hi] at hg
  calc
    _ = inner ℝ g (Q.resolvent hQ β hβ f) := real_inner_comm _ _
    _ = _ := hg.symm.trans hf

/-- self-adjointness as a continuous operator. -/
theorem resolvent_isSelfAdjoint (β : ℝ) (hβ : 0 < β) :
    IsSelfAdjoint (Q.resolvent hQ β hβ) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (Q.resolvent_symm hQ β hβ)

/-- The diagonal variational identity. -/
theorem resolvent_energy_identity (β : ℝ) (hβ : 0 < β) (f : H) :
    Q.E (Q.resolventDom hQ β hβ f) (Q.resolventDom hQ β hβ f) +
      β * ‖Q.resolvent hQ β hβ f‖ ^ 2 = inner ℝ f (Q.resolvent hQ β hβ f) := by
  simpa only [coe_resolventDom, real_inner_self_eq_norm_sq] using
    Q.resolvent_spec hQ β hβ f (Q.resolventDom hQ β hβ f)

/-- The lower bound for the quadratic pairing. -/
theorem beta_norm_sq_resolvent_le (β : ℝ) (hβ : 0 < β) (f : H) :
    β * ‖Q.resolvent hQ β hβ f‖ ^ 2 ≤ inner ℝ f (Q.resolvent hQ β hβ f) := by
  linarith [Q.resolvent_energy_identity hQ β hβ f, Q.nonneg (Q.resolventDom hQ β hβ f)]

/-- positivity of the resolvent. -/
theorem inner_resolvent_self_nonneg (β : ℝ) (hβ : 0 < β) (f : H) :
    0 ≤ inner ℝ (Q.resolvent hQ β hβ f) f := by
  rw [real_inner_comm]
  exact (mul_nonneg hβ.le (sq_nonneg _)).trans (Q.beta_norm_sq_resolvent_le hQ β hβ f)

/-- The scaled resolvent is a contraction. -/
theorem norm_beta_resolvent_le (β : ℝ) (hβ : 0 < β) (f : H) :
    ‖β • Q.resolvent hQ β hβ f‖ ≤ ‖f‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
  have hh := (Q.beta_norm_sq_resolvent_le hQ β hβ f).trans (real_inner_le_norm _ _)
  by_cases hz : ‖Q.resolvent hQ β hβ f‖ = 0
  · simp [hz]
  · have hp := lt_of_le_of_ne (norm_nonneg (Q.resolvent hQ β hβ f)) (Ne.symm hz)
    nlinarith

/-- contraction in operator norm. -/
theorem norm_beta_resolvent_op_le (β : ℝ) (hβ : 0 < β) :
    ‖β • Q.resolvent hQ β hβ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using Q.norm_beta_resolvent_le hQ β hβ f

/-- energy bound for arbitrary data. -/
theorem resolvent_energy_le (β : ℝ) (hβ : 0 < β) (f : H) :
    Q.E (Q.resolventDom hQ β hβ f) (Q.resolventDom hQ β hβ f) ≤ ‖f‖ ^ 2 / β := by
  have hc := Q.norm_beta_resolvent_le hQ β hβ f
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hβ] at hc
  apply (le_div_iff₀ hβ).mpr
  have hi := real_inner_le_norm f (Q.resolvent hQ β hβ f)
  have he := Q.resolvent_energy_identity hQ β hβ f
  have he' : Q.E (Q.resolventDom hQ β hβ f) (Q.resolventDom hQ β hβ f) ≤
      ‖f‖ * ‖Q.resolvent hQ β hβ f‖ := by
    nlinarith [mul_nonneg hβ.le (sq_nonneg ‖Q.resolvent hQ β hβ f‖)]
  nlinarith [mul_le_mul_of_nonneg_right he' hβ.le,
    mul_le_mul_of_nonneg_left hc (norm_nonneg f)]

end ErrorCalculus.QuadForm
