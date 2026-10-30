import ErrorCalculus.Dirichlet.SemigroupResolvent
import ErrorCalculus.Dirichlet.ErrorStructure
import Foundations.Semigroup.SelfAdjoint

noncomputable section
open Filter Topology Set MeasureTheory
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (Q : QuadForm H) (hQ : Q.IsClosed) (hd : Dense (Q.dom : Set H))

/-- The form resolvent is self-adjoint. -/
theorem formResolvent_isSelfAdjoint : (Q.formResolvent hQ hd).IsSelfAdjointResolvent := by
  intro b hb
  rw [Q.formResolvent_G hQ hd hb]
  exact Q.resolvent_isSelfAdjoint hQ b hb

/--
The strongly continuous contraction semigroup associated with the closed form. Negative times are
assigned zero; the semigroup laws concern nonnegative times.
-/
def semigroup (t : ℝ) : H →L[ℝ] H := (Q.formResolvent hQ hd).semigroup t

theorem norm_semigroup_le_one {t : ℝ} (ht : 0 ≤ t) : ‖Q.semigroup hQ hd t‖ ≤ 1 :=
  (Q.formResolvent hQ hd).norm_semigroup_le_one ht

theorem norm_semigroup_apply_le {t : ℝ} (ht : 0 ≤ t) (u : H) :
    ‖Q.semigroup hQ hd t u‖ ≤ ‖u‖ :=
  (Q.formResolvent hQ hd).norm_semigroup_apply_le ht u

@[simp] theorem semigroup_zero : Q.semigroup hQ hd 0 = 1 :=
  (Q.formResolvent hQ hd).semigroup_zero

theorem semigroup_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Q.semigroup hQ hd (s+t) = Q.semigroup hQ hd s * Q.semigroup hQ hd t :=
  (Q.formResolvent hQ hd).semigroup_add hs ht

theorem continuous_semigroup_apply (u : H) :
    ContinuousOn (fun t => Q.semigroup hQ hd t u) (Ici 0) :=
  (Q.formResolvent hQ hd).continuous_semigroup_apply u

theorem semigroup_selfAdjoint {t : ℝ} (ht : 0 ≤ t) :
    IsSelfAdjoint (Q.semigroup hQ hd t) :=
  (Q.formResolvent hQ hd).semigroup_selfAdjoint (Q.formResolvent_isSelfAdjoint hQ hd) ht

theorem semigroup_symm {t : ℝ} (ht : 0 ≤ t) (u v : H) :
    inner ℝ (Q.semigroup hQ hd t u) v = inner ℝ u (Q.semigroup hQ hd t v) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (Q.semigroup_selfAdjoint hQ hd ht) u v

/-- Positivity in the Hilbert-space sense, for every closed symmetric form. -/
theorem inner_semigroup_self_nonneg {t : ℝ} (ht : 0 ≤ t) (u : H) :
    0 ≤ inner ℝ (Q.semigroup hQ hd t u) u :=
  (Q.formResolvent hQ hd).inner_semigroup_self_nonneg (Q.formResolvent_isSelfAdjoint hQ hd) ht u

theorem norm_semigroup_sub_le {t : ℝ} (ht : 0 ≤ t) (u : (Q.formResolvent hQ hd).dom) :
    ‖Q.semigroup hQ hd t u - u‖ ≤ t * ‖(Q.formResolvent hQ hd).generator u‖ :=
  (Q.formResolvent hQ hd).norm_semigroup_sub_le ht u

theorem semigroup_sub_eq_integral {t : ℝ} (ht : 0 ≤ t) (u : (Q.formResolvent hQ hd).dom) :
    Q.semigroup hQ hd t u - u =
      ∫ s in 0..t, Q.semigroup hQ hd s ((Q.formResolvent hQ hd).generator u) :=
  (Q.formResolvent hQ hd).semigroup_sub_eq_integral ht u

theorem hasDerivWithinAt_semigroup_zero (u : (Q.formResolvent hQ hd).dom) :
    HasDerivWithinAt (fun t => Q.semigroup hQ hd t u)
      ((Q.formResolvent hQ hd).generator u) (Ici 0) 0 :=
  (Q.formResolvent hQ hd).hasDerivWithinAt_semigroup_zero u

theorem tendsto_semigroup_sub_div (u : (Q.formResolvent hQ hd).dom) :
    Tendsto (fun t : ℝ => t⁻¹ • (Q.semigroup hQ hd t u - u)) (𝓝[>] 0)
      (𝓝 ((Q.formResolvent hQ hd).generator u)) :=
  (Q.formResolvent hQ hd).tendsto_semigroup_sub_div u

end ErrorCalculus.QuadForm
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The semigroup attached to an error structure. -/
def semigroup (S : ErrorStructure Ω μ) (t : ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  S.energy.semigroup S.energy_closed S.dense t

end ErrorCalculus.ErrorStructure
