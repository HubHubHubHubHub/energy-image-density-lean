import ErrorCalculus.Dirichlet.FormNorm
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Tactic

noncomputable section
open Filter Topology
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (Q : QuadForm H)

/-- The existing form space has exactly the graph norm. -/
theorem formSpace_norm_sq (x : Q.FormSpace) :
    ‖x‖ ^ 2 = ‖(Q.formToDomain x : H)‖ ^ 2 + Q.E (Q.formToDomain x) (Q.formToDomain x) :=
  Q.formNorm_sq (Q.formToDomain x)

/-- The inclusion in the ambient Hilbert space is contractive. -/
def formInclusion : Q.FormSpace →L[ℝ] H :=
  (Q.dom.subtype.comp Q.formToDomain.toLinearMap).mkContinuous 1 (by
    intro x
    have he := Q.formSpace_norm_sq x
    have hp := Q.nonneg (Q.formToDomain x)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, one_mul]
    nlinarith [norm_nonneg x, norm_nonneg (Q.formToDomain x : H)])

/-- The ambient inclusion has operator norm at most one. -/
theorem formInclusion_norm_le : ‖Q.formInclusion‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The energy coordinate is also contractive for the form norm. -/
def formEnergy : Q.FormSpace →L[ℝ] Q.EnergyHilbert :=
  (Q.j.comp Q.formToDomain.toLinearMap).mkContinuous 1 (by
    intro x
    have he := Q.formSpace_norm_sq x
    have hj : ‖Q.j (Q.formToDomain x)‖ ^ 2 = Q.E (Q.formToDomain x) (Q.formToDomain x) := by
      rw [← real_inner_self_eq_norm_sq, Q.inner_j]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, one_mul]
    nlinarith [norm_nonneg x, norm_nonneg (Q.j (Q.formToDomain x)),
      sq_nonneg ‖(Q.formToDomain x : H)‖])

/-- closedness implies completeness of the form Hilbert space. -/
theorem IsClosed.completeSpace_formSpace [CompleteSpace H] (hQ : Q.IsClosed) :
    CompleteSpace Q.FormSpace := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro x hx
  have hc : Q.IsCauchy (fun n => Q.formToDomain (x n)) :=
    ⟨hx.map Q.formInclusion.uniformContinuous, hx.map Q.formEnergy.uniformContinuous⟩
  obtain ⟨v, hv, he⟩ := (Q.isClosed_iff_complete.mp hQ) _ hc
  refine ⟨Q.formToDomain.symm v, ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun n => ‖x n - Q.formToDomain.symm v‖ ^ 2) atTop (𝓝 0) := by
    have ht := ((hv.sub_const (v : H)).norm.pow 2).add he
    simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_add, Q.formSpace_norm_sq, map_sub, LinearEquiv.apply_symm_apply,
      Submodule.coe_sub] using ht
  have ht := hs.sqrt
  simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using ht

end ErrorCalculus.QuadForm
