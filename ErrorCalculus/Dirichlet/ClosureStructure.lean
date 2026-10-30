import ErrorCalculus.Dirichlet.ClosureCalculus
import ErrorCalculus.Dirichlet.Calculus

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ErrorCalculus.ProtoErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ProtoErrorStructure Ω μ)

/-- The closure of a closable proto-structure is an error structure. -/
def closure (h : S.energy.IsClosable) : ErrorStructure Ω μ where
  toErrorData := S.toErrorData.closureData h
  dense := S.dense.mono S.energy.le_closureDom
  «calc» := S.closure_calculus h
  energy_closed := S.toErrorData.closureData_isClosed h
  one_mem := S.energy.le_closureDom S.one_mem

@[simp] theorem closure_dom (h : S.energy.IsClosable) :
    (S.closure h).dom = S.energy.closureDom := rfl

@[simp] theorem closure_Γ_extends (h : S.energy.IsClosable) (u v : S.dom) :
    (S.closure h).Γ (S.energy.inclusion u) (S.energy.inclusion v) = S.Γ u v :=
  S.toErrorData.closureGamma_extends h u v

/-- Equality of quadratic forms, with their domains. -/
@[simp] theorem closure_energy (h : S.energy.IsClosable) :
    (S.closure h).energy = S.energy.closure h := S.toErrorData.closureData_energy h

/-- The scalar C¹ Lipschitz contraction bound on the closed domain. -/
theorem closure_energy_contraction (h : S.energy.IsClosable) {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) (u w : (S.closure h).dom)
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun ω => F ((u : Lp ℝ 2 μ) ω)) :
    (S.energy.closure h).E w w ≤ (L:ℝ)^2 * (S.energy.closure h).E u u := by
  have he := (S.closure h).energy_contraction hF hL u w hw
  have hwE : (S.closure h).energy.E w w = (S.energy.closure h).E w w :=
    S.toErrorData.closureGamma_energy h w w
  have huE : (S.closure h).energy.E u u = (S.energy.closure h).E u u :=
    S.toErrorData.closureGamma_energy h u u
  rw [hwE, huE] at he
  exact he

/--
A global derivative bound suffices: the Lipschitz hypothesis follows by the mean value theorem.
-/
theorem closure_calculus_of_fderiv_bound (h : S.energy.IsClosable) (m : ℕ) (hm : 0 < m)
    (u : Fin m → S.energy.closureDom) (F : (Fin m → ℝ) → ℝ) (L : ℝ≥0)
    (hF : ContDiff ℝ 1 F) (hD : ∀ x, ‖fderiv ℝ F x‖₊ ≤ L)
    (w : Lp ℝ 2 μ) (hw : ⇑w =ᵐ[μ] fun ω => F (fun i => (u i : Lp ℝ 2 μ) ω)) :
    ∃ hw' : w ∈ S.energy.closureDom, ∀ v : S.energy.closureDom,
      ⇑(S.toErrorData.closureGamma h ⟨w,hw'⟩ v) =ᵐ[μ] fun ω => ∑ i,
        fderiv ℝ F (fun j => (u j : Lp ℝ 2 μ) ω) (Pi.single i 1) *
          S.toErrorData.closureGamma h (u i) v ω :=
  S.closure_calculus h m hm u F L hF
    (lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by norm_num)) hD) w hw

end ErrorCalculus.ProtoErrorStructure
