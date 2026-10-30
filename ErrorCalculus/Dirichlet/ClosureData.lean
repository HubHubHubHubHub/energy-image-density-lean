import ErrorCalculus.Dirichlet.ExtensionGamma

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorData
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorData Ω μ) (h : S.energy.IsClosable)

/-- The closed-domain error data. -/
def closureData : ErrorData Ω μ where
  dom := S.energy.closureDom
  Γ := S.closureGamma h
  Γ_symm := S.closureGamma_symm h
  Γ_nonneg := S.closureGamma_nonneg h

/-- equality of quadratic forms, including the domain and mixed energies. -/
theorem closureData_energy : (S.closureData h).energy = S.energy.closure h := by
  apply QuadForm.Extends.antisymm
  · refine ⟨le_rfl, fun u v => ?_⟩
    exact (S.closureGamma_energy h u v).symm
  · refine ⟨le_rfl, fun u v => ?_⟩
    exact S.closureGamma_energy h u v

/-- The energy of the extended data is closed. -/
theorem closureData_isClosed : (S.closureData h).energy.IsClosed := by
  rw [S.closureData_energy h]
  exact S.energy.closure_isClosed h

/-- Cauchy--Schwarz on the closed domain. -/
theorem closureGamma_cauchy_schwarz (u v : S.energy.closureDom) :
    ∀ᵐ ω ∂μ, (S.closureGamma h u v ω)^2 ≤
      S.closureGamma h u u ω * S.closureGamma h v v ω :=
  (S.closureData h).gamma_cauchy_schwarz u v

/-- The triangle inequality on the closed domain. -/
theorem closureGamma_sqrt_add_le (u v : S.energy.closureDom) :
    ∀ᵐ ω ∂μ, Real.sqrt (S.closureGamma h (u+v) (u+v) ω) ≤
      Real.sqrt (S.closureGamma h u u ω) + Real.sqrt (S.closureGamma h v v ω) :=
  (S.closureData h).sqrt_gamma_add_le u v

/-- The reverse triangle inequality on the closed domain. -/
theorem closureGamma_sqrt_sub_le (u v : S.energy.closureDom) :
    ∀ᵐ ω ∂μ, |Real.sqrt (S.closureGamma h u u ω) - Real.sqrt (S.closureGamma h v v ω)| ≤
      Real.sqrt (S.closureGamma h (u-v) (u-v) ω) :=
  (S.closureData h).sqrt_gamma_sub_le u v

/-- finite, function-valued coefficients on the closed domain. -/
theorem closureGamma_sum_cauchy_schwarz {k : ℕ} (u : Fin k → S.energy.closureDom)
    (v : S.energy.closureDom) (c : Fin k → Ω → ℝ) :
    ∀ᵐ ω ∂μ, |∑ i, c i ω * S.closureGamma h (u i) v ω| ≤
      Real.sqrt (∑ i, (c i ω)^2) * Real.sqrt (∑ i, S.closureGamma h (u i) (u i) ω) *
        Real.sqrt (S.closureGamma h v v ω) :=
  (S.closureData h).gamma_sum_cauchy_schwarz u v c

/-- The normalization of the square root on the closure. -/
theorem closureData_norm_sqrtGamma_sq (u : S.energy.closureDom) :
    ‖(S.closureData h).sqrtGamma u‖^2 = 2 * (S.energy.closure h).E u u := by
  rw [(S.closureData h).norm_sqrtGamma_sq]
  congr 1
  exact S.closureGamma_energy h u u

/-- The square-root extension agrees with the original L² class. -/
theorem closureData_sqrtGamma_extends (u : S.dom) :
    (S.closureData h).sqrtGamma (S.energy.inclusion u) = S.sqrtGamma u := by
  apply Lp.ext
  filter_upwards [(S.closureData h).coeFn_sqrtGamma (S.energy.inclusion u),
    S.coeFn_sqrtGamma u] with ω hc hu
  change _ = Real.sqrt (S.closureGamma h (S.energy.inclusion u) (S.energy.inclusion u) ω) at hc
  rw [S.closureGamma_extends] at hc
  exact hc.trans hu.symm

/-- L¹ approximation of the diagonal error in the closed domain. -/
theorem closureGamma_approx {u : ℕ → S.dom} {v : S.energy.closureDom}
    (hu : S.energy.Approaches u v) :
    Tendsto (fun n => ‖S.closureGamma h (S.energy.inclusion (u n)-v)
      (S.energy.inclusion (u n)-v)‖) atTop (𝓝 0) := by
  have ht := (S.energy.closure_approx h hu v.property).const_mul 2
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [] with n
  change 2 * (S.energy.closure h).E _ _ = ‖(S.closureData h).Γ _ _‖
  rw [(S.closureData h).norm_gamma_self]
  congr 1
  exact (S.closureGamma_energy h _ _).symm

/-- Every approaching sequence of roots converges to the closed root. -/
theorem closureData_sqrtGamma_tendsto {u : ℕ → S.dom} {v : S.energy.closureDom}
    (hu : S.energy.Approaches u v) :
    Tendsto (fun n => S.sqrtGamma (u n)) atTop (𝓝 ((S.closureData h).sqrtGamma v)) := by
  have ht := (S.closureGamma_approx h hu).sqrt
  simp only [Real.sqrt_zero] at ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ ht
  intro n
  rw [← S.closureData_sqrtGamma_extends h (u n)]
  apply ((S.closureData h).norm_sqrtGamma_sub_le _ _).trans_eq
  rw [← (S.closureData h).norm_sqrtGamma]
  rw [← Real.sqrt_sq (norm_nonneg _), (S.closureData h).norm_sqrtGamma_sq,
    ← (S.closureData h).norm_gamma_self]
  rfl

end ErrorCalculus.ErrorData
