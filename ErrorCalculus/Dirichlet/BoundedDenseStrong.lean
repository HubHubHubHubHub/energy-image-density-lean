import ErrorCalculus.Dirichlet.FormConvergence
import ErrorCalculus.Dirichlet.BoundedDense

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- The explicit form-norm bound for every truncation. -/
theorem norm_truncationSeq_formSpace_le (u : S.dom) (n : ℕ) :
    ‖S.energy.formToDomain.symm (S.truncationSeq u n)‖ ≤ ‖S.energy.formToDomain.symm u‖ := by
  have hn := pow_le_pow_left₀ (norm_nonneg _) (S.norm_truncationSeq_le u n) 2
  have he := S.energy_truncationSeq_le u n
  have h1 := S.energy.formSpace_norm_sq (S.energy.formToDomain.symm (S.truncationSeq u n))
  have h2 := S.energy.formSpace_norm_sq (S.energy.formToDomain.symm u)
  simp only [LinearEquiv.apply_symm_apply] at h1 h2
  nlinarith [norm_nonneg (S.energy.formToDomain.symm (S.truncationSeq u n)),
    norm_nonneg (S.energy.formToDomain.symm u)]

/-- bounded truncations converge in the form norm. -/
theorem tendsto_truncationSeq_formSpace (u : S.dom) :
    Tendsto (fun n => S.energy.formToDomain.symm (S.truncationSeq u n)) atTop
      (𝓝 (S.energy.formToDomain.symm u)) :=
  S.energy_closed.tendsto_formSpace_of_energy_le
    (S.tendsto_truncationSeq u) (S.energy_truncationSeq_le u)

/-- The energies of the approximation errors tend to zero. -/
theorem tendsto_energy_truncationSeq_sub (u : S.dom) :
    Tendsto (fun n => S.energy.E (S.truncationSeq u n - u) (S.truncationSeq u n - u))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n => S.energy.formToDomain.symm (S.truncationSeq u n - u))
      atTop (𝓝 0) := by
    simpa only [map_sub, sub_self] using
      (S.tendsto_truncationSeq_formSpace u).sub_const (S.energy.formToDomain.symm u)
  have hh := (S.energy.continuous_energy_formSpace.tendsto (0, 0)).comp
    (ht.prodMk_nhds ht)
  simpa only [Function.comp_def, LinearEquiv.apply_symm_apply,
    map_zero, LinearMap.zero_apply] using hh

/-- diagonal energies converge as real numbers. -/
theorem tendsto_energy_truncationSeq (u : S.dom) :
    Tendsto (fun n => S.energy.E (S.truncationSeq u n) (S.truncationSeq u n))
      atTop (𝓝 (S.energy.E u u)) := by
  have ht := S.tendsto_truncationSeq_formSpace u
  have he := (S.energy.continuous_energy_formSpace.tendsto
    (S.energy.formToDomain.symm u, S.energy.formToDomain.symm u)).comp (ht.prodMk_nhds ht)
  simpa only [Function.comp_def, LinearEquiv.apply_symm_apply] using he

/-- energy seminorm convergence of the approximation errors. -/
theorem tendsto_seminorm_truncationSeq_sub (u : S.dom) :
    Tendsto (fun n => S.energy.seminorm (S.truncationSeq u n - u)) atTop (𝓝 0) := by
  simpa only [QuadForm.seminorm, Real.sqrt_zero] using
    (S.tendsto_energy_truncationSeq_sub u).sqrt

/-- bounded domain elements are dense in the form Hilbert space. -/
theorem dense_bounded_formSpace :
    Dense {x : S.energy.FormSpace | AEBounded (μ := μ) (S.energy.formInclusion x)} := by
  intro x
  apply mem_closure_of_tendsto (S.tendsto_truncationSeq_formSpace (S.energy.formToDomain x))
  exact Eventually.of_forall fun n => S.bounded_truncationSeq _ n

/-- Quantitative form approximation, in the squared graph norm convention. -/
theorem exists_bounded_approx_form (u : S.dom) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : S.dom, AEBounded (μ := μ) (v : Lp ℝ 2 μ) ∧
      ‖((v - u : S.dom) : Lp ℝ 2 μ)‖^2 + S.energy.E (v-u) (v-u) < ε := by
  have ht := ((S.tendsto_truncationSeq_formSpace u).sub_const
    (S.energy.formToDomain.symm u)).norm.pow 2
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at ht
  have he := ht.eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := he.exists
  refine ⟨S.truncationSeq u n, S.bounded_truncationSeq u n, ?_⟩
  rw [← map_sub, S.energy.formSpace_norm_sq] at hn
  exact hn

/-- The carré du champ as a bounded bilinear map for the form norm. -/
def gammaFormBilin : S.energy.FormSpace →L[ℝ] S.energy.FormSpace →L[ℝ] Lp ℝ 1 μ :=
  (S.Γ.compl₁₂ S.energy.formToDomain.toLinearMap S.energy.formToDomain.toLinearMap).mkContinuous₂
    2 (by
      intro x y
      apply (S.toErrorData.norm_gamma_le_energy (S.energy.formToDomain x)
        (S.energy.formToDomain y)).trans
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (S.energy.seminorm_le_formNorm _) (by norm_num)
      · exact S.energy.seminorm_le_formNorm _
      · exact Real.sqrt_nonneg _
      · positivity)

@[simp] theorem gammaFormBilin_apply (x y : S.energy.FormSpace) :
    S.gammaFormBilin x y = S.Γ (S.energy.formToDomain x) (S.energy.formToDomain y) := rfl

/-- joint L¹ continuity of the carré du champ. -/
theorem continuous_gamma_formSpace :
    Continuous (fun p : S.energy.FormSpace × S.energy.FormSpace =>
      S.Γ (S.energy.formToDomain p.1) (S.energy.formToDomain p.2)) :=
  S.gammaFormBilin.continuous₂

/-- The truncation carré du champ converges in L¹. -/
theorem tendsto_gamma_truncationSeq (u : S.dom) :
    Tendsto (fun n => S.Γ (S.truncationSeq u n) (S.truncationSeq u n)) atTop
      (𝓝 (S.Γ u u)) :=
  (S.continuous_gamma_formSpace.tendsto
    (S.energy.formToDomain.symm u, S.energy.formToDomain.symm u)).comp
      ((S.tendsto_truncationSeq_formSpace u).prodMk_nhds (S.tendsto_truncationSeq_formSpace u))

end ErrorCalculus.ErrorStructure
