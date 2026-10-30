import ErrorCalculus.Dirichlet.FormSpaceDensityLadder

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- Canonical resolvent approximation in the actual form domain. -/
def generatorApprox (u : S.dom) (k : ℕ) : S.dom :=
  S.generatorForm (S.betaResolventGenerator (QuadForm.resolventParameter k)
    (QuadForm.resolventParameter_pos k) u)

theorem generatorApprox_mem_generatorDom (u : S.dom) (k : ℕ) :
    (S.generatorApprox u k : Lp ℝ 2 μ) ∈ S.generatorDom :=
  (S.betaResolventGenerator (QuadForm.resolventParameter k) (QuadForm.resolventParameter_pos k) u).property

theorem generatorApprox_tendsto_formSpace (u : S.dom) :
    Tendsto (fun k => S.energy.formToDomain.symm (S.generatorApprox u k)) atTop
      (𝓝 (S.energy.formToDomain.symm u)) :=
  S.tendsto_betaResolvent_formSpace_seq QuadForm.resolventParameter
    QuadForm.resolventParameter_pos QuadForm.tendsto_resolventParameter u

/-- Generator-domain density in the form norm, supplied by the resolvent. -/
theorem exists_generatorDom_seq_tendsto_formSpace (u : S.dom) :
    ∃ g : ℕ → S.dom, (∀ k, (g k : Lp ℝ 2 μ) ∈ S.generatorDom) ∧
      Tendsto (fun k => S.energy.formToDomain.symm (g k)) atTop
        (𝓝 (S.energy.formToDomain.symm u)) :=
  ⟨S.generatorApprox u, S.generatorApprox_mem_generatorDom u, S.generatorApprox_tendsto_formSpace u⟩

end ErrorCalculus.ErrorStructure
