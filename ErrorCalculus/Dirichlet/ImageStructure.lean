import ErrorCalculus.Dirichlet.ImageCalculus

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {m : ℕ} (X : Fin m → Lp ℝ 2 μ) (hX : ∀ i, X i ∈ S.dom)

/-- The image error structure, with all five properties proved. -/
def image : ErrorStructure (Fin m → ℝ) (imageLaw X) where
  toErrorData := S.toErrorData.imageData X
  dense := S.imageDom_dense X hX
  «calc» := S.imageData_calculus X
  energy_closed := S.toErrorData.imageData_isClosed X S.energy_closed
  one_mem := S.toErrorData.imageData_one_mem X S.one_mem

/-- The image domain is exactly the inverse image of the original domain. -/
theorem image_dom : (S.image X hX).dom = S.dom.comap (pullback X).toLinearMap := rfl

/-- The mixed carré du champ is characterized by all bounded measurable tests. -/
theorem image_Γ_characterization (F G : (S.image X hX).dom)
    (H : (Fin m → ℝ) → ℝ) (hH : Measurable H) (hB : ∃ C : ℝ, ∀ x, ‖H x‖ ≤ C) :
    (∫ x, H x * (S.image X hX).Γ F G x ∂imageLaw X) =
      ∫ ω, H (imageRepresentative X ω) *
        S.Γ (S.toErrorData.imageLift X F) (S.toErrorData.imageLift X G) ω ∂μ :=
  S.toErrorData.imageGamma_characterization X F G ⟨H, hH, hB⟩

/-- Exact equality of the mixed energies. -/
theorem image_energy (F G : (S.image X hX).dom) :
    (S.image X hX).energy.E F G =
      S.energy.E (S.toErrorData.imageLift X F) (S.toErrorData.imageLift X G) :=
  S.toErrorData.imageData_energy X F G

/-- The image diagonal is the RN derivative of the pushed-forward error measure. -/
theorem image_Γ_diag_rnDeriv (F : (S.image X hX).dom) :
    ⇑((S.image X hX).Γ F F) =ᵐ[imageLaw X] fun x =>
      (((S.toErrorData.gammaMeasure X F).map (imageRepresentative X)).rnDeriv (imageLaw X) x).toReal := by
  change ⇑(S.toErrorData.imageGamma X F F) =ᵐ[imageLaw X] _
  rw [S.toErrorData.imageGamma_self]
  exact S.toErrorData.imageGammaDiag_ae_eq X F

end ErrorCalculus.ErrorStructure
