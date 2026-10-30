import ErrorCalculus.Dirichlet.ClosureData

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorData
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S R : ErrorData Ω μ)

/-- Gamma limits agree with an existing domain point; closability already suffices. -/
theorem gamma_characterization (h : S.energy.IsClosable) {u w : ℕ → S.dom} {v z : S.dom}
    (hu : S.energy.Approaches u v) (hw : S.energy.Approaches w z) :
    Tendsto (fun n => S.Γ (u n) (w n)) atTop (𝓝 (S.Γ v z)) := by
  have ht := S.closureGamma_characterization h (a := S.energy.inclusion v)
    (b := S.energy.inclusion z) hu hw
  rw [S.closureGamma_extends] at ht
  exact ht

/-- A gamma extension automatically extends the mixed energy form. -/
theorem energy_extends_of_gamma (hd : S.dom ≤ R.dom)
    (hg : ∀ u v : S.dom, R.Γ (Submodule.inclusion hd u) (Submodule.inclusion hd v) = S.Γ u v) :
    S.energy.Extends R.energy := by
  refine ⟨hd, fun u v => ?_⟩
  change (1/2:ℝ) * ∫ ω, R.Γ (Submodule.inclusion hd u) (Submodule.inclusion hd v) ω ∂μ =
    (1/2:ℝ) * ∫ ω, S.Γ u v ω ∂μ
  rw [hg]

/--
any closed gamma extension contains the closure domain and agrees with the closed gamma. The
stronger statement needs only ErrorData with closed energy, not functional calculus.
-/
theorem closureGamma_unique (h : S.energy.IsClosable) (hR : R.energy.IsClosed)
    (hd : S.dom ≤ R.dom)
    (hg : ∀ u v : S.dom, R.Γ (Submodule.inclusion hd u) (Submodule.inclusion hd v) = S.Γ u v) :
    ∃ hbar : S.energy.closureDom ≤ R.dom, ∀ u v : S.energy.closureDom,
      R.Γ (Submodule.inclusion hbar u) (Submodule.inclusion hbar v) = S.closureGamma h u v := by
  have hE := S.energy_extends_of_gamma R hd hg
  let hbar := S.energy.closureDom_le R.energy hR hE
  refine ⟨hbar, fun u v => ?_⟩
  obtain ⟨un, hun⟩ := (S.energy.mem_closureDom_iff u).mp u.property
  obtain ⟨vn, hvn⟩ := (S.energy.mem_closureDom_iff v).mp v.property
  have huR : R.energy.Approaches (fun n => Submodule.inclusion hd (un n))
      (Submodule.inclusion hbar u) := ⟨hE.isCauchy S.energy R.energy hun.1, hun.2⟩
  have hvR : R.energy.Approaches (fun n => Submodule.inclusion hd (vn n))
      (Submodule.inclusion hbar v) := ⟨hE.isCauchy S.energy R.energy hvn.1, hvn.2⟩
  have ht := R.gamma_characterization (hR.isClosable R.energy) huR hvR
  simp only [hg] at ht
  exact tendsto_nhds_unique ht (S.closureGamma_characterization h hun hvn)

end ErrorCalculus.ErrorData
