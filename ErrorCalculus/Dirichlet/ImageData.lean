import ErrorCalculus.Dirichlet.ImageGamma

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Constants pull back to the same constants. -/
theorem pullback_const {m : ℕ} (X : Fin m → Lp ℝ 2 μ) (c : ℝ) :
    pullback X (Lp.const 2 (imageLaw X) c) = Lp.const 2 μ c := by
  apply Lp.ext
  have hc := ae_eq_comp (measurable_imageRepresentative X).aemeasurable
    (Lp.coeFn_const (p := 2) (μ := imageLaw X) (c := c))
  exact (pullback_ae_eq X _).trans (hc.trans (Lp.coeFn_const (p := 2) (μ := μ) (c := c)).symm)

namespace ErrorData
variable (S : ErrorData Ω μ) {m : ℕ} (X : Fin m → Lp ℝ 2 μ)

/-- error data on the exact inverse-image domain. -/
def imageData : ErrorData (Fin m → ℝ) (imageLaw X) where
  dom := S.imageDom X
  Γ := S.imageGammaBilinear X
  Γ_symm := S.imageGamma_symm X
  Γ_nonneg F := by
    change 0 ≤ᵐ[imageLaw X] ⇑(S.imageGamma X F F)
    rw [S.imageGamma_self]
    exact S.imageGammaDiag_nonneg X F

/-- mixed energy is precisely the source energy of the pullbacks. -/
theorem imageData_energy (F G : S.imageDom X) :
    (S.imageData X).energy.E F G = S.energy.E (S.imageLift X F) (S.imageLift X G) := by
  have h := S.imageGamma_characterization X F G ImageTest.one
  have he : (ImageTest.one.comp (imageRepresentative X) (measurable_imageRepresentative X)) =
      (ImageTest.one : ImageTest Ω) := rfl
  rw [he, ImageTest.integral_one, ImageTest.integral_one] at h
  change (1/2:ℝ) * (∫ x, S.imageGamma X F G x ∂imageLaw X) = _
  rw [h]; rfl

theorem imageData_seminorm (F : S.imageDom X) :
    (S.imageData X).energy.seminorm F = S.energy.seminorm (S.imageLift X F) := by
  simp only [QuadForm.seminorm, S.imageData_energy]

/-- closedness descends along the isometric pullback. -/
theorem imageData_isClosed (h : S.energy.IsClosed) : (S.imageData X).energy.IsClosed := by
  intro u hu v hv
  change ℕ → S.imageDom X at u
  have ht : Tendsto (fun n => pullback X (u n)) atTop (𝓝 (pullback X v)) :=
    ((pullback X).continuous.tendsto v).comp hv
  have hc : S.energy.IsCauchy (fun n => S.imageLift X (u n)) := by
    apply (S.energy.isCauchy_iff _).mpr
    refine ⟨ht.cauchySeq, ?_⟩
    intro ε hε
    obtain ⟨N, hN⟩ := ((S.imageData X).energy.isCauchy_iff u).mp hu |>.2 ε hε
    refine ⟨N, fun a ha b hb => ?_⟩
    have he := hN a ha b hb
    rw [S.imageData_seminorm] at he
    change S.energy.seminorm (S.imageLift X (u a - u b)) < ε at he
    rwa [map_sub] at he
  obtain ⟨hd, he⟩ := h _ hc (pullback X v) ht
  refine ⟨hd, ?_⟩
  convert he using 1
  ext n
  rw [S.imageData_energy]
  change S.energy.E (S.imageLift X (u n - (⟨v, hd⟩ : S.imageDom X)))
    (S.imageLift X (u n - (⟨v, hd⟩ : S.imageDom X))) = _
  rw [map_sub (S.imageLift X)]
  rfl

/-- The unit belongs to the image domain. -/
theorem imageData_one_mem (h : Lp.const 2 μ (1 : ℝ) ∈ S.dom) :
    Lp.const 2 (imageLaw X) (1 : ℝ) ∈ (S.imageData X).dom := by
  change pullback X (Lp.const 2 (imageLaw X) 1) ∈ S.dom
  rwa [pullback_const]

end ErrorData
end ErrorCalculus
