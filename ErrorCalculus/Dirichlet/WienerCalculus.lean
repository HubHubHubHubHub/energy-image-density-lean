import ErrorCalculus.Dirichlet.WienerPartial

noncomputable section
open MeasureTheory Filter
open scoped NNReal

namespace ErrorCalculus

/-- Composition commutes with a finite-level pullback, at the level of L² classes. -/
theorem cylLp_composition {N m : ℕ} (u : Fin m → protoDomD (ouDensityD N))
    (F : (Fin m → ℝ) → ℝ) (w : Lp ℝ 2 (densityMeasureD (ouDensityD N)))
    (hw : ⇑w =ᵐ[densityMeasureD (ouDensityD N)] fun x => F (fun j => (u j : Lp ℝ 2 (densityMeasureD (ouDensityD N))) x)) :
    ⇑(cylLp N 2 w) =ᵐ[wienerCoord] fun x => F (fun j => (cylProto N (u j) : Lp ℝ 2 wienerCoord) x) := by
  have hu := ae_all_iff.mpr (fun j => coeFn_cylLp N 2 (u j : Lp ℝ 2 (densityMeasureD (ouDensityD N))))
  filter_upwards [coeFn_cylLp N 2 w, (restrictN_preserving N).quasiMeasurePreserving.ae hw, hu]
    with x ha hb hc
  rw [ha, Function.comp_apply, hb]
  congr 1
  exact funext fun j => (hc j).symm

/-- calculus supplies a domain representative of a cylindrical composition. -/
theorem exists_cyl_composition {N m : ℕ} (hm : 0 < m) (u : Fin m → protoDomD (ouDensityD N))
    (F : (Fin m → ℝ) → ℝ) (L : ℝ≥0) (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) :
    ∃ w : protoDomD (ouDensityD N),
      (⇑(w : Lp ℝ 2 (densityMeasureD (ouDensityD N))) =ᵐ[densityMeasureD (ouDensityD N)] fun x => F (fun j => (u j : Lp ℝ 2 (densityMeasureD (ouDensityD N))) x)) ∧
      ∀ v : protoDomD (ouDensityD N),
        ⇑(gammaD _ w v) =ᵐ[densityMeasureD (ouDensityD N)] fun x => ∑ j,
          fderiv ℝ F (fun k => (u k : Lp ℝ 2 (densityMeasureD (ouDensityD N))) x) (Pi.single j 1) * gammaD _ (u j) v x := by
  obtain ⟨w, hw⟩ := ErrorStructure.exists_composition (fun j => (u j : Lp ℝ 2 (densityMeasureD (ouDensityD N)))) hL
  obtain ⟨hd, hc⟩ := protoData_calculusD (ouDensityD N) m hm u F L hF hL w hw
  exact ⟨⟨w, hd⟩, hw, hc⟩

/-- full C¹ Lipschitz calculus in the proto-structure signature. -/
theorem wienerProto_calculus (m : ℕ) (hm : 0 < m) (u : Fin m → wienerDom)
    (F : (Fin m → ℝ) → ℝ) (L : ℝ≥0) (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F)
    (W : Lp ℝ 2 wienerCoord)
    (hW : ⇑W =ᵐ[wienerCoord] fun x => F (fun j => (u j : Lp ℝ 2 wienerCoord) x)) :
    ∃ hD : W ∈ wienerDom, ∀ v : wienerDom,
      ⇑(wienerGamma ⟨W, hD⟩ v) =ᵐ[wienerCoord] fun x => ∑ j,
        fderiv ℝ F (fun k => (u k : Lp ℝ 2 wienerCoord) x) (Pi.single j 1) * wienerGamma (u j) v x := by
  have hD : W ∈ wienerDom := by
    obtain ⟨N, a, ha⟩ := exists_common_level u
    obtain ⟨w, hw, _⟩ := exists_cyl_composition hm a F L hF hL
    have he : cylLp N 2 (w : Lp ℝ 2 (densityMeasureD (ouDensityD N))) = W := by
      apply Lp.ext
      exact (cylLp_composition a F _ hw).trans (by simpa only [ha] using hW.symm)
    exact he ▸ (cylProto N w).property
  refine ⟨hD, fun v => ?_⟩
  let family : Option (Fin m) → wienerDom := fun j => j.elim v u
  obtain ⟨N, a, ha⟩ := exists_common_level family
  let b : Fin m → protoDomD (ouDensityD N) := fun j => a (some j)
  have hb (j) : cylProto N (b j) = u j := ha (some j)
  have hv : cylProto N (a none) = v := ha none
  obtain ⟨w, hw, hc⟩ := exists_cyl_composition hm b F L hF hL
  have he : cylProto N w = (⟨W, hD⟩ : wienerDom) := by
    apply Subtype.ext
    apply Lp.ext
    exact (cylLp_composition b F _ hw).trans (by simpa only [hb] using hW.symm)
  have hg (j) : wienerGamma (u j) v = cylLp N 1 (gammaD _ (b j) (a none)) :=
    wienerGamma_at _ _ _ _ (hb j) hv
  have hu : ∀ᵐ x ∂wienerCoord, ∀ j,
      (u j : Lp ℝ 2 wienerCoord) x = (b j : Lp ℝ 2 (densityMeasureD (ouDensityD N))) (restrictN N x) := by
    apply ae_all_iff.mpr
    intro j
    rw [← hb j]
    exact coeFn_cylLp N 2 _
  have hgam : ∀ᵐ x ∂wienerCoord, ∀ j,
      wienerGamma (u j) v x = gammaD _ (b j) (a none) (restrictN N x) := by
    apply ae_all_iff.mpr
    intro j
    rw [hg j]
    exact coeFn_cylLp N 1 _
  rw [wienerGamma_at _ _ w (a none) he hv]
  filter_upwards [coeFn_cylLp N 1 (gammaD _ w (a none)),
    (restrictN_preserving N).quasiMeasurePreserving.ae (hc (a none)), hu, hgam] with x h₁ h₂ h₃ h₄
  rw [h₁, Function.comp_apply, h₂]
  have ht : (fun j => (u j : Lp ℝ 2 wienerCoord) x) = fun j => (b j : Lp ℝ 2 (densityMeasureD (ouDensityD N))) (restrictN N x) := funext h₃
  rw [ht]
  exact Finset.sum_congr rfl (fun j _ => by rw [h₄ j])

end ErrorCalculus
