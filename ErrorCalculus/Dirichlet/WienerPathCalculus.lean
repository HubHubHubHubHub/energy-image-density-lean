import ErrorCalculus.Dirichlet.WienerPathBrownian

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology Foundations
open scoped NNReal
namespace ErrorCalculus

theorem coeFn_canonicalProcessDom (t : WienerTime) :
    ⇑(canonicalProcessDom t : Lp ℝ 2 wienerMeasure) =ᵐ[wienerMeasure] canonicalProcess t :=
  (memLp_canonicalProcess t).coeFn_toLp

/--
finite C¹ Lipschitz Brownian cylinders and their full diagonal chain rule. The input class may be
any representative of the indicated composition.
-/
theorem wienerPathStructure_Γ_comp_canonicalProcess {n : ℕ} (hn : 0 < n)
    (t : Fin n → WienerTime) (F : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hC : ContDiff ℝ 1 F) (hL : LipschitzWith L F) (w : Lp ℝ 2 wienerMeasure)
    (hw : ⇑w =ᵐ[wienerMeasure] fun ω => F (fun i => canonicalProcess (t i) ω)) :
    ∃ hd : w ∈ wienerPathStructure.dom,
      ⇑(wienerPathStructure.Γ ⟨w,hd⟩ ⟨w,hd⟩) =ᵐ[wienerMeasure] fun ω =>
        ∑ i, ∑ j, fderiv ℝ F (fun k => canonicalProcess (t k) ω) (Pi.single i 1) *
          fderiv ℝ F (fun k => canonicalProcess (t k) ω) (Pi.single j 1) *
          (min (t i : ℝ≥0) (t j : ℝ≥0) : ℝ) := by
  have hu := ae_all_iff.mpr (fun i => coeFn_canonicalProcessDom (t i))
  have hw' : ⇑w =ᵐ[wienerMeasure]
      fun ω => F (fun i => (canonicalProcessDom (t i) : Lp ℝ 2 wienerMeasure) ω) := by
    filter_upwards [hw, hu] with ω hw hu
    simpa only [hu] using hw
  obtain ⟨hd,hg⟩ := wienerPathStructure.calc n hn (fun i => canonicalProcessDom (t i))
    F L hC hL w hw'
  refine ⟨hd, ?_⟩
  filter_upwards [hg ⟨w,hd⟩, ae_all_iff.mpr (fun i => hg (canonicalProcessDom (t i))),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
      wienerPathStructure_Γ_canonicalProcess_ae (t i) (t j))), hu] with ω hww hi hij hu
  rw [hww]
  simp only [hu]
  apply Finset.sum_congr rfl
  intro i _
  rw [wienerPathStructure.Γ_symm (canonicalProcessDom (t i)) ⟨w,hd⟩, hi i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [hu, hij, min_comm, mul_assoc]

/-- Existence of the L² class is supplied by the same Lipschitz calculus API. -/
theorem exists_wienerPathStructure_comp_canonicalProcess {n : ℕ} (hn : 0 < n)
    (t : Fin n → WienerTime) (F : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hC : ContDiff ℝ 1 F) (hL : LipschitzWith L F) :
    ∃ w : wienerPathStructure.dom,
      ⇑(w : Lp ℝ 2 wienerMeasure) =ᵐ[wienerMeasure]
        fun ω => F (fun i => canonicalProcess (t i) ω) := by
  obtain ⟨w,hw⟩ := ErrorStructure.exists_composition
    (fun i => (canonicalProcessDom (t i) : Lp ℝ 2 wienerMeasure)) hL
  have hw' : ⇑w =ᵐ[wienerMeasure] fun ω => F (fun i => canonicalProcess (t i) ω) := by
    filter_upwards [hw, ae_all_iff.mpr (fun i => coeFn_canonicalProcessDom (t i))] with ω hw hu
    simpa only [hu] using hw
  exact ⟨⟨w, (wienerPathStructure_Γ_comp_canonicalProcess hn t F L hC hL w hw').choose⟩, hw'⟩

end ErrorCalculus
