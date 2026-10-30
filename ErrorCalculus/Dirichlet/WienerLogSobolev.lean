import ErrorCalculus.Dirichlet.OUDLogSobolev
import ErrorCalculus.Dirichlet.WienerLogSobolevCyl
import ErrorCalculus.Dirichlet.WienerPathCalculus

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus

/-- Restriction preserves the entropy of every finite-dimensional L² class. -/
theorem entropy_cylLp_sq (N : ℕ) (u : Lp ℝ 2 (densityMeasureD (ouDensityD N))) :
    entropy wienerCoord (fun x => (cylLp N 2 u x)^2) =
      entropy (densityMeasureD (ouDensityD N)) (fun x => (u x)^2) := by
  have hm : AEStronglyMeasurable (fun x => (u x)^2) (densityMeasureD (ouDensityD N)) := by
    exact (continuous_pow 2).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)
  calc
    _ = entropy wienerCoord ((fun x => (u x)^2) ∘ restrictN N) := by
      apply entropy_congr_ae
      filter_upwards [coeFn_cylLp N 2 u] with x hx
      exact congrArg (fun z => z^2) hx
    _ = _ := entropy_comp_measurePreserving (restrictN_preserving N) hm

/-- The integrability part of entropy also survives the cylindrical pullback. -/
theorem integrable_cylLp_sq_mul_log (N : ℕ) (u : Lp ℝ 2 (densityMeasureD (ouDensityD N)))
    (h : Integrable (fun x => (u x)^2 * Real.log ((u x)^2)) (densityMeasureD (ouDensityD N))) :
    Integrable (fun x => (cylLp N 2 u x)^2 * Real.log ((cylLp N 2 u x)^2)) wienerCoord := by
  have hi := ((restrictN_preserving N).integrable_comp h.aestronglyMeasurable).mpr h
  apply hi.congr
  filter_upwards [coeFn_cylLp N 2 u] with x hx
  exact (congrArg (fun z => z^2 * Real.log (z^2)) hx).symm

/-- Restriction preserves the entropy of every finite-dimensional OU domain element. -/
theorem entropy_wienerOU (N : ℕ) (u : (ouStructureD N).dom) :
    entropy wienerCoord (fun x => ((wienerOU N u : Lp ℝ 2 wienerCoord) x)^2) =
      entropy (densityMeasureD (ouDensityD N))
        (fun x => ((u : Lp ℝ 2 (densityMeasureD (ouDensityD N))) x)^2) :=
  entropy_cylLp_sq N u

/-- The cylindrical hypothesis of now discharged on the full OU_N domain. -/
theorem wienerOU_logSobolev (N : ℕ) (u : (ouStructureD N).dom) :
    Integrable (fun x => ((wienerOU N u : Lp ℝ 2 wienerCoord) x)^2 *
      Real.log (((wienerOU N u : Lp ℝ 2 wienerCoord) x)^2)) wienerCoord ∧
    entropy wienerCoord (fun x => ((wienerOU N u : Lp ℝ 2 wienerCoord) x)^2) ≤
      4 * wienerStructure.energy.E (wienerOU N u) (wienerOU N u) := by
  have h := ouStructureD_hasLogSobolev N u
  refine ⟨integrable_cylLp_sq_mul_log N u h.1, ?_⟩
  rw [entropy_wienerOU, wienerOU_energy]
  exact h.2

/-- Gross's inequality on the closed Wiener coordinate structure. -/
theorem wienerStructure_hasLogSobolev : wienerStructure.HasLogSobolev 4 :=
  wienerStructure_hasLogSobolev_of_cyl wienerOU_logSobolev

/-- Gross's inequality for Wiener measure on continuous paths. -/
theorem wienerPathStructure_hasLogSobolev : wienerPathStructure.HasLogSobolev 4 :=
  transport_hasLogSobolev wienerPathIso wienerStructure_hasLogSobolev

/-- The Brownian cylinder formula, including integrability, for every C¹ Lipschitz F. -/
theorem wienerPath_logSobolev_comp_canonicalProcess {n : ℕ} (hn : 0 < n)
    (t : Fin n → Foundations.WienerTime) (F : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hC : ContDiff ℝ 1 F) (hL : LipschitzWith L F) :
    Integrable (fun ω => (F (fun i => Foundations.canonicalProcess (t i) ω))^2 *
      Real.log ((F (fun i => Foundations.canonicalProcess (t i) ω))^2))
        Foundations.wienerMeasure ∧
    entropy Foundations.wienerMeasure
      (fun ω => (F (fun i => Foundations.canonicalProcess (t i) ω))^2) ≤
      2 * ∫ ω, ∑ i, ∑ j,
        Foundations.partialD F i (fun k => Foundations.canonicalProcess (t k) ω) *
        Foundations.partialD F j (fun k => Foundations.canonicalProcess (t k) ω) *
        (min (t i : ℝ≥0) (t j : ℝ≥0) : ℝ) ∂Foundations.wienerMeasure := by
  obtain ⟨w, hw⟩ := exists_wienerPathStructure_comp_canonicalProcess hn t F L hC hL
  obtain ⟨hd, hΓ⟩ := wienerPathStructure_Γ_comp_canonicalProcess hn t F L hC hL w hw
  have hh := wienerPathStructure_hasLogSobolev (⟨w, hd⟩ : wienerPathStructure.dom)
  have hlog := hw.fun_comp (fun z => z^2 * Real.log (z^2))
  have hsq := hw.fun_comp (fun z => z^2)
  simp only [Function.comp_def] at hlog hsq
  refine ⟨hh.1.congr hlog, ?_⟩
  rw [entropy_congr_ae hsq] at hh
  have he : 4 * wienerPathStructure.energy.E ⟨w, hd⟩ ⟨w, hd⟩ =
      2 * ∫ ω, ∑ i, ∑ j,
        Foundations.partialD F i (fun k => Foundations.canonicalProcess (t k) ω) *
        Foundations.partialD F j (fun k => Foundations.canonicalProcess (t k) ω) *
        (min (t i : ℝ≥0) (t j : ℝ≥0) : ℝ) ∂Foundations.wienerMeasure := by
    change 4 * ((1/2 : ℝ) * ∫ ω, wienerPathStructure.Γ _ _ ω ∂_) = _
    rw [integral_congr_ae hΓ]
    dsimp only [Foundations.partialD]
    ring
  exact he ▸ hh.2

end ErrorCalculus
