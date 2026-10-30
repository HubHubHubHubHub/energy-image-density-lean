import Foundations.EnergyImageDensity.C1
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# countable injective decomposition and the Lipschitz case.

## Main results
The decomposition uses only differentiability on the regular set. With Mathlib's zero convention for
`deriv`, measurable real functions already satisfy the weighted conclusion. Rademacher additionally
identifies this derivative with the classical a.e. derivative.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Foundations

/-- In dimension one an error smaller than the linear slope forces injectivity. -/
theorem injOn_of_approximatesLinearOn_real {u : ℝ → ℝ} {A : ℝ →L[ℝ] ℝ}
    {s : Set ℝ} {c : ℝ≥0} (h : ApproximatesLinearOn u A s c)
    (hc : (c : ℝ) < |A 1|) : InjOn u s := by
  have hA (z : ℝ) : A z = z * A 1 := by
    simpa only [smul_eq_mul, mul_one] using A.map_smul z (1 : ℝ)
  intro x hx y hy hxy
  by_contra hn
  have hp : 0 < |x-y| := abs_pos.mpr (sub_ne_zero.mpr hn)
  have hh := h x hx y hy
  simp only [hxy, sub_self, zero_sub, norm_neg] at hh
  rw [hA (x-y), norm_mul] at hh
  simp only [Real.norm_eq_abs] at hh
  nlinarith

/--
measurable injective pieces cover exactly the nonzero-derivative set. No Lipschitz or continuity
hypothesis is needed for this decomposition.
-/
theorem exists_injective_partition_deriv_ne_zero (u : ℝ → ℝ) :
    ∃ s : ℕ → Set ℝ, (∀ n, MeasurableSet (s n)) ∧
      (⋃ n, s n) = {x | deriv u x ≠ 0} ∧
      (∀ n, InjOn u (s n)) ∧
      (∀ n x, x ∈ s n → DifferentiableAt ℝ u x) := by
  classical
  let D := {x | deriv u x ≠ 0}
  let r : (ℝ →L[ℝ] ℝ) → ℝ≥0 := fun A => if A 1 = 0 then 1 else ‖A 1‖₊ / 2
  have hr : ∀ A, r A ≠ 0 := by
    intro A
    dsimp [r]
    split_ifs with hA
    · exact one_ne_zero
    · exact div_ne_zero (by simpa using hA) (by norm_num)
  have hd : ∀ x ∈ D, HasFDerivWithinAt u
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv u x)) D x := by
    intro x hx
    exact (differentiableAt_of_deriv_ne_zero hx).hasDerivAt.hasFDerivAt.hasFDerivWithinAt
  obtain ⟨t, A, _, ht, hcover, happ, hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt u D _ hd r hr
  have hD : MeasurableSet D := ((measurable_deriv u) (measurableSet_singleton 0)).compl
  refine ⟨fun n => D ∩ t n, fun n => hD.inter (ht n), ?_, ?_, ?_⟩
  · ext x
    simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => by
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover hx)
      exact ⟨n, hx, hn⟩⟩
  · intro n
    by_cases hne : D.Nonempty
    · obtain ⟨y, hy, hay⟩ := hA hne n
      have han : A n 1 ≠ 0 := by simpa [hay] using (show deriv u y ≠ 0 from hy)
      apply injOn_of_approximatesLinearOn_real (happ n)
      simp only [r, if_neg han, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs]
      have hp := abs_pos.mpr han
      linarith
    · intro x hx
      exact (hne ⟨x, hx.1⟩).elim
  · intro n x hx
    exact differentiableAt_of_deriv_ne_zero hx.1

/-- The derivative-weighted conclusion holds for any measurable real map. -/
theorem map_withDensity_abs_deriv_absolutelyContinuous_of_measurable {u : ℝ → ℝ}
    (hu : Measurable u) :
    (volume.withDensity (fun x => ENNReal.ofReal |deriv u x|)).map u ≪ volume := by
  obtain ⟨s, hs, hcover, hi, hd⟩ := exists_injective_partition_deriv_ne_zero u
  have hsupport : (volume.withDensity (fun x => ENNReal.ofReal |deriv u x|)).restrict
      {x | deriv u x ≠ 0} = volume.withDensity (fun x => ENNReal.ofReal |deriv u x|) :=
    withDensity_restrict_eq_self_of_zero_outside (measurable_deriv u).norm.ennreal_ofReal
      (fun x hx => by simp_all)
  rw [← hsupport, ← hcover]
  apply map_absolutelyContinuous_of_restrict_iUnion hu
  intro n
  rw [restrict_withDensity (hs n), map_withDensity_abs_deriv_eq_volume_restrict (hs n)
    (fun x hx => (hd n x hx).hasDerivAt.hasDerivWithinAt) (hi n)]
  exact Measure.restrict_le_self.absolutelyContinuous

/-- The Lipschitz energy-image theorem, with no injectivity assumption. -/
theorem LipschitzWith.map_withDensity_abs_deriv_absolutelyContinuous {u : ℝ → ℝ}
    {L : ℝ≥0} (hu : LipschitzWith L u) :
    (volume.withDensity (fun x => ENNReal.ofReal |deriv u x|)).map u ≪ volume :=
  map_withDensity_abs_deriv_absolutelyContinuous_of_measurable hu.continuous.measurable

/-- The same strengthening applies to the energy density with a measurable weight. -/
theorem map_withDensity_sq_deriv_mul_absolutelyContinuous_of_measurable {u ρ : ℝ → ℝ}
    (hu : Measurable u) (hρ : Measurable ρ) :
    (volume.withDensity (fun x => ENNReal.ofReal ((deriv u x)^2 * ρ x))).map u ≪ volume := by
  have hac := withDensity_absolutelyContinuous_of_zero_imp (μ := volume)
    (((measurable_deriv u).pow_const 2).mul hρ).ennreal_ofReal
    (measurable_deriv u).norm.ennreal_ofReal (fun x hx => by
      have hd : deriv u x = 0 := abs_eq_zero.mp
        (le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (abs_nonneg _))
      simp [hd])
  exact (hac.map hu).trans (map_withDensity_abs_deriv_absolutelyContinuous_of_measurable hu)

/-- EID for arbitrary measurable nonnegative weights and Lipschitz maps. -/
theorem LipschitzWith.map_withDensity_sq_deriv_mul_absolutelyContinuous {u ρ : ℝ → ℝ}
    {L : ℝ≥0} (hu : LipschitzWith L u) (hρ : Measurable ρ) :
    (volume.withDensity (fun x => ENNReal.ofReal ((deriv u x)^2 * ρ x))).map u ≪ volume :=
  map_withDensity_sq_deriv_mul_absolutelyContinuous_of_measurable hu.continuous.measurable hρ

/-- Rademacher makes the exceptional nondifferentiability set null. -/
theorem LipschitzWith.volume_not_differentiableAt {u : ℝ → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) : volume {x | ¬ DifferentiableAt ℝ u x} = 0 := by
  exact (ae_iff.mp (hu.ae_differentiableAt (μ := volume)))

/-- Lipschitz maps carry Lebesgue-null sets to null sets, via Hausdorff measure. -/
theorem LipschitzWith.volume_image_eq_zero {u : ℝ → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) {s : Set ℝ} (hs : volume s = 0) : volume (u '' s) = 0 := by
  have h := hu.hausdorffMeasure_image_le (d := 1) (by norm_num) s
  simpa [hausdorffMeasure_real, hs] using h

/-- In particular, the image of the Rademacher exceptional set is null. -/
theorem LipschitzWith.volume_image_not_differentiableAt {u : ℝ → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) : volume (u '' {x | ¬ DifferentiableAt ℝ u x}) = 0 :=
  LipschitzWith.volume_image_eq_zero hu (LipschitzWith.volume_not_differentiableAt hu)

end Foundations
