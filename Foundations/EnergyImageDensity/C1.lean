import Foundations.EnergyImageDensity.Density
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# C1

## Main results
Energy image density for C¹ real functions, by rational interval localization.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace Foundations

/-- The regular set of a C¹ function is open. -/
theorem isOpen_deriv_ne_zero {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) :
    IsOpen {x | deriv u x ≠ 0} :=
  isOpen_ne.preimage (hu.continuous_deriv (by simp))

/-- a rational interval inside an open set contains each of its points. -/
theorem exists_rat_Ioo_subset {s : Set ℝ} (hs : IsOpen s) {x : ℝ} (hx : x ∈ s) :
    ∃ a b : ℚ, x ∈ Ioo (a : ℝ) (b : ℝ) ∧ Ioo (a : ℝ) (b : ℝ) ⊆ s := by
  obtain ⟨v, hv, hxv, hvs⟩ := Real.isTopologicalBasis_Ioo_rat.exists_subset_of_mem_open hx hs
  simp only [mem_iUnion, mem_singleton_iff] at hv
  obtain ⟨a, b, _, rfl⟩ := hv
  exact ⟨a, b, hxv, hvs⟩

/-- The index type is a subtype of ℚ × ℚ, hence countable. -/
theorem open_eq_iUnion_rat_Ioo {s : Set ℝ} (hs : IsOpen s) :
    s = ⋃ p : {p : ℚ × ℚ // Ioo (p.1 : ℝ) (p.2 : ℝ) ⊆ s},
      Ioo (p.val.1 : ℝ) (p.val.2 : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, b, hx, hab⟩ := exists_rat_Ioo_subset hs hx
    exact mem_iUnion.mpr ⟨⟨(a, b), hab⟩, hx⟩
  · intro hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    exact p.property hp

/-- a continuous nonvanishing derivative has constant sign on an interval. -/
theorem deriv_pos_or_neg_on_Ioo {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) {a b : ℝ}
    (hn : ∀ x ∈ Ioo a b, deriv u x ≠ 0) :
    (∀ x ∈ Ioo a b, 0 < deriv u x) ∨ (∀ x ∈ Ioo a b, deriv u x < 0) := by
  classical
  by_cases hp : ∀ x ∈ Ioo a b, 0 < deriv u x
  · exact Or.inl hp
  right
  push Not at hp
  obtain ⟨y, hy, hdy⟩ := hp
  intro x hx
  by_contra hdx
  obtain ⟨z, hz, hdz⟩ := isPreconnected_Ioo.intermediate_value hy hx
    (hu.continuous_deriv (by simp)).continuousOn ⟨hdy, le_of_not_gt hdx⟩
  exact hn z hz hdz

/-- strict monotonicity gives injectivity on every regular interval. -/
theorem injOn_Ioo_of_deriv_ne_zero {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) {a b : ℝ}
    (hn : ∀ x ∈ Ioo a b, deriv u x ≠ 0) : InjOn u (Ioo a b) := by
  rcases deriv_pos_or_neg_on_Ioo hu hn with hp | hm
  · exact (strictMonoOn_of_deriv_pos (convex_Ioo a b) hu.continuous.continuousOn
      (fun x hx => hp x (interior_subset hx))).injOn
  · exact (strictAntiOn_of_deriv_neg (convex_Ioo a b) hu.continuous.continuousOn
      (fun x hx => hm x (interior_subset hx))).injOn

/-- The one-dimensional measure form of injective change of variables. -/
theorem map_withDensity_abs_deriv_eq_volume_restrict {u d : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, HasDerivWithinAt u (d x) s x)
    (hi : InjOn u s) :
    ((volume.restrict s).withDensity (fun x => ENNReal.ofReal |d x|)).map u =
      volume.restrict (u '' s) := by
  simpa only [ContinuousLinearMap.det_toSpanSingleton] using
    map_withDensity_abs_det_fderiv_eq_addHaar volume hs.nullMeasurableSet
      (fun x hx => (hd x hx).hasFDerivWithinAt) hi

/-- Change of variables on each rational interval in the regular set. -/
theorem map_withDensity_abs_deriv_restrict_Ioo {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    {a b : ℝ} (hn : ∀ x ∈ Ioo a b, deriv u x ≠ 0) :
    ((volume.restrict (Ioo a b)).withDensity (fun x => ENNReal.ofReal |deriv u x|)).map u =
      volume.restrict (u '' Ioo a b) :=
  map_withDensity_abs_deriv_eq_volume_restrict measurableSet_Ioo
    (fun x _ => ((hu.differentiable (by simp)) x).hasDerivAt.hasDerivWithinAt)
    (injOn_Ioo_of_deriv_ne_zero hu hn)

/-- no injectivity or boundedness assumption is imposed on the C¹ function. -/
theorem map_withDensity_abs_deriv_absolutelyContinuous {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) :
    (volume.withDensity (fun x => ENNReal.ofReal |deriv u x|)).map u ≪ volume := by
  let U := {x | deriv u x ≠ 0}
  have hU : IsOpen U := isOpen_deriv_ne_zero hu
  have hs : (volume.withDensity (fun x => ENNReal.ofReal |deriv u x|)).restrict U =
      volume.withDensity (fun x => ENNReal.ofReal |deriv u x|) :=
    withDensity_restrict_eq_self_of_zero_outside (measurable_deriv u).norm.ennreal_ofReal
      (fun x hx => by simp_all [U])
  rw [← hs, open_eq_iUnion_rat_Ioo hU]
  apply map_absolutelyContinuous_of_restrict_iUnion hu.continuous.measurable
  intro p
  rw [restrict_withDensity measurableSet_Ioo,
    map_withDensity_abs_deriv_restrict_Ioo hu (fun x hx => p.property hx)]
  exact Measure.restrict_le_self.absolutelyContinuous

/-- restriction to a Borel set preserves energy image density. -/
theorem map_withDensity_abs_deriv_restrict_absolutelyContinuous {u : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) {s : Set ℝ} (hs : MeasurableSet s) :
    ((volume.restrict s).withDensity (fun x => ENNReal.ofReal |deriv u x|)).map u ≪ volume := by
  rw [← restrict_withDensity hs]
  exact ((Measure.map_mono Measure.restrict_le_self hu.continuous.measurable).absolutelyContinuous).trans
    (map_withDensity_abs_deriv_absolutelyContinuous hu)

/-- arbitrary measurable real weights are admitted via `ofReal` (in particular ρ ≥ 0). -/
theorem map_withDensity_sq_deriv_mul_absolutelyContinuous {u ρ : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) (hρ : Measurable ρ) :
    (volume.withDensity (fun x => ENNReal.ofReal ((deriv u x)^2 * ρ x))).map u ≪ volume := by
  have hac := withDensity_absolutelyContinuous_of_zero_imp (μ := volume)
    (((measurable_deriv u).pow_const 2).mul hρ).ennreal_ofReal
    (measurable_deriv u).norm.ennreal_ofReal (fun x hx => by
      have hd : deriv u x = 0 := abs_eq_zero.mp
        (le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (abs_nonneg _))
      simp [hd])
  exact (hac.map hu.continuous.measurable).trans
    (map_withDensity_abs_deriv_absolutelyContinuous hu)

end Foundations
