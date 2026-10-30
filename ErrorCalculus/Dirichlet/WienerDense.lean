import ErrorCalculus.Dirichlet.WienerCalculus
import Mathlib.MeasureTheory.Measure.SeparableMeasure

noncomputable section
open MeasureTheory Filter Topology Set

namespace ErrorCalculus

/-- Every measurable cylinder with an arbitrary finite support uses an initial segment. -/
theorem measurableCylinder_initial {s : Set (ℕ → ℝ)}
    (hs : s ∈ measurableCylinders (fun _ : ℕ => ℝ)) :
    ∃ N, ∃ t : Set (Fin N → ℝ), MeasurableSet t ∧ s = restrictN N ⁻¹' t := by
  obtain ⟨I, t, ht, rfl⟩ := (mem_measurableCylinders s).mp hs
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range I
  let q : (Fin N → ℝ) → (I → ℝ) := fun x i => x ⟨i.val, Finset.mem_range.mp (hN i.property)⟩
  have hq : Measurable q := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  exact ⟨N, q ⁻¹' t, hq ht, rfl⟩

/-- Pullbacks of indicators are indicators of cylinder preimages. -/
theorem cylLp_indicator (N : ℕ) {t : Set (Fin N → ℝ)} (ht : MeasurableSet t) (c : ℝ) :
    cylLp N 2 (indicatorConstLp 2 ht (measure_ne_top _ _) c) =
      indicatorConstLp 2 ((restrictN_measurable N) ht) (measure_ne_top _ _) c := by
  apply Lp.ext
  filter_upwards [coeFn_cylLp N 2 (indicatorConstLp 2 ht (measure_ne_top _ _) c),
    (restrictN_preserving N).quasiMeasurePreserving.ae
      (indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := measure_ne_top _ _) (c := c)),
    indicatorConstLp_coeFn (p := 2) (hs := (restrictN_measurable N) ht)
      (hμs := measure_ne_top _ _) (c := c)] with x ha hb hc
  rw [ha, Function.comp_apply, hb, hc]
  rfl

/-- The cylinder algebra is measure-dense: Mathlib's generating-algebra monotone-class theorem. -/
theorem measurableCylinders_measureDense :
    wienerCoord.MeasureDense (measurableCylinders (fun _ : ℕ => ℝ)) :=
  Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite wienerCoord
    ⟨empty_mem_measurableCylinders _, fun {_} hs => compl_mem_measurableCylinders hs,
      fun {_ _} hs ht => union_mem_measurableCylinders hs ht⟩ generateFrom_measurableCylinders.symm

/-- A closed linear subspace containing every finite-coordinate L² function is all of L². -/
theorem cylinder_closed_submodule_eq_top (S : Submodule ℝ (Lp ℝ 2 wienerCoord))
    (hS : IsClosed (S : Set (Lp ℝ 2 wienerCoord)))
    (hcyl : ∀ N (u : Lp ℝ 2 (densityMeasureD (ouDensityD N))), cylLp N 2 u ∈ S) : S = ⊤ := by
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hind (c : ℝ) {s : Set (ℕ → ℝ)} (hs : MeasurableSet s) :
      indicatorConstLp 2 hs (measure_ne_top _ _) c ∈ S := by
    have hmem := measurableCylinders_measureDense.indicatorConstLp_subset_closure
      (p := 2) c ⟨s, hs, measure_ne_top _ _, rfl⟩
    apply (closure_minimal (t := (S : Set (Lp ℝ 2 wienerCoord))) ?_ hS) hmem
    rintro _ ⟨t, ht, hμt, rfl⟩
    obtain ⟨N, a, ha, rfl⟩ := measurableCylinder_initial ht
    rw [← cylLp_indicator N ha c]
    exact hcyl N _
  apply top_unique
  intro f _
  apply Lp.induction (p := 2) (by norm_num) (fun f : Lp ℝ 2 wienerCoord => f ∈ S)
    (fun c s hs _ => ?_) (fun _ _ _ _ _ hf hg => S.add_mem hf hg) hS f
  exact hind c hs

/-- All finite-coordinate L² classes, as an increasing union submodule. -/
def cylinderLpDom : Submodule ℝ (Lp ℝ 2 wienerCoord) :=
  ⨆ N, LinearMap.range (cylLp N 2).toLinearMap

theorem cylinderLpDom_mono : Monotone (fun N => LinearMap.range (cylLp N 2).toLinearMap) := by
  intro N M h f hf
  obtain ⟨u, rfl⟩ := hf
  exact ⟨liftLp h 2 u, cylLp_comp h 2 u⟩

theorem cylinderLpDom_eq_union : (cylinderLpDom : Set (Lp ℝ 2 wienerCoord)) =
    ⋃ N, Set.range (cylLp N 2) := by
  ext f
  change f ∈ (⨆ N, LinearMap.range (cylLp N 2).toLinearMap) ↔ _
  rw [Submodule.mem_iSup_of_directed _ cylinderLpDom_mono.directed_le]
  simp only [Set.mem_iUnion, LinearMap.mem_range, Set.mem_range]
  rfl

/-- cylinders are dense in the Gaussian L² space. -/
theorem cylinder_dense : Dense (⋃ N, Set.range (cylLp N 2) : Set (Lp ℝ 2 wienerCoord)) := by
  rw [← cylinderLpDom_eq_union]
  rw [dense_iff_closure_eq]
  change (cylinderLpDom.topologicalClosure : Set (Lp ℝ 2 wienerCoord)) = Set.univ
  have h := cylinder_closed_submodule_eq_top cylinderLpDom.topologicalClosure
    cylinderLpDom.isClosed_topologicalClosure (fun N u => cylinderLpDom.le_topologicalClosure
      (Submodule.mem_iSup_of_mem N ⟨u, rfl⟩))
  rw [h]
  rfl

/-- finite-dimensional smooth density gives density of the cylindrical C¹_b domain. -/
theorem wienerDom_dense : Dense (wienerDom : Set (Lp ℝ 2 wienerCoord)) := by
  rw [dense_iff_closure_eq]
  change (wienerDom.topologicalClosure : Set (Lp ℝ 2 wienerCoord)) = Set.univ
  have h := cylinder_closed_submodule_eq_top wienerDom.topologicalClosure
    wienerDom.isClosed_topologicalClosure (fun N u => ?_)
  · rw [h]; rfl
  have hclosed : IsClosed {v : Lp ℝ 2 (densityMeasureD (ouDensityD N)) |
      cylLp N 2 v ∈ wienerDom.topologicalClosure} :=
    wienerDom.isClosed_topologicalClosure.preimage (cylLp N 2).continuous
  apply (closure_minimal (t := {v | cylLp N 2 v ∈ wienerDom.topologicalClosure}) ?_ hclosed)
    ((dense_protoDomD (ouDensityD N)) u)
  intro v hv
  exact wienerDom.le_topologicalClosure (cylProto N ⟨v, hv⟩).property

end ErrorCalculus
