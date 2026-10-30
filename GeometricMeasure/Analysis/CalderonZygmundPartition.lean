import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Countable partitions preserving selected balls

## Main results
A countable partition preserves the selected small balls. A counterexample records the failure of
the naive construction.

Bibliographic context: Hart Smith, Lecture 8, pp. 2–4; De Philippis–Rindler, pp. 1027–1028. These
page locators are unverified against those editions.
-/

noncomputable section
open MeasureTheory Set
namespace GeometricMeasure.CalderonZygmund
variable {X I : Type*}

/--
Piece retaining its core and removing all cores before the lower-ranked envelopes. Source: Hart
Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
def cell [Encodable I] (C B : I → Set X) (i : I) : Set X :=
  C i ∪ ((B i \ ⋃ j, C j) \ ⋃ j, ⋃ (_ : Encodable.encode j < Encodable.encode i), B j)

/--
Each core is contained in its own piece, without additional assumptions. Source: Hart Smith, Lecture
8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem subset_cell [Encodable I] (C B : I → Set X) (i : I) :
    C i ⊆ cell C B i := subset_union_left

/--
Each piece stays inside its envelope when every core is contained in its envelope. Source: Hart
Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
theorem cell_subset [Encodable I] {C B : I → Set X} (hCB : ∀ i, C i ⊆ B i) (i : I) :
    cell C B i ⊆ B i := by
  intro x hx
  rcases hx with hx | hx
  · exact hCB i hx
  · exact hx.1.1

/--
Disjointness of the cores implies disjointness of pieces with injective ranks. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem cell_pairwiseDisjoint [Encodable I] {C B : I → Set X}
    (hC : Pairwise (fun i j => Disjoint (C i) (C j))) : Pairwise (fun i j => Disjoint (cell C B i) (cell C B j)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro x hi hj
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact Set.disjoint_left.1 (hC hij) hi hj
  · exact hj.1.2 (mem_iUnion.2 ⟨i, hi⟩)
  · exact hi.1.2 (mem_iUnion.2 ⟨j, hj⟩)
  · have he : Encodable.encode i ≠ Encodable.encode j :=
      fun h => hij (Encodable.encode_injective h)
    rcases lt_or_gt_of_ne he with h | h
    · exact hj.2 (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨h, hi.1.1⟩⟩)
    · exact hi.2 (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨h, hj.1.1⟩⟩)

/--
The union of the pieces equals that of the envelopes containing the cores. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem iUnion_cell [Encodable I] {C B : I → Set X} (hCB : ∀ i, C i ⊆ B i) :
    (⋃ i, cell C B i) = ⋃ i, B i := by
  classical
  apply Subset.antisymm
  · exact iUnion_mono (cell_subset hCB)
  · intro x hx
    by_cases hC : x ∈ ⋃ i, C i
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hC
      exact mem_iUnion.2 ⟨i, subset_cell C B i hi⟩
    · have hex : ∃ n : ℕ, ∃ i : I, Encodable.encode i = n ∧ x ∈ B i := by
        obtain ⟨i, hi⟩ := mem_iUnion.1 hx
        exact ⟨_, i, rfl, hi⟩
      obtain ⟨i, hi, hxi⟩ := Nat.find_spec hex
      refine mem_iUnion.2 ⟨i, Or.inr ⟨⟨hxi, hC⟩, ?_⟩⟩
      intro hearlier
      obtain ⟨j, hj⟩ := mem_iUnion.1 hearlier
      obtain ⟨hj, hxj⟩ := mem_iUnion.1 hj
      have hmin := Nat.find_min' hex (show ∃ k, Encodable.encode k = Encodable.encode j ∧
        x ∈ B k from ⟨j, rfl, hxj⟩)
      omega

/--
Measurability of the pieces for measurable cores and envelopes and an encodable index. Source: Hart
Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
theorem measurableSet_cell [MeasurableSpace X] [Encodable I]
    {C B : I → Set X} (hC : ∀ i, MeasurableSet (C i))
    (hB : ∀ i, MeasurableSet (B i)) (i : I) : MeasurableSet (cell C B i) := by
  exact (hC i).union (((hB i).diff (MeasurableSet.iUnion hC)).diff
    (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hB j))

/--
Two disjoint sets exhibit the loss of a core under naive disjointification. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem plain_disjointification_loses_core :
    ∃ C B : Fin 2 → Set ℝ,
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧ (∀ i, C i ⊆ B i) ∧
      ¬ C 1 ⊆ B 1 \ B 0 := by
  let C : Fin 2 → Set ℝ := fun i => if i = 0 then {0} else {1}
  let B : Fin 2 → Set ℝ := fun _ => {0, 1}
  refine ⟨C, B, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [C]
  · intro i
    fin_cases i <;> simp [C, B]
  · simp [C, B]

end GeometricMeasure.CalderonZygmund

end
