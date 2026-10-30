import ErrorCalculus.Dirichlet.WienerLevels

noncomputable section
open MeasureTheory

namespace ErrorCalculus

/-- Cylindrical bounded C¹ classes at a fixed level. -/
def cylDom (N : ℕ) : Submodule ℝ (Lp ℝ 2 wienerCoord) :=
  (protoDomD (ouDensityD N)).map (cylLp N 2).toLinearMap

theorem cylDom_mono : Monotone cylDom := by
  intro N M h F hF
  obtain ⟨u, hu, rfl⟩ := hF
  exact ⟨liftLp h 2 u, liftLp_mem_protoDomD h ⟨u, hu⟩, cylLp_comp h 2 u⟩

/-- The increasing union, as an actual L² submodule. -/
def wienerDom : Submodule ℝ (Lp ℝ 2 wienerCoord) := ⨆ N, cylDom N

theorem mem_wienerDom_iff (F : Lp ℝ 2 wienerCoord) :
    F ∈ wienerDom ↔ ∃ N, F ∈ cylDom N :=
  Submodule.mem_iSup_of_directed cylDom cylDom_mono.directed_le

/-- Canonical linear inclusion of an domain into the cylindrical domain. -/
def cylProto (N : ℕ) : protoDomD (ouDensityD N) →ₗ[ℝ] wienerDom where
  toFun u := ⟨cylLp N 2 (u : Lp ℝ 2 _), (mem_wienerDom_iff _).mpr ⟨N, u, u.property, rfl⟩⟩
  map_add' u v := Subtype.ext (map_add (cylLp N 2) (u : Lp ℝ 2 _) (v : Lp ℝ 2 _))
  map_smul' c u := Subtype.ext (map_smul (cylLp N 2) c (u : Lp ℝ 2 _))

@[simp] theorem coe_cylProto (N : ℕ) (u : protoDomD (ouDensityD N)) :
    (cylProto N u : Lp ℝ 2 wienerCoord) = cylLp N 2 (u : Lp ℝ 2 _) := rfl

theorem cylProto_injective (N : ℕ) : Function.Injective (cylProto N) := by
  intro u v h
  exact Subtype.ext ((cylLp N 2).injective (congrArg Subtype.val h))

@[simp] theorem cylProto_lift {N M : ℕ} (h : N ≤ M) (u : protoDomD (ouDensityD N)) :
    cylProto M (liftProto h u) = cylProto N u :=
  Subtype.ext (cylLp_comp h 2 _)

theorem exists_cylRep (F : wienerDom) :
    ∃ N, ∃ u : protoDomD (ouDensityD N), cylProto N u = F := by
  obtain ⟨N, u, hu, he⟩ := (mem_wienerDom_iff _).mp F.property
  exact ⟨N, ⟨u, hu⟩, Subtype.ext he⟩

/-- A chosen finite level. No minimality is required. -/
def level (F : wienerDom) : ℕ := Classical.choose (exists_cylRep F)

def cylRep (F : wienerDom) : protoDomD (ouDensityD (level F)) :=
  Classical.choose (Classical.choose_spec (exists_cylRep F))

theorem cylRep_spec (F : wienerDom) : cylProto (level F) (cylRep F) = F :=
  Classical.choose_spec (Classical.choose_spec (exists_cylRep F))

/-- Representative at any higher level. -/
def cylRepAt (F : wienerDom) {M : ℕ} (h : level F ≤ M) : protoDomD (ouDensityD M) :=
  liftProto h (cylRep F)

theorem cylRepAt_spec (F : wienerDom) {M : ℕ} (h : level F ≤ M) :
    cylProto M (cylRepAt F h) = F := by
  rw [cylRepAt, cylProto_lift, cylRep_spec]

/-- Uniqueness is simply injectivity of the L² isometry. -/
theorem cylRep_unique_at (F : wienerDom) {M : ℕ} (h : level F ≤ M)
    (u : protoDomD (ouDensityD M)) (hu : cylProto M u = F) : u = cylRepAt F h :=
  (cylProto_injective M) (hu.trans (cylRepAt_spec F h).symm)

theorem cylRep_common_unique {N M K : ℕ} (u : protoDomD (ouDensityD N))
    (v : protoDomD (ouDensityD M)) (he : cylProto N u = cylProto M v)
    (hN : N ≤ K) (hM : M ≤ K) : liftProto hN u = liftProto hM v := by
  apply cylProto_injective K
  simpa only [cylProto_lift] using he

/-- Every finite family can be represented at one common level (even an empty family). -/
theorem exists_common_level {ι : Type*} [Fintype ι] (F : ι → wienerDom) :
    ∃ N, ∃ u : ι → protoDomD (ouDensityD N), ∀ i, cylProto N (u i) = F i := by
  classical
  let N := Finset.univ.sup (fun i => level (F i))
  have hN (i : ι) : level (F i) ≤ N := Finset.le_sup (f := fun i => level (F i)) (Finset.mem_univ i)
  exact ⟨N, fun i => cylRepAt (F i) (hN i), fun i => cylRepAt_spec (F i) (hN i)⟩

/-- A common level may additionally be required to exceed any prescribed bound. -/
theorem exists_common_level_above {ι : Type*} [Fintype ι] (F : ι → wienerDom) (B : ℕ) :
    ∃ N, B ≤ N ∧ ∃ u : ι → protoDomD (ouDensityD N), ∀ i, cylProto N (u i) = F i := by
  obtain ⟨N, u, hu⟩ := exists_common_level F
  refine ⟨max N B, le_max_right _ _, fun i => liftProto (le_max_left N B) (u i), ?_⟩
  intro i
  rw [cylProto_lift, hu]

theorem exists_common_level_three (F G H : wienerDom) :
    ∃ N, ∃ u v w : protoDomD (ouDensityD N),
      cylProto N u = F ∧ cylProto N v = G ∧ cylProto N w = H := by
  obtain ⟨N, u, hu⟩ := exists_common_level ![F, G, H]
  exact ⟨N, u 0, u 1, u 2, hu 0, hu 1, hu 2⟩

theorem const_mem_wienerDom (c : ℝ) : Lp.const 2 wienerCoord c ∈ wienerDom := by
  rw [← cylLp_const 0 c]
  exact (cylProto 0 ⟨_, const_mem_protoDomD _ c⟩).property

end ErrorCalculus
