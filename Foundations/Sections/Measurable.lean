import Foundations.Sections.Basic
import Mathlib.Order.Filter.IndicatorFunction

noncomputable section
open MeasureTheory Filter Set MeasurableSpace
open scoped Topology ENNReal BigOperators
namespace Foundations
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (μ : Measure α) [IsFiniteMeasure μ]

/-- Every measurable indicator has square-integrable sections under a finite measure. -/
theorem memLp_indicator_section {s : Set (α × β)} (hs : MeasurableSet s) (c : ℝ) (y : β) :
    MemLp (fun x => s.indicator (fun _ => c) (x,y)) 2 μ := by
  classical
  have h := (memLp_const c : MemLp (fun _ : α => c) 2 μ).indicator
    (hs.preimage (measurable_id.prodMk (measurable_const (a := y))))
  convert h using 1
  ext x
  simp [Set.indicator]

omit [IsFiniteMeasure μ] [MeasurableSpace β] in
@[simp] theorem sectionLp_zero : sectionLp μ (fun _ : α × β => 0) = fun _ => 0 := by
  funext y
  rw [sectionLp_of_memLp μ (MemLp.zero : MemLp (0 : α → ℝ) 2 μ)]
  rfl

theorem sectionLp_indicator_union {s t : Set (α × β)}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t) (c : ℝ) :
    sectionLp μ ((s ∪ t).indicator (fun _ => c)) =
      sectionLp μ (s.indicator (fun _ => c)) + sectionLp μ (t.indicator (fun _ => c)) := by
  rw [Set.indicator_union_of_disjoint hd]
  funext y
  exact sectionLp_add_of_memLp μ (memLp_indicator_section μ hs c y)
    (memLp_indicator_section μ ht c y)

theorem sectionLp_indicator_compl {s : Set (α × β)} (hs : MeasurableSet s) (c : ℝ) :
    sectionLp μ (sᶜ.indicator (fun _ => c)) =
      (fun _ => (memLp_const c : MemLp (fun _ : α => c) 2 μ).toLp _) -
        sectionLp μ (s.indicator (fun _ => c)) := by
  rw [Set.indicator_compl]
  funext y
  simp only [Pi.sub_apply]
  rw [sectionLp_of_memLp μ ((memLp_const c).sub (memLp_indicator_section μ hs c y)),
    sectionLp_of_memLp μ (memLp_indicator_section μ hs c y)]
  rfl

/-- Rectangles give simple L²-valued functions. -/
theorem stronglyMeasurable_sectionLp_indicator_prod {s : Set α} {t : Set β}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (c : ℝ) :
    StronglyMeasurable (sectionLp μ ((s ×ˢ t).indicator (fun _ => c))) := by
  classical
  have he : sectionLp μ ((s ×ˢ t).indicator (fun _ => c)) =
      t.indicator (fun _ => indicatorConstLp 2 hs (measure_ne_top μ s) c) := by
    funext y
    by_cases hy : y ∈ t
    · rw [Set.indicator_of_mem hy, sectionLp_of_memLp μ (memLp_indicator_section μ (hs.prod ht) c y)]
      apply Lp.ext
      filter_upwards [(memLp_indicator_section μ (hs.prod ht) c y).coeFn_toLp,
        indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s) (c := c)] with x hx hx'
      rw [hx, hx']
      simp [Set.indicator, hy]
    · rw [Set.indicator_of_notMem hy]
      have hz : (fun x => (s ×ˢ t).indicator (fun _ => c) (x,y)) = (0 : α → ℝ) := by
        ext x; simp [Set.indicator, hy]
      unfold sectionLp
      simp only [hz, dif_pos MemLp.zero, MemLp.toLp_zero]
  rw [he]
  exact stronglyMeasurable_const.indicator ht

/-- Monotone-class step: sections of all measurable indicators are strongly measurable. -/
theorem stronglyMeasurable_sectionLp_indicator {s : Set (α × β)}
    (hs : MeasurableSet s) (c : ℝ) :
    StronglyMeasurable (sectionLp μ (s.indicator (fun _ => c))) := by
  classical
  induction s, hs using induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simpa using (stronglyMeasurable_const : StronglyMeasurable (fun _ : β => (0 : Lp ℝ 2 μ)))
  | basic s hs =>
      obtain ⟨s, hs, t, ht, rfl⟩ := hs
      exact stronglyMeasurable_sectionLp_indicator_prod μ hs ht c
  | compl s hs ih =>
      rw [sectionLp_indicator_compl μ hs c]
      exact stronglyMeasurable_const.sub ih
  | iUnion s hd hs ih =>
      let A : ℕ → Set (α × β) := fun n => ⋃ i ∈ Finset.range n, s i
      have hA n : MeasurableSet (A n) := by
        exact Finset.measurableSet_biUnion _ (fun i _ => hs i)
      have hfin (a : Finset ℕ) :
          StronglyMeasurable (sectionLp μ ((⋃ i ∈ a, s i).indicator (fun _ => c))) := by
        induction a using Finset.induction_on with
        | empty => simpa using (stronglyMeasurable_const : StronglyMeasurable (fun _ : β => (0 : Lp ℝ 2 μ)))
        | @insert i a hi ha =>
            rw [Finset.set_biUnion_insert, sectionLp_indicator_union μ (hs i)
              (Finset.measurableSet_biUnion _ (fun k _ => hs k))
              (disjoint_iUnion_right.2 (fun k => disjoint_iUnion_right.2 (fun hk => hd (by aesop)))) c]
            exact (ih i).add ha
      apply stronglyMeasurable_of_tendsto atTop (fun n => hfin (Finset.range n))
      apply tendsto_pi_nhds.2
      intro y
      have hmem n := memLp_indicator_section μ (hA n) c y
      have hmem' := memLp_indicator_section μ (MeasurableSet.iUnion hs) c y
      change Tendsto (fun n => sectionLp μ ((A n).indicator (fun _ => c)) y) atTop
        (𝓝 (sectionLp μ ((⋃ i, s i).indicator (fun _ => c)) y))
      simp_rw [sectionLp_of_memLp μ (hmem _), sectionLp_of_memLp μ hmem']
      apply tendsto_toLp_dominated μ hmem hmem' (memLp_const ‖c‖)
      · intro n
        exact Eventually.of_forall (fun x => norm_indicator_le_norm_self (fun _ => c) (x,y))
      · apply Eventually.of_forall
        intro x
        have hm : Monotone A := fun n m h => biUnion_subset_biUnion_left (Finset.range_mono h)
        have hu : (⋃ n, A n) = ⋃ i, s i := by
          ext z
          simp only [A, mem_iUnion, Finset.mem_range]
          constructor
          · rintro ⟨n,i,hi,hz⟩; exact ⟨i,hz⟩
          · rintro ⟨i,hi⟩; exact ⟨i+1,i,by omega,hi⟩
        have he := hm.indicator_eventuallyEq_iUnion A (fun _ => c) (x,y)
        rw [hu] at he
        exact tendsto_const_nhds.congr' he.symm

/-- Simple functions have strongly measurable L² sections. -/
theorem stronglyMeasurable_sectionLp_simpleFunc (f : SimpleFunc (α × β) ℝ) :
    StronglyMeasurable (sectionLp μ f) := by
  classical
  induction f using SimpleFunc.induction with
  | @const c s hs =>
      convert stronglyMeasurable_sectionLp_indicator μ hs c using 1
      rfl
  | @add f g hd hf hg =>
      have he : sectionLp μ (f + g) = sectionLp μ f + sectionLp μ g := by
        funext y
        exact sectionLp_add_of_memLp μ
          ((f.comp (fun x => (x,y)) measurable_prodMk_right).memLp_of_isFiniteMeasure 2 μ)
          ((g.comp (fun x => (x,y)) measurable_prodMk_right).memLp_of_isFiniteMeasure 2 μ)
      rw [he]
      exact hf.add hg

variable {ν : Measure β} [IsFiniteMeasure ν]

/-- Fubini for classes: a square-integrable real function has AE strongly measurable sections. -/
theorem aestronglyMeasurable_sectionLp {F : α × β → ℝ}
    (hF : MemLp F 2 (μ.prod ν)) : AEStronglyMeasurable (sectionLp μ F) ν := by
  classical
  let G := hF.1.mk F
  have hG : StronglyMeasurable G := hF.1.stronglyMeasurable_mk
  have hFG : F =ᵐ[μ.prod ν] G := hF.1.ae_eq_mk
  have hGmem : MemLp G 2 (μ.prod ν) := hF.ae_eq hFG
  let f := fun n => SimpleFunc.approxOn G hG.measurable univ 0 (mem_univ 0) n
  have hm : ∀ n, AEStronglyMeasurable (sectionLp μ (f n)) ν :=
    fun n => (stronglyMeasurable_sectionLp_simpleFunc μ (f n)).aestronglyMeasurable
  have hlim : ∀ᵐ y ∂ν, Tendsto (fun n => sectionLp μ (f n) y) atTop (𝓝 (sectionLp μ G y)) := by
    filter_upwards [memLp_section_ae μ hGmem] with y hy
    have hfn n : MemLp (fun x => f n (x,y)) 2 μ :=
      ((f n).comp (fun x => (x,y)) measurable_prodMk_right).memLp_of_isFiniteMeasure 2 μ
    simp_rw [sectionLp_of_memLp μ (hfn _), sectionLp_of_memLp μ hy]
    apply tendsto_toLp_dominated μ hfn hy (hy.norm.add hy.norm)
    · intro n
      exact Eventually.of_forall (fun x => SimpleFunc.norm_approxOn_zero_le hG.measurable (mem_univ 0) (x,y) n)
    · exact Eventually.of_forall (fun x => SimpleFunc.tendsto_approxOn hG.measurable (mem_univ 0) (by simp))
  exact (aestronglyMeasurable_of_tendsto_ae atTop hm hlim).congr
    (sectionLp_congr_ae μ hFG).symm

end Foundations
