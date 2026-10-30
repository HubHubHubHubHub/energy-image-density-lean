import GeometricMeasure.Analysis.CalderonZygmundGeometry
import GeometricMeasure.Analysis.CalderonZygmundPartition
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Quantitative Calderón–Zygmund decomposition

## Main results
The good and bad parts satisfy L¹, L² and L∞ bounds, cancellation, support and series
identities, with explicit constants 5^d, 2 and 10^d.

Bibliographic context: Hart Smith, Lecture 8, pp. 2–4; De Philippis–Rindler, pp. 1027–1028. These
page locators are unverified against those editions. The proofs below establish the claims under
their displayed hypotheses.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace GeometricMeasure.CalderonZygmund
variable {d : ℕ} {I : Type*} [Countable I]

/--
Real-valued average on a piece; quantitative uses later prove positivity of its volume. Source: Hart
Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
def average (f : Space d → ℝ) (A : Set (Space d)) : ℝ :=
  (∫ x in A, f x) / volume.real A

/--
Good part equal to the average on the selected piece, and to f outside the union. Source: Hart
Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
def good (f : Space d → ℝ) (A : I → Set (Space d)) (x : Space d) : ℝ := by
  classical
  exact if h : ∃ i, x ∈ A i then average f (A h.choose) else f x

/--
Bad part: the indicator of a piece multiplied by f minus its average. Source: Hart Smith, Lecture 8,
pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
def bad (f : Space d → ℝ) (A : I → Set (Space d)) (i : I) : Space d → ℝ :=
  (A i).indicator (fun x => f x - average f (A i))

omit [Countable I] in
/--
On a piece of a disjoint family, the good part is exactly its average. Source: Hart Smith, Lecture
8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem good_on {f : Space d → ℝ} {A : I → Set (Space d)}
    (hdj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (i : I) {x : Space d} (hx : x ∈ A i) : good f A x = average f (A i) := by
  classical
  have h : ∃ j, x ∈ A j := ⟨i, hx⟩
  have heq : h.choose = i := by
    by_contra hn
    exact Set.disjoint_left.1 (hdj hn) h.choose_spec hx
  simp only [good, dif_pos h, heq]

omit [Countable I] in
/--
The good part equals f pointwise outside the union of the pieces. Source: Hart Smith, Lecture 8, pp.
2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem good_off {f : Space d → ℝ} {A : I → Set (Space d)}
    {x : Space d} (hx : x ∉ ⋃ i, A i) : good f A x = f x := by
  classical
  have h : ¬ ∃ i, x ∈ A i := by simpa only [mem_iUnion] using hx
  simp only [good, dif_neg h]

/--
Volume times the norm of the average equals the norm of the integral, for positive real volume.
Source: Hart Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the
cited editions.)
-/
theorem norm_average_mass {f : Space d → ℝ} {A : Set (Space d)}
    (hpos : 0 < volume.real A) :
    volume.real A * ‖average f A‖ = ‖∫ x in A, f x‖ := by
  rw [average, norm_div, Real.norm_of_nonneg hpos.le]
  field_simp

/--
A bound on the integral of the norm bounds the average on a piece of positive real volume. Source:
Hart Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
theorem average_bound {f : Space d → ℝ} {A : Set (Space d)}
    (hpos : 0 < volume.real A) {K : ℝ}
    (hK : (∫ x in A, ‖f x‖) ≤ K * volume.real A) : ‖average f A‖ ≤ K := by
  rw [average, norm_div, Real.norm_of_nonneg hpos.le]
  exact (div_le_iff₀ hpos).2 ((norm_integral_le_integral_norm _).trans hK)

omit [Countable I] in
/--
Integrability of the good part on each disjoint measurable piece of finite measure. Source: Hart
Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
theorem good_integrableOn {f : Space d → ℝ} {A : I → Set (Space d)}
    (hA : ∀ i, MeasurableSet (A i))
    (hdj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hfin : ∀ i, volume (A i) ≠ ∞) (i : I) : IntegrableOn (good f A) (A i) := by
  exact IntegrableOn.congr_fun (μ := volume)
    (integrableOn_const (C := average f (A i)) (hfin i))
    (fun x hx => (good_on hdj i hx).symm) (hA i)

omit [Countable I] in
/--
Averaging does not increase mass on each disjoint measurable piece of positive real volume. Source:
Hart Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
theorem good_cell_integral_norm {f : Space d → ℝ} {A : I → Set (Space d)}
    (hA : ∀ i, MeasurableSet (A i))
    (hdj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hpos : ∀ i, 0 < volume.real (A i)) (i : I) :
    (∫ x in A i, ‖good f A x‖) ≤ ∫ x in A i, ‖f x‖ := by
  rw [setIntegral_congr_fun (hA i) (fun x hx => congrArg norm (good_on hdj i hx)),
    setIntegral_const, smul_eq_mul, norm_average_mass (hpos i)]
  exact norm_integral_le_integral_norm _

/--
For integrable f and a countable disjoint measurable family of pieces of finite positive measure,
the good part is globally integrable. Source: Hart Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028
(Page references unverified against the cited editions.)
-/
theorem good_integrable {f : Space d → ℝ} (hf : Integrable f)
    {A : I → Set (Space d)} (hA : ∀ i, MeasurableSet (A i))
    (hdj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hfin : ∀ i, volume (A i) ≠ ∞) (hpos : ∀ i, 0 < volume.real (A i)) :
    Integrable (good f A) := by
  have hsum := (disjoint_integrals_summable hf hA hdj).1
  have hs : Summable (fun i => ∫ x in A i, ‖good f A x‖) :=
    hsum.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (good_cell_integral_norm hA hdj hpos)
  have hu := integrableOn_iUnion_of_summable_integral_norm (good_integrableOn hA hdj hfin) hs
  have hc : IntegrableOn (good f A) (⋃ i, A i)ᶜ :=
    IntegrableOn.congr_fun hf.restrict (fun x hx => (good_off hx).symm) (MeasurableSet.iUnion hA).compl
  simpa only [union_compl_self, integrableOn_univ] using hu.union hc

/--
The global mass of the good part does not exceed that of f. Source: Hart Smith, Lecture 8, pp. 2–4;
DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem good_mass_le {f : Space d → ℝ} (hf : Integrable f)
    {A : I → Set (Space d)} (hA : ∀ i, MeasurableSet (A i))
    (hdj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hfin : ∀ i, volume (A i) ≠ ∞) (hpos : ∀ i, 0 < volume.real (A i)) :
    mass (good f A) ≤ mass f := by
  have hg := good_integrable hf hA hdj hfin hpos
  have hU := MeasurableSet.iUnion hA
  unfold mass
  rw [← integral_add_compl hU hg.norm, ← integral_add_compl hU hf.norm]
  apply add_le_add
  · rw [integral_iUnion hA hdj hg.norm.restrict, integral_iUnion hA hdj hf.norm.restrict]
    exact (hasSum_integral_iUnion hA hdj hg.norm.restrict).summable.tsum_le_tsum
      (good_cell_integral_norm hA hdj hpos)
      (hasSum_integral_iUnion hA hdj hf.norm.restrict).summable
  · exact le_of_eq (setIntegral_congr_fun hU.compl (fun x hx => congrArg norm (good_off hx)))

omit [Countable I] in
/--
Each bad part is integrable on a measurable piece of finite measure. Source: Hart Smith, Lecture 8,
pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem bad_integrable {f : Space d → ℝ} (hf : Integrable f)
    {A : I → Set (Space d)} (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, volume (A i) ≠ ∞) (i : I) : Integrable (bad f A i) :=
  IntegrableOn.integrable_indicator
    (hf.restrict.sub (integrableOn_const (C := average f (A i)) (hfin i))) (hA i)

omit [Countable I] in
/--
The integral of each bad part is exactly zero, assuming strictly positive real volume. Source: Hart
Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
theorem bad_integral_zero {f : Space d → ℝ} (hf : Integrable f)
    {A : I → Set (Space d)} (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, volume (A i) ≠ ∞) (hpos : ∀ i, 0 < volume.real (A i)) (i : I) :
    (∫ x, bad f A i x) = 0 := by
  rw [bad, integral_indicator (hA i), integral_sub hf.restrict (integrableOn_const (hfin i)),
    setIntegral_const, smul_eq_mul, average]
  field_simp [(hpos i).ne']
  ring

omit [Countable I] in
/--
The ordinary support of each bad part is contained in its piece. Source: Hart Smith, Lecture 8, pp.
2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem bad_support {f : Space d → ℝ} (A : I → Set (Space d)) (i : I) :
    Function.support (bad f A i) ⊆ A i := by
  intro x hx
  by_contra hn
  exact hx (Set.indicator_of_notMem hn _)

omit [Countable I] in
/--
The mass of each bad part is bounded by twice the mass of f on its piece. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem bad_mass_le {f : Space d → ℝ} (hf : Integrable f)
    {A : I → Set (Space d)} (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, volume (A i) ≠ ∞) (hpos : ∀ i, 0 < volume.real (A i)) (i : I) :
    mass (bad f A i) ≤ 2 * ∫ x in A i, ‖f x‖ := by
  have heq : (fun x => ‖bad f A i x‖) = (A i).indicator (fun x => ‖f x - average f (A i)‖) := by
    ext x
    by_cases hx : x ∈ A i <;> simp [bad, hx]
  unfold mass
  rw [heq, integral_indicator (hA i)]
  calc
    _ ≤ ∫ x in A i, (‖f x‖ + ‖average f (A i)‖) :=
      integral_mono (hf.restrict.sub (integrableOn_const (hfin i))).norm
        (hf.norm.restrict.add (integrableOn_const (hfin i))) (fun x => norm_sub_le _ _)
    _ = (∫ x in A i, ‖f x‖) + ‖∫ x in A i, f x‖ := by
      rw [integral_add hf.norm.restrict (integrableOn_const (hfin i)), setIntegral_const,
        smul_eq_mul, norm_average_mass (hpos i)]
    _ ≤ 2 * ∫ x in A i, ‖f x‖ := by linarith [norm_integral_le_integral_norm (fun x => f x) (μ := volume.restrict (A i))]

/--
Summability of the bad masses and global bound by 2 * mass f. Source: Hart Smith, Lecture 8, pp.
2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem bad_sum_mass_le {f : Space d → ℝ} (hf : Integrable f)
    {A : I → Set (Space d)} (hA : ∀ i, MeasurableSet (A i))
    (hdj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hfin : ∀ i, volume (A i) ≠ ∞) (hpos : ∀ i, 0 < volume.real (A i)) :
    Summable (fun i => mass (bad f A i)) ∧ (∑' i, mass (bad f A i)) ≤ 2 * mass f := by
  obtain ⟨hs, hbound⟩ := disjoint_integrals_summable hf hA hdj
  have hb := (hs.mul_left 2).of_nonneg_of_le (fun i => mass_nonneg _)
    (bad_mass_le hf hA hfin hpos)
  refine ⟨hb, ?_⟩
  calc
    _ ≤ ∑' i, 2 * ∫ x in A i, ‖f x‖ := hb.tsum_le_tsum (bad_mass_le hf hA hfin hpos) (hs.mul_left 2)
    _ = 2 * ∑' i, ∫ x in A i, ‖f x‖ := tsum_mul_left
    _ ≤ 2 * mass f := by linarith

omit [Countable I] in
/--
Pointwise identity f = good + sum of the bad parts on disjoint pieces. Source: Hart Smith, Lecture
8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem decomposition_pointwise {f : Space d → ℝ} {A : I → Set (Space d)}
    (hdj : Pairwise (fun i j => Disjoint (A i) (A j))) (x : Space d) :
    f x = good f A x + ∑' i, bad f A i x := by
  classical
  by_cases hx : ∃ i, x ∈ A i
  · obtain ⟨i, hi⟩ := hx
    have ho : ∀ j ≠ i, bad f A j x = 0 := by
      intro j hj
      have hn : x ∉ A j := fun h => Set.disjoint_left.1 (hdj hj) h hi
      exact Set.indicator_of_notMem hn _
    rw [tsum_eq_single i ho, good_on hdj i hi, bad, Set.indicator_of_mem hi]
    ring
  · have hn : x ∉ ⋃ i, A i := by simpa only [mem_iUnion] using hx
    have hz : ∀ i, bad f A i x = 0 := fun i => Set.indicator_of_notMem (fun h => hx ⟨i, h⟩) _
    simp only [good_off hn, hz, tsum_zero, add_zero]

omit [Countable I] in
/--
Almost-everywhere bound on good from the averages and the exterior bound. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem good_bound {f : Space d → ℝ} {A : I → Set (Space d)}
    (hdj : Pairwise (fun i j => Disjoint (A i) (A j))) {K : ℝ}
    (havg : ∀ i, ‖average f (A i)‖ ≤ K)
    (hout : ∀ᵐ x, x ∉ ⋃ i, A i → ‖f x‖ ≤ K) :
    ∀ᵐ x, ‖good f A x‖ ≤ K := by
  filter_upwards [hout] with x hx
  by_cases h : ∃ i, x ∈ A i
  · obtain ⟨i, hi⟩ := h
    rw [good_on hdj i hi]
    exact havg i
  · have hn : x ∉ ⋃ i, A i := by simpa only [mem_iUnion] using h
    rw [good_off hn]
    exact hx hn

/--
An integrable real function bounded almost everywhere has an integrable square. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem integrable_sq_of_bound {g : Space d → ℝ} (hg : Integrable g)
    {K : ℝ} (hK : ∀ᵐ x, ‖g x‖ ≤ K) : Integrable (fun x => g x ^ 2) := by
  apply (hg.norm.const_mul K).mono' (hg.aestronglyMeasurable.pow 2)
  filter_upwards [hK] with x hx
  change ‖g x ^ 2‖ ≤ K * ‖g x‖
  rw [norm_pow, sq]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/--
The integral of the square is bounded by the almost-everywhere bound times the mass. Source: Hart
Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
theorem integral_sq_le {g : Space d → ℝ} (hg : Integrable g)
    {K : ℝ} (hK : ∀ᵐ x, ‖g x‖ ≤ K) :
    (∫ x, g x ^ 2) ≤ K * mass g := by
  rw [mass, ← integral_const_mul]
  apply integral_mono_ae (integrable_sq_of_bound hg hK) (hg.norm.const_mul K)
  filter_upwards [hK] with x hx
  calc
    g x ^ 2 = ‖g x‖ * ‖g x‖ := by rw [← sq, Real.norm_eq_abs, sq_abs]
    _ ≤ K * ‖g x‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)

end GeometricMeasure.CalderonZygmund

end

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace GeometricMeasure.CalderonZygmund
variable {d : ℕ} {I : Type*} [Countable I]

/--
The norm of the L¹ representative equals the real integral of the norm. Source: Hart Smith, Lecture
8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem norm_toL1_eq_mass {f : Space d → ℝ} (hf : Integrable f) :
    ‖hf.toL1 f‖ = mass f := by
  rw [Integrable.norm_toL1_eq_lintegral_enorm, mass,
    integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]

/--
The series of bad parts converges in L¹ to the prescribed representative f - good. Source: Hart
Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
theorem decomposition_hasSum_L1 {f : Space d → ℝ} (hf : Integrable f)
    {A : I → Set (Space d)} (hA : ∀ i, MeasurableSet (A i))
    (hdj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hfin : ∀ i, volume (A i) ≠ ∞) (hpos : ∀ i, 0 < volume.real (A i)) :
    HasSum (fun i => (bad_integrable hf hA hfin i).toL1 (bad f A i))
      ((hf.sub (good_integrable hf hA hdj hfin hpos)).toL1 (f - good f A)) := by
  let bL : I → Space d →₁[volume] ℝ := fun i => (bad_integrable hf hA hfin i).toL1 (bad f A i)
  have hs : Summable (fun i => ‖bL i‖) := by
    simpa only [bL, norm_toL1_eq_mass] using (bad_sum_mass_le hf hA hdj hfin hpos).1
  have he : (∑' i, ‖bL i‖ₑ) ≠ ∞ := by
    simpa only [ofReal_norm] using hs.tsum_ofReal_ne_top
  have heq : (∑' i, bL i) =
      (hf.sub (good_integrable hf hA hdj hfin hpos)).toL1 (f - good f A) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_tsum he,
      ae_all_iff.2 (fun i => (bad_integrable hf hA hfin i).coeFn_toL1),
      (hf.sub (good_integrable hf hA hdj hfin hpos)).coeFn_toL1] with x hx hb hfg
    rw [hx, hfg]
    have hb' : ∀ i, bL i x = bad f A i x := hb
    simp only [hb', Pi.sub_apply]
    linarith [decomposition_pointwise (f := f) hdj x]
  exact heq ▸ hs.of_norm.hasSum

end GeometricMeasure.CalderonZygmund

end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Metric Set
open scoped ENNReal NNReal Topology
namespace GeometricMeasure.CalderonZygmund
variable {d : ℕ} {f : Space d → ℝ} {lam : ℝ}

namespace BallFamily
variable (F : BallFamily d f lam)
/--
Injective natural-number encoding of the countable index of the ball family. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
noncomputable instance encodableIndex : Encodable F.Index := Encodable.ofCountable _

/--
Partition (35) of the union of the 5-fold dilates, preserving each small ball. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
def pieces : F.Index → Set (Space d) := cell F.core (F.expanded 5)

/--
The small ball is contained in its 5-fold dilate. Source: Hart Smith, Lecture 8, pp. 2–4; DPR, pp.
1027–1028 (Page references unverified against the cited editions.)
-/
theorem core_subset_expanded (i : F.Index) : F.core i ⊆ F.expanded 5 i :=
  ball_subset_ball (by linarith [F.radius_pos i])

/--
The small ball is contained in its piece. Source: Hart Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028
(Page references unverified against the cited editions.)
-/
theorem core_subset_pieces (i : F.Index) : F.core i ⊆ F.pieces i :=
  subset_cell _ _ i

/--
Each piece is contained in the open 5-fold dilate. Source: Hart Smith, Lecture 8, pp. 2–4; DPR, pp.
1027–1028 (Page references unverified against the cited editions.)
-/
theorem pieces_subset_expanded (i : F.Index) : F.pieces i ⊆ F.expanded 5 i :=
  cell_subset F.core_subset_expanded i

/--
Each piece of the ball family is measurable. Source: Hart Smith, Lecture 8, pp. 2–4; DPR, pp.
1027–1028 (Page references unverified against the cited editions.)
-/
theorem pieces_measurable (i : F.Index) : MeasurableSet (F.pieces i) :=
  measurableSet_cell (fun _ => measurableSet_ball) (fun _ => measurableSet_ball) i

/--
The pieces of the ball family are pairwise disjoint. Source: Hart Smith, Lecture 8, pp. 2–4; DPR,
pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem pieces_disjoint : Pairwise (fun i j => Disjoint (F.pieces i) (F.pieces j)) :=
  cell_pairwiseDisjoint F.disjoint

/--
The pieces cover exactly the union of the 5-fold dilates. Source: Hart Smith, Lecture 8, pp. 2–4;
DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem pieces_union : (⋃ i, F.pieces i) = ⋃ i, F.expanded 5 i :=
  iUnion_cell F.core_subset_expanded

/--
Each piece has finite measure. Source: Hart Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page
references unverified against the cited editions.)
-/
theorem pieces_finite (i : F.Index) : volume (F.pieces i) ≠ ∞ :=
  ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (F.pieces_subset_expanded i))

/--
Each piece has strictly positive real volume. Source: Hart Smith, Lecture 8, pp. 2–4; DPR, pp.
1027–1028 (Page references unverified against the cited editions.)
-/
theorem pieces_pos (i : F.Index) : 0 < volume.real (F.pieces i) :=
  (real_ball_pos (F.center i) (F.radius_pos i)).trans_le
    (measureReal_mono (F.core_subset_pieces i) (F.pieces_finite i))

/--
Exact bound 5^d * lam on the averages of the pieces. Source: Hart Smith, Lecture 8, pp. 2–4; DPR,
pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem pieces_average_bound (hf : Integrable f) (hlam : 0 < lam) (i : F.Index) :
    ‖average f (F.pieces i)‖ ≤ (5 : ℝ) ^ d * lam := by
  apply average_bound (F.pieces_pos i)
  have hmon : (∫ x in F.pieces i, ‖f x‖) ≤ ∫ x in F.expanded 5 i, ‖f x‖ :=
    integral_mono_measure (Measure.restrict_mono (F.pieces_subset_expanded i) le_rfl)
      (ae_of_all _ (fun _ => norm_nonneg _)) hf.norm.restrict
  have hvol : volume.real (F.core i) ≤ volume.real (F.pieces i) :=
    measureReal_mono (F.core_subset_pieces i) (F.pieces_finite i)
  calc
    _ ≤ ∫ x in F.expanded 5 i, ‖f x‖ := hmon
    _ ≤ lam * volume.real (F.expanded 5 i) := F.good_dilate i
    _ = ((5 : ℝ) ^ d * lam) * volume.real (F.core i) := by
      rw [show volume.real (F.expanded 5 i) = (5 : ℝ) ^ d * volume.real (F.core i) from
        real_ball_scale _ _ (by norm_num)]
      ring
    _ ≤ ((5 : ℝ) ^ d * lam) * volume.real (F.pieces i) :=
      mul_le_mul_of_nonneg_left hvol (by positivity)

/--
Almost-everywhere bound 5^d * lam on the good part obtained from the selected balls. Source: Hart
Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
theorem good_bound (hf : Integrable f) (hlam : 0 < lam) :
    ∀ᵐ x, ‖CalderonZygmund.good f F.pieces x‖ ≤ (5 : ℝ) ^ d * lam := by
  apply CalderonZygmund.good_bound F.pieces_disjoint (F.pieces_average_bound hf hlam)
  filter_upwards [F.outside] with x hx hn
  have hout : ‖f x‖ ≤ lam := hx (by
    change x ∉ ⋃ i, F.expanded 5 i
    rwa [← F.pieces_union])
  have hp : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
  exact hout.trans (by nlinarith)

end BallFamily

/--
A decomposition with L¹, L², L∞, cancellation, ordinary support, pointwise identity and L¹ series.
Source: Hart Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the
cited editions.)
-/
structure Decomposition (d : ℕ) (f : Space d → ℝ) (lam : ℝ) where
  balls : BallFamily d f lam
  g : Space d → ℝ
  b : balls.Index → Space d → ℝ
  input_integrable : Integrable f
  good_eq : g = CalderonZygmund.good f balls.pieces
  bad_eq : b = CalderonZygmund.bad f balls.pieces
  good_integrable : Integrable g
  good_memLp_two : MemLp g 2
  good_bound : ∀ᵐ x, ‖g x‖ ≤ (5 : ℝ) ^ d * lam
  good_eLpNorm_top : eLpNorm g ∞ volume ≤ ENNReal.ofReal ((5 : ℝ) ^ d * lam)
  good_mass : mass g ≤ mass f
  good_square : (∫ x, g x ^ 2) ≤ (5 : ℝ) ^ d * lam * mass f
  bad_integrable : ∀ i, Integrable (b i)
  bad_summable : Summable (fun i => mass (b i))
  bad_mass : (∑' i, mass (b i)) ≤ 2 * mass f
  bad_zero : ∀ i, (∫ x, b i x) = 0
  bad_support : ∀ i, Function.support (b i) ⊆ balls.expanded 5 i
  pointwise : ∀ x, f x = g x + ∑' i, b i x
  hasSum_L1 : HasSum (fun i => (bad_integrable i).toL1 (b i))
    ((Integrable.sub input_integrable good_integrable).toL1 (f - g))
  enlarged_summable : Summable (fun i => volume.real (balls.expanded 5 i))
  enlarged_sum : (∑' i, volume (balls.expanded 5 i)) ≤
    ENNReal.ofReal ((5 : ℝ) ^ d * mass f / lam)
  exceptional : volume (⋃ i, balls.expanded 10 i) ≤
    ENNReal.ofReal ((10 : ℝ) ^ d * mass f / lam)

/--
Construction of all decomposition fields from a ball family. Source: Hart Smith, Lecture 8, pp. 2–4;
DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
noncomputable def BallFamily.decompose (F : BallFamily d f lam)
    (hf : Integrable f) (hlam : 0 < lam) : Decomposition d f lam := by
  let g := CalderonZygmund.good f F.pieces
  let b := CalderonZygmund.bad f F.pieces
  have hg := CalderonZygmund.good_integrable hf F.pieces_measurable F.pieces_disjoint
    F.pieces_finite F.pieces_pos
  have hbound := F.good_bound hf hlam
  have hmass := CalderonZygmund.good_mass_le hf F.pieces_measurable F.pieces_disjoint
    F.pieces_finite F.pieces_pos
  have hb := CalderonZygmund.bad_sum_mass_le hf F.pieces_measurable F.pieces_disjoint
    F.pieces_finite F.pieces_pos
  refine {
    balls := F
    g := g
    b := b
    input_integrable := hf
    good_eq := rfl
    bad_eq := rfl
    good_integrable := hg
    good_memLp_two := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2
      (integrable_sq_of_bound hg hbound)
    good_bound := hbound
    good_eLpNorm_top := ?_
    good_mass := hmass
    good_square := ?_
    bad_integrable := CalderonZygmund.bad_integrable hf F.pieces_measurable F.pieces_finite
    bad_summable := hb.1
    bad_mass := hb.2
    bad_zero := CalderonZygmund.bad_integral_zero hf F.pieces_measurable F.pieces_finite F.pieces_pos
    bad_support := fun i => (CalderonZygmund.bad_support F.pieces i).trans (F.pieces_subset_expanded i)
    pointwise := decomposition_pointwise F.pieces_disjoint
    hasSum_L1 := decomposition_hasSum_L1 hf F.pieces_measurable F.pieces_disjoint
      F.pieces_finite F.pieces_pos
    enlarged_summable := (F.sum_expanded hf hlam (by norm_num : (0 : ℝ) < 5)).1
    enlarged_sum := ?_
    exceptional := F.measure_expanded_union hf hlam (by norm_num) }
  · exact eLpNormEssSup_le_of_ae_bound hbound
  · exact (integral_sq_le hg hbound).trans
      (mul_le_mul_of_nonneg_left hmass (by positivity))
  · obtain ⟨hs, hsum⟩ := F.sum_expanded hf hlam (by norm_num : (0 : ℝ) < 5)
    exact ennreal_sum_of_real_bound (fun _ => measure_ball_lt_top.ne) hs hsum

/--
existence assuming only d ≥ 1, integrable f and lam > 0. Source: Hart Smith, Lecture 8, pp. 2–4;
DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem exists_decomposition (hd : 1 ≤ d) (hf : Integrable f) (hlam : 0 < lam) :
    Nonempty (Decomposition d f lam) := by
  obtain ⟨F⟩ := exists_ballFamily hd hf hlam
  exact ⟨F.decompose hf hlam⟩

end GeometricMeasure.CalderonZygmund

end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Metric Set
open scoped ENNReal NNReal Topology
namespace GeometricMeasure.CalderonZygmund
variable {d : ℕ} {f : Space d → ℝ} {lam : ℝ}

namespace BallFamily
variable (F : BallFamily d f lam)

/--
Interface (43): outside the 10-fold dilates, distance to the center is at least 10r and strictly
greater than twice the distance of y in 5C to the center. Source: Hart Smith, Lecture 8, pp. 2–4;
DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem far_of_not_mem_exceptional {x y : Space d} (hx : x ∉ ⋃ i, F.expanded 10 i)
    (i : F.Index) (hy : y ∈ F.expanded 5 i) :
    10 * F.radius i ≤ dist x (F.center i) ∧ 2 * dist y (F.center i) < dist x (F.center i) := by
  have h1 : 10 * F.radius i ≤ dist x (F.center i) := by
    by_contra h
    have hm : x ∈ F.expanded 10 i := by
      change x ∈ ball (F.center i) (10 * F.radius i)
      exact mem_ball.2 (lt_of_not_ge h)
    exact hx (mem_iUnion.2 ⟨i, hm⟩)
  have h2 : dist y (F.center i) < 5 * F.radius i := by
    have hy' : y ∈ ball (F.center i) (5 * F.radius i) := hy
    exact mem_ball.1 hy'
  exact ⟨h1, by linarith⟩

end BallFamily

/--
Interface (43) applied to the ordinary support of each bad part, outside the exceptional region.
Source: Hart Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the
cited editions.)
-/
theorem Decomposition.far_of_mem_support (D : Decomposition d f lam) {x y : Space d}
    (hx : x ∉ ⋃ i, D.balls.expanded 10 i) (i : D.balls.Index)
    (hy : y ∈ Function.support (D.b i)) :
    2 * dist y (D.balls.center i) < dist x (D.balls.center i) :=
  (D.balls.far_of_not_mem_exceptional hx i (D.bad_support i hy)).2

end GeometricMeasure.CalderonZygmund

end
