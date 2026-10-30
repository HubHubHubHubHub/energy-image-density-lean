import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Geometry for Calderón–Zygmund decomposition

## Main results
Almost maximal ball choices, the Vitali 5r selection, exterior estimates and bounds on sums of
volumes supply the geometric decomposition.

Bibliographic context: Hart Smith, Lecture 8, pp. 2–4; De Philippis–Rindler, pp. 1027–1028. These
page locators are unverified against those editions.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Metric Set
open scoped ENNReal NNReal Topology
namespace GeometricMeasure
namespace CalderonZygmund
/--
Real Euclidean space over Fin d, equipped with its Euclidean norm. Source: Hart Smith, Lecture 8,
pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
/--
Real mass defined as the integral of the norm, with the Bochner convention. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
def mass {d : ℕ} (f : Space d → ℝ) : ℝ := ∫ x, ‖f x‖
/--
Strictly positive radii where the average of the norm exceeds the threshold lam. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
def badRadii {d : ℕ} (f : Space d → ℝ) (lam : ℝ) (x : Space d) : Set ℝ :=
  {r | 0 < r ∧ lam * volume.real (ball x r) < ∫ y in ball x r, ‖f y‖}

/--
The mass is nonnegative, without an integrability assumption. Source: Hart Smith, Lecture 8, pp.
2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem mass_nonneg {d : ℕ} (f : Space d → ℝ) : 0 ≤ mass f :=
  integral_nonneg (fun _ => norm_nonneg _)

/--
The real volume of a ball with strictly positive radius is strictly positive. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem real_ball_pos {d : ℕ} (x : Space d) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (ball x r) := by
  exact ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne

/--
Exact scaling of real volume by the factor a^d for a > 0. Source: Hart Smith, Lecture 8, pp. 2–4;
DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem real_ball_scale {d : ℕ} (x : Space d) (r : ℝ) {a : ℝ} (ha : 0 < a) :
    volume.real (ball x (a * r)) = a ^ d * volume.real (ball x r) := by
  simp only [Measure.real, addHaar_ball_mul_of_pos volume x ha r,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ha.le _),
    finrank_euclideanSpace_fin, addHaar_ball_center volume x r]

/--
Real volume of a ball with positive radius in terms of the unit ball. Source: Hart Smith, Lecture 8,
pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem real_ball_formula {d : ℕ} (x : Space d) {r : ℝ} (hr : 0 < r) :
    volume.real (ball x r) = r ^ d * volume.real (ball (0 : Space d) 1) := by
  simp only [Measure.real, addHaar_ball_of_pos volume x hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _),
    finrank_euclideanSpace_fin]

/--
Uniform bound on the bad radii for d ≥ 1, integrable f and lam > 0. Source: Hart Smith, Lecture 8,
pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem bad_radius_bound {d : ℕ} (hd : 1 ≤ d) {f : Space d → ℝ}
    (hf : Integrable f) {lam : ℝ} (hlam : 0 < lam) (x : Space d)
    {r : ℝ} (hr : r ∈ badRadii f lam x) :
    r ≤ 1 + mass f / (lam * volume.real (ball (0 : Space d) 1)) := by
  have hw := real_ball_pos (0 : Space d) (r := 1) zero_lt_one
  have hL := mass_nonneg f
  have hden : 0 < lam * volume.real (ball (0 : Space d) 1) := mul_pos hlam hw
  have htop : (∫ y in ball x r, ‖f y‖) ≤ mass f := by
    exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun _ => norm_nonneg _)) hf.norm
  have hbad := hr.2.trans_le htop
  rw [real_ball_formula x hr.1] at hbad
  have hp : r ^ d < mass f / (lam * volume.real (ball (0 : Space d) 1)) := by
    apply (lt_div_iff₀ hden).2
    nlinarith [hbad]
  by_cases h : r ≤ 1
  · exact h.trans (le_add_of_nonneg_right (div_nonneg hL hden.le))
  · have hr1 : 1 ≤ r := (lt_of_not_ge h).le
    have : r ≤ r ^ d := by
      simpa using (pow_le_pow_right₀ hr1 hd)
    linarith

/--
Bad radius chosen beyond half the supremum, whose 5-fold dilate is good. Source: Hart Smith, Lecture
8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem exists_near_maximal_radius {d : ℕ} (hd : 1 ≤ d) {f : Space d → ℝ}
    (hf : Integrable f) {lam : ℝ} (hlam : 0 < lam) (x : Space d)
    (hx : (badRadii f lam x).Nonempty) :
    ∃ r ∈ badRadii f lam x, sSup (badRadii f lam x) / 2 < r ∧
      (∫ y in ball x (5 * r), ‖f y‖) ≤ lam * volume.real (ball x (5 * r)) := by
  have hb : BddAbove (badRadii f lam x) :=
    ⟨_, fun r hr => bad_radius_bound hd hf hlam x hr⟩
  obtain ⟨t, ht⟩ := hx
  have hs : 0 < sSup (badRadii f lam x) := ht.1.trans_le (le_csSup hb ht)
  obtain ⟨r, hr, hsr⟩ := exists_lt_of_lt_csSup ⟨t, ht⟩ (show sSup (badRadii f lam x) / 2 <
    sSup (badRadii f lam x) by linarith)
  refine ⟨r, hr, hsr, ?_⟩
  by_contra h
  have hm : 5 * r ∈ badRadii f lam x := ⟨by linarith [hr.1], lt_of_not_ge h⟩
  have := le_csSup hb hm
  linarith

/--
Almost-everywhere equality of open and closed balls, only for positive radius. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem ball_ae_closedBall {d : ℕ} (x : Space d) {r : ℝ} (hr : 0 < r) :
    ball x r =ᵐ[volume] closedBall x r := by
  apply ae_eq_of_subset_of_measure_ge ball_subset_closedBall
  · rw [addHaar_closedBall volume x hr.le, addHaar_ball_of_pos volume x hr]
  · exact measurableSet_ball.nullMeasurableSet
  · exact measure_closedBall_lt_top.ne

/--
Differentiation gives the almost-everywhere bound at centers with no bad radius. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem ae_norm_le_of_no_bad_radius {d : ℕ} {f : Space d → ℝ}
    (hf : Integrable f) (lam : ℝ) :
    ∀ᵐ x, (badRadii f lam x = ∅) → ‖f x‖ ≤ lam := by
  filter_upwards [(Besicovitch.vitaliFamily volume).ae_tendsto_average
    hf.norm.locallyIntegrable] with x hx hnone
  have ht := hx.comp (Besicovitch.tendsto_filterAt volume x)
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hnot : ¬ r ∈ badRadii f lam x := by simp [hnone]
  have hle : (∫ y in ball x r, ‖f y‖) ≤ lam * volume.real (ball x r) := by
    by_contra h
    exact hnot ⟨hr, lt_of_not_ge h⟩
  have heq := ball_ae_closedBall x hr
  simp only [Function.comp_def, setAverage_eq, smul_eq_mul]
  rw [show volume.real (closedBall x r) = volume.real (ball x r) from
    (congrArg ENNReal.toReal (measure_congr heq)).symm, ← setIntegral_congr_set heq]
  change (volume.real (ball x r))⁻¹ * (∫ y in ball x r, ‖f y‖) ≤ lam
  rw [← div_eq_inv_mul]
  exact (div_le_iff₀ (real_ball_pos x hr)).2 hle

/--
Countable disjoint Vitali 5r selection; almost-everywhere exterior bound. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem select_balls {d : ℕ} (hd : 1 ≤ d) {f : Space d → ℝ}
    (hf : Integrable f) {lam : ℝ} (hlam : 0 < lam) :
    ∃ (s : Set (Space d)) (r : Space d → ℝ), s.Countable ∧
      (s.PairwiseDisjoint (fun x => ball x (r x))) ∧
      (∀ x ∈ s, 0 < r x ∧
        lam * volume.real (ball x (r x)) < ∫ y in ball x (r x), ‖f y‖) ∧
      (∀ x ∈ s, (∫ y in ball x (5 * r x), ‖f y‖) ≤
        lam * volume.real (ball x (5 * r x))) ∧
      (∀ᵐ x, x ∉ ⋃ c ∈ s, ball c (5 * r c) → ‖f x‖ ≤ lam) := by
  classical
  let E := {x : Space d | (badRadii f lam x).Nonempty}
  have hchoose : ∀ x ∈ E, ∃ r ∈ badRadii f lam x,
      sSup (badRadii f lam x) / 2 < r ∧
      (∫ y in ball x (5 * r), ‖f y‖) ≤ lam * volume.real (ball x (5 * r)) :=
    fun x hx => exists_near_maximal_radius hd hf hlam x hx
  let r : Space d → ℝ := fun x => if hx : x ∈ E then (hchoose x hx).choose else 0
  have hr (x : Space d) (hx : x ∈ E) : r x ∈ badRadii f lam x ∧
      sSup (badRadii f lam x) / 2 < r x ∧
      (∫ y in ball x (5 * r x), ‖f y‖) ≤ lam * volume.real (ball x (5 * r x)) := by
    simpa only [r, dif_pos hx] using (hchoose x hx).choose_spec
  obtain ⟨s, hsE, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball E id r
      (1 + mass f / (lam * volume.real (ball (0 : Space d) 1)))
      (fun x hx => bad_radius_bound hd hf hlam x (hr x hx).1) 5 (by norm_num)
  have hcount : s.Countable := hdisj.countable_of_nonempty_interior (fun x hx => by
    rw [isOpen_ball.interior_eq]
    exact ⟨x, mem_ball_self (hr x (hsE hx)).1.1⟩)
  refine ⟨s, r, hcount, hdisj, fun x hx => (hr x (hsE hx)).1,
    fun x hx => (hr x (hsE hx)).2.2, ?_⟩
  filter_upwards [ae_norm_le_of_no_bad_radius hf lam] with x hx hout
  apply hx
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hbad
  obtain ⟨c, hc, hsub⟩ := hcover x hbad
  apply hout
  exact mem_iUnion.2 ⟨c, mem_iUnion.2 ⟨hc, hsub (mem_ball_self (hr x hbad).1.1)⟩⟩

end CalderonZygmund
end GeometricMeasure

end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Metric Set
open scoped ENNReal NNReal Topology
namespace GeometricMeasure.CalderonZygmund

variable {d : ℕ} {I : Type*} [Countable I]

/--
The integrals of the norm over a countable disjoint measurable family are summable and bounded by
the mass. Source: Hart Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified
against the cited editions.)
-/
theorem disjoint_integrals_summable {f : Space d → ℝ} (hf : Integrable f)
    {A : I → Set (Space d)} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    Summable (fun i => ∫ x in A i, ‖f x‖) ∧
      (∑' i, ∫ x in A i, ‖f x‖) ≤ mass f := by
  have hs := hasSum_integral_iUnion hA hdisj hf.norm.restrict
  refine ⟨hs.summable, ?_⟩
  rw [hs.tsum_eq]
  exact integral_mono_measure Measure.restrict_le_self
    (ae_of_all _ (fun _ => norm_nonneg _)) hf.norm

/--
The bad-average condition bounds the sum of real volumes by the mass divided by lam. Source: Hart
Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
theorem disjoint_volume_bound {f : Space d → ℝ} (hf : Integrable f)
    {lam : ℝ} (hlam : 0 < lam) {A : I → Set (Space d)}
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hbad : ∀ i, lam * volume.real (A i) ≤ ∫ x in A i, ‖f x‖) :
    Summable (fun i => volume.real (A i)) ∧
      (∑' i, volume.real (A i)) ≤ mass f / lam := by
  obtain ⟨hs, hsum⟩ := disjoint_integrals_summable hf hA hdisj
  have hle (i) : volume.real (A i) ≤ (∫ x in A i, ‖f x‖) / lam := by
    apply (le_div_iff₀ hlam).2
    simpa [mul_comm] using hbad i
  have hV := (hs.div_const lam).of_nonneg_of_le (fun i => ENNReal.toReal_nonneg) hle
  refine ⟨hV, ?_⟩
  calc
    (∑' i, volume.real (A i)) ≤ ∑' i, (∫ x in A i, ‖f x‖) / lam :=
      hV.tsum_le_tsum hle (hs.div_const lam)
    _ = (∑' i, ∫ x in A i, ‖f x‖) / lam := tsum_div_const
    _ ≤ mass f / lam := div_le_div_of_nonneg_right hsum hlam.le

omit [Countable I] in
/--
Transfer from a series of finite real volumes to its bound in ENNReal. Source: Hart Smith, Lecture
8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem ennreal_sum_of_real_bound {A : I → Set (Space d)}
    (hfin : ∀ i, volume (A i) ≠ ∞) (hs : Summable fun i => volume.real (A i))
    {L : ℝ} (hL : (∑' i, volume.real (A i)) ≤ L) :
    (∑' i, volume (A i)) ≤ ENNReal.ofReal L := by
  have heq (i) : volume (A i) = ENNReal.ofReal (volume.real (A i)) :=
    (ENNReal.ofReal_toReal (hfin i)).symm
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => show 0 ≤ volume.real (A i) from ENNReal.toReal_nonneg) hs]
  exact ENNReal.ofReal_le_ofReal hL

/--
Ball contract: positive radii, disjointness, bad averages, good dilates and exterior bound. Source:
Hart Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
structure BallFamily (d : ℕ) (f : Space d → ℝ) (lam : ℝ) where
  Index : Type
  countableIndex : Countable Index
  center : Index → Space d
  radius : Index → ℝ
  radius_pos : ∀ i, 0 < radius i
  disjoint : Pairwise (fun i j => Disjoint (ball (center i) (radius i))
    (ball (center j) (radius j)))
  bad : ∀ i, lam * volume.real (ball (center i) (radius i)) <
    ∫ x in ball (center i) (radius i), ‖f x‖
  good_dilate : ∀ i, (∫ x in ball (center i) (5 * radius i), ‖f x‖) ≤
    lam * volume.real (ball (center i) (5 * radius i))
  outside : ∀ᵐ x, x ∉ ⋃ i, ball (center i) (5 * radius i) → ‖f x‖ ≤ lam

attribute [instance] BallFamily.countableIndex

namespace BallFamily
variable {f : Space d → ℝ} {lam : ℝ} (F : BallFamily d f lam)

/--
Small open ball of the family, with radius radius i. Source: Hart Smith, Lecture 8, pp. 2–4; DPR,
pp. 1027–1028 (Page references unverified against the cited editions.)
-/
def core (i : F.Index) : Set (Space d) := ball (F.center i) (F.radius i)
/--
Concentric open ball with radius a * radius i; the definition imposes no positivity on a. Source:
Hart Smith, Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited
editions.)
-/
def expanded (a : ℝ) (i : F.Index) : Set (Space d) := ball (F.center i) (a * F.radius i)

/--
Estimate (31) and summability of the real volumes of the small balls. Source: Hart Smith, Lecture 8,
pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem sum_core (hf : Integrable f) (hlam : 0 < lam) :
    Summable (fun i => volume.real (F.core i)) ∧
      (∑' i, volume.real (F.core i)) ≤ mass f / lam :=
  disjoint_volume_bound hf hlam (fun _ => measurableSet_ball) F.disjoint (fun i => (F.bad i).le)

/--
Summability and bound a^d * mass f / lam for every positive dilation. Source: Hart Smith, Lecture 8,
pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem sum_expanded (hf : Integrable f) (hlam : 0 < lam) {a : ℝ} (ha : 0 < a) :
    Summable (fun i => volume.real (F.expanded a i)) ∧
      (∑' i, volume.real (F.expanded a i)) ≤ a ^ d * mass f / lam := by
  have heq (i) : volume.real (F.expanded a i) = a ^ d * volume.real (F.core i) :=
    real_ball_scale _ _ ha
  simp_rw [heq]
  obtain ⟨hs, hb⟩ := F.sum_core hf hlam
  refine ⟨hs.mul_left _, ?_⟩
  rw [tsum_mul_left]
  have := mul_le_mul_of_nonneg_left hb (pow_nonneg ha.le d)
  simpa [mul_div_assoc] using this

/--
Volume bound on the dilated union by subadditivity, with no overlap bound. Source: Hart Smith,
Lecture 8, pp. 2–4; DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem measure_expanded_union (hf : Integrable f) (hlam : 0 < lam)
    {a : ℝ} (ha : 0 < a) :
    volume (⋃ i, F.expanded a i) ≤ ENNReal.ofReal (a ^ d * mass f / lam) := by
  obtain ⟨hs, hb⟩ := F.sum_expanded hf hlam ha
  exact (measure_iUnion_le _).trans (ennreal_sum_of_real_bound
    (fun _ => measure_ball_lt_top.ne) hs hb)

end BallFamily

/--
existence assuming only d ≥ 1, integrable f and lam > 0. Source: Hart Smith, Lecture 8, pp. 2–4;
DPR, pp. 1027–1028 (Page references unverified against the cited editions.)
-/
theorem exists_ballFamily {d : ℕ} (hd : 1 ≤ d) {f : Space d → ℝ}
    (hf : Integrable f) {lam : ℝ} (hlam : 0 < lam) :
    Nonempty (BallFamily d f lam) := by
  obtain ⟨s, r, hc, hdj, hbad, hgood, hout⟩ := select_balls hd hf hlam
  letI := hc.toEncodable
  refine ⟨{
    Index := s
    countableIndex := inferInstance
    center := Subtype.val
    radius := fun i => r i
    radius_pos := fun i => (hbad i i.property).1
    disjoint := ?_
    bad := fun i => (hbad i i.property).2
    good_dilate := fun i => hgood i i.property
    outside := ?_ }⟩
  · intro i j hij
    exact hdj i.property j.property (fun h => hij (Subtype.ext h))
  · filter_upwards [hout] with x hx hn
    apply hx
    simpa only [iUnion_subtype] using hn

end GeometricMeasure.CalderonZygmund

end
