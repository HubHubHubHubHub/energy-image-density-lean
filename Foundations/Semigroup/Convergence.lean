import Foundations.Semigroup.Estimates
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Normed.Operator.Completeness

noncomputable section
open Filter Topology Set
namespace Foundations.ContractionResolvent
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable (R : ContractionResolvent H)

theorem uniformCauchy_semigroupApprox_dom (x : R.dom) {T : ℝ} (hT : 0 ≤ T) :
    UniformCauchySeqOn (fun b t => R.semigroupApprox b t x) atTop (Icc 0 T) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (R.tendsto_yosida x).cauchySeq
    (ε/(T+1)) (div_pos hε (by linarith))
  refine ⟨max N 1, fun a ha b hb t ht => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans ha)
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hb)
  have hh := hN a ((le_max_left _ _).trans ha) b ((le_max_left _ _).trans hb)
  rw [dist_eq_norm] at hh ⊢
  apply (R.norm_semigroupApprox_sub_le ha0 hb0 ht.1 x).trans_lt
  have hmul : (T+1) * ‖R.yosida a x - R.yosida b x‖ < ε :=
    by nlinarith [(lt_div_iff₀ (by linarith : 0 < T+1)).mp hh]
  nlinarith [ht.2, norm_nonneg (R.yosida a x - R.yosida b x)]

theorem uniformCauchy_semigroupApprox (x : H) {T : ℝ} (hT : 0 ≤ T) :
    UniformCauchySeqOn (fun b t => R.semigroupApprox b t x) atTop (Icc 0 T) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := R.dense_dom.exists_dist_lt x (by positivity : 0 < ε/4)
  obtain ⟨N,hN⟩ := Metric.uniformCauchySeqOn_iff.mp
    (R.uniformCauchy_semigroupApprox_dom ⟨y,hy⟩ hT) (ε/2) (by positivity)
  refine ⟨max N 1, fun a ha b hb t ht => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans ha)
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hb)
  have hm := hN a ((le_max_left _ _).trans ha) b ((le_max_left _ _).trans hb) t ht
  have h₁ : dist (R.semigroupApprox a t x) (R.semigroupApprox a t y) ≤ dist x y := by
    simpa [dist_eq_norm, ← map_sub] using R.norm_semigroupApprox_apply_le ha0 ht.1 (x-y)
  have h₂ : dist (R.semigroupApprox b t y) (R.semigroupApprox b t x) ≤ dist x y := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_sub_rev x y]
    exact R.norm_semigroupApprox_apply_le hb0 ht.1 (y-x)
  have hd := dist_triangle4 (R.semigroupApprox a t x) (R.semigroupApprox a t y)
    (R.semigroupApprox b t y) (R.semigroupApprox b t x)
  dsimp at hm
  linarith

def semigroupLimit (t : ℝ) (x : H) : H := limUnder atTop (fun b => R.semigroupApprox b t x)

theorem cauchy_semigroupApprox {t : ℝ} (ht : 0 ≤ t) (x : H) :
    CauchySeq (fun b : ℝ => R.semigroupApprox b t x) :=
  (R.uniformCauchy_semigroupApprox x ht).cauchySeq (right_mem_Icc.mpr ht)

theorem tendsto_semigroupApprox {t : ℝ} (ht : 0 ≤ t) (x : H) :
    Tendsto (fun b => R.semigroupApprox b t x) atTop (𝓝 (R.semigroupLimit t x)) :=
  (R.cauchy_semigroupApprox ht x).tendsto_limUnder

theorem tendstoUniformlyOn_semigroupApprox (x : H) {T : ℝ} (hT : 0 ≤ T) :
    TendstoUniformlyOn (fun b t => R.semigroupApprox b t x) (fun t => R.semigroupLimit t x)
      atTop (Icc 0 T) :=
  (R.uniformCauchy_semigroupApprox x hT).tendstoUniformlyOn_of_tendsto
    (fun _ ht => R.tendsto_semigroupApprox ht.1 x)

theorem norm_semigroupLimit_le {t : ℝ} (ht : 0 ≤ t) (x : H) :
    ‖R.semigroupLimit t x‖ ≤ ‖x‖ := by
  apply le_of_tendsto (R.tendsto_semigroupApprox ht x).norm
  filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb
  exact R.norm_semigroupApprox_apply_le hb ht x

end Foundations.ContractionResolvent
