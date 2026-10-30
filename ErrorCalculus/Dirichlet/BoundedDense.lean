import ErrorCalculus.Dirichlet.ContractionLipschitz
import ErrorCalculus.Dirichlet.GeneratorWeights
import ErrorCalculus.Dirichlet.LowerSemicontinuous
import ErrorCalculus.Dirichlet.ExtensionLp

noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace
namespace ErrorCalculus

theorem norm_truncation_le_self (M x : ℝ) : ‖truncation M x‖ ≤ ‖x‖ := by
  have h := (truncation_lipschitz M).dist_le_mul x 0
  simpa only [truncation, intervalIntegral.integral_same, dist_zero_right,
    NNReal.coe_one, one_mul] using h

namespace ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- Smooth bounded approximants in the original form domain. -/
def truncationSeq (v : S.dom) (n : ℕ) : S.dom :=
  S.lipschitzComp (truncation_lipschitz (n : ℝ)) v

theorem coeFn_truncationSeq (v : S.dom) (n : ℕ) :
    ⇑(S.truncationSeq v n : Lp ℝ 2 μ) =ᵐ[μ]
      fun ω => truncation n ((v : Lp ℝ 2 μ) ω) := S.coeFn_lipschitzComp _ _

theorem bounded_truncationSeq (v : S.dom) (n : ℕ) :
    AEBounded (μ := μ) (S.truncationSeq v n : Lp ℝ 2 μ) :=
  ⟨truncationBound n, (S.coeFn_truncationSeq v n).mono fun ω he => by
    rw [he]; exact norm_truncation_le _ _⟩

theorem norm_truncationSeq_le (v : S.dom) (n : ℕ) :
    ‖(S.truncationSeq v n : Lp ℝ 2 μ)‖ ≤ ‖(v : Lp ℝ 2 μ)‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [S.coeFn_truncationSeq v n] with ω he
  rw [he]
  exact norm_truncation_le_self _ _

theorem energy_truncationSeq_le (v : S.dom) (n : ℕ) :
    S.energy.E (S.truncationSeq v n) (S.truncationSeq v n) ≤ S.energy.E v v := by
  simpa using S.energy_contraction (truncation_contDiff (n : ℝ))
    (truncation_lipschitz (n : ℝ)) v (S.truncationSeq v n) (S.coeFn_truncationSeq v n)

/-- L² convergence uses domination by 2|v|, not convergence in the form norm. -/
theorem tendsto_truncationSeq (v : S.dom) :
    Tendsto (fun n => (S.truncationSeq v n : Lp ℝ 2 μ)) atTop (𝓝 (v : Lp ℝ 2 μ)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply lp_two_tendsto_zero_of_dominated _ ((2 : ℝ) • (v : Lp ℝ 2 μ))
  · intro n
    filter_upwards [Lp.coeFn_sub (S.truncationSeq v n : Lp ℝ 2 μ) v,
      S.coeFn_truncationSeq v n, Lp.coeFn_smul (2 : ℝ) (v : Lp ℝ 2 μ)] with ω hs ht h2
    simp only [hs, ht, h2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    have h := norm_truncation_le_self (n : ℝ) ((v : Lp ℝ 2 μ) ω)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    linarith [abs_sub (truncation (n : ℝ) ((v : Lp ℝ 2 μ) ω)) ((v : Lp ℝ 2 μ) ω)]
  · filter_upwards [ae_all_iff.mpr (fun n => Lp.coeFn_sub (S.truncationSeq v n : Lp ℝ 2 μ) v),
      ae_all_iff.mpr (S.coeFn_truncationSeq v)] with ω hs ht
    apply tendsto_const_nhds.congr'
    obtain ⟨N,hN⟩ := exists_nat_ge |(v : Lp ℝ 2 μ) ω|
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnR : |(v : Lp ℝ 2 μ) ω| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
    simp only [hs n, Pi.sub_apply, ht n, truncation_eq_self hnR, sub_self]

/--
bounded domain tests determine every continuous linear functional on the form Hilbert space. This is
weak density, without a claim that the truncations converge strongly in the form norm.
-/
theorem formFunctional_eq_zero_of_bounded (ℓ : S.energy.FormSpace →L[ℝ] ℝ)
    (hℓ : ∀ v : S.dom, AEBounded (μ := μ) (v : Lp ℝ 2 μ) →
      ℓ (S.energy.formToDomain.symm v) = 0) (v : S.dom) :
    ℓ (S.energy.formToDomain.symm v) = 0 := by
  letI := S.energy_closed.completeSpace_formSpace
  let x : ℕ → S.energy.FormSpace := fun n => S.energy.formToDomain.symm (S.truncationSeq v n)
  let R := Real.sqrt (‖(v : Lp ℝ 2 μ)‖ ^ 2 + S.energy.E v v)
  have hr : 0 ≤ ‖(v : Lp ℝ 2 μ)‖ ^ 2 + S.energy.E v v :=
    add_nonneg (sq_nonneg _) (S.energy.nonneg v)
  have hb : ∀ n, ‖x n‖ ≤ R := by
    intro n
    apply (Real.le_sqrt (norm_nonneg _) hr).mpr
    rw [S.energy.formSpace_norm_sq]
    change ‖(S.truncationSeq v n : Lp ℝ 2 μ)‖ ^ 2 +
      S.energy.E (S.truncationSeq v n) (S.truncationSeq v n) ≤ _
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (S.norm_truncationSeq_le v n) 2)
      (S.energy_truncationSeq_le v n)
  obtain ⟨z,_,hc⟩ := exists_weak_clusterPt_of_frequently_norm_le x R (Eventually.of_forall hb).frequently
  have he := QuadForm.formInclusion_eq_of_weak_cluster hc inf_le_left (S.tendsto_truncationSeq v)
  have hz : S.energy.formToDomain z = v := Subtype.ext he
  have heval := weak_cluster_eval_eq hc inf_le_left ℓ
    (show Tendsto (fun n => ℓ (x n)) atTop (𝓝 0) from by
      simpa only [x, hℓ _ (S.bounded_truncationSeq v _)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  simpa only [← hz, LinearEquiv.symm_apply_apply] using heval

/-- extend an energy identity from bounded tests to the whole domain. -/
theorem energy_identity_of_bounded (w : S.dom) (h : Lp ℝ 2 μ)
    (he : ∀ v : S.dom, AEBounded (μ := μ) (v : Lp ℝ 2 μ) →
      S.energy.E w v = inner ℝ h (v : Lp ℝ 2 μ)) (v : S.dom) :
    S.energy.E w v = inner ℝ h (v : Lp ℝ 2 μ) := by
  let ℓ := S.energy.formBilin 0 (S.energy.formToDomain.symm w) -
    (InnerProductSpace.toDualMap ℝ (Lp ℝ 2 μ) h).comp S.energy.formInclusion
  have hl (z : S.dom) : ℓ (S.energy.formToDomain.symm z) =
      S.energy.E w z - inner ℝ h (z : Lp ℝ 2 μ) := by
    simp [ℓ, QuadForm.formBilin_apply, QuadForm.formInclusion]
  have hz := S.formFunctional_eq_zero_of_bounded ℓ (fun z hb => by rw [hl, he z hb, sub_self]) v
  rw [hl] at hz
  exact sub_eq_zero.mp hz

end ErrorStructure
end ErrorCalculus
