import ErrorCalculus.Dirichlet.ClosureData
import ErrorCalculus.Dirichlet.ExtensionLp

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- one subsequence works for every member of a finite L² family. -/
theorem exists_common_ae_subsequence {k : ℕ} (u : Fin k → ℕ → Lp ℝ 2 μ)
    (v : Fin k → Lp ℝ 2 μ) (hu : ∀ i, Tendsto (u i) atTop (𝓝 (v i))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n => u i (φ n) ω) atTop (𝓝 (v i ω)) := by
  induction k with
  | zero =>
    exact ⟨id, strictMono_id, ae_of_all _ (fun _ i => Fin.elim0 i)⟩
  | succ k ih =>
    obtain ⟨φ, hφ, hφa⟩ := ih (fun i => u i.succ) (fun i => v i.succ) (fun i => hu i.succ)
    obtain ⟨ψ, hψ, hψa⟩ := (tendstoInMeasure_of_tendsto_Lp ((hu 0).comp hφ.tendsto_atTop)).exists_seq_tendsto_ae
    refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
    filter_upwards [hφa, hψa] with ω hω h0
    intro i
    refine Fin.cases h0 (fun j => ?_) i
    exact (hω j).comp hψ.tendsto_atTop

/-- A pointwise square-root estimate, valid also for signed inputs after taking absolute values. -/
theorem sqrt_abs_sub_sq_le (a b : ℝ) :
    (Real.sqrt |a| - Real.sqrt |b|)^2 ≤ |a-b| := by
  have ha := Real.sq_sqrt (abs_nonneg a)
  have hb := Real.sq_sqrt (abs_nonneg b)
  have hc := abs_le.mp (abs_abs_sub_abs_le_abs_sub a b)
  rcases le_total (Real.sqrt |a|) (Real.sqrt |b|) with h | h
  · nlinarith [mul_nonneg (Real.sqrt_nonneg |a|) (sub_nonneg.mpr h)]
  · nlinarith [mul_nonneg (Real.sqrt_nonneg |b|) (sub_nonneg.mpr h)]

theorem sqrtAbs_memLp (f : Lp ℝ 1 μ) : MemLp (fun ω => Real.sqrt |f ω|) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_sqrt.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f).norm)).mpr
  apply (L1.integrable_coeFn f).norm.congr
  exact ae_of_all _ (fun ω => (Real.sq_sqrt (abs_nonneg (f ω))).symm)

/-- Square root of the absolute value, a map from L¹ to L². -/
def sqrtAbsLp (f : Lp ℝ 1 μ) : Lp ℝ 2 μ := (sqrtAbs_memLp f).toLp _

theorem coeFn_sqrtAbsLp (f : Lp ℝ 1 μ) :
    ⇑(sqrtAbsLp f) =ᵐ[μ] fun ω => Real.sqrt |f ω| := (sqrtAbs_memLp f).coeFn_toLp

/-- The one-half Hölder estimate for square roots as Lp classes. -/
theorem sqrtAbsLp_sub_norm_sq_le (f g : Lp ℝ 1 μ) :
    ‖sqrtAbsLp f - sqrtAbsLp g‖^2 ≤ ‖f-g‖ := by
  rw [lp_two_norm_sq, L1.norm_eq_integral_norm]
  apply integral_mono_ae
    ((memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
    (L1.integrable_coeFn _).norm
  filter_upwards [Lp.coeFn_sub (sqrtAbsLp f) (sqrtAbsLp g), coeFn_sqrtAbsLp f,
    coeFn_sqrtAbsLp g, Lp.coeFn_sub f g] with ω hd hf hg hfg
  simpa only [hd, hf, hg, hfg, Pi.sub_apply, Real.norm_eq_abs] using sqrt_abs_sub_sq_le (f ω) (g ω)

/-- Strong L¹ convergence implies strong L² convergence of the square roots. -/
theorem sqrtAbsLp_tendsto {f : ℕ → Lp ℝ 1 μ} {g : Lp ℝ 1 μ}
    (hf : Tendsto f atTop (𝓝 g)) : Tendsto (fun n => sqrtAbsLp (f n)) atTop (𝓝 (sqrtAbsLp g)) := by
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp hf
  have hs := squeeze_zero (fun n => sq_nonneg ‖sqrtAbsLp (f n)-sqrtAbsLp g‖)
    (fun n => sqrtAbsLp_sub_norm_sq_le (f n) g) hn
  have ht := hs.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht

namespace ErrorData
variable [IsProbabilityMeasure μ] (S : ErrorData Ω μ)

/-- The representative of the finite total error weight. -/
theorem coeFn_sqrtAbsLp_sum_gamma {k : ℕ} (u : Fin k → S.dom) :
    ⇑(sqrtAbsLp (∑ i, S.Γ (u i) (u i))) =ᵐ[μ]
      fun ω => Real.sqrt (∑ i, S.Γ (u i) (u i) ω) := by
  filter_upwards [coeFn_sqrtAbsLp (∑ i, S.Γ (u i) (u i)),
    lp_coeFn_sum Finset.univ (fun i => S.Γ (u i) (u i)),
    ae_all_iff.mpr (fun i => S.Γ_nonneg (u i))] with ω hs he hp
  rw [hs, he, abs_of_nonneg (Finset.sum_nonneg fun i _ => hp i)]

/-- The total error weights converge in L². This proof uses L¹ convergence of diagonals. -/
theorem sqrt_sum_gamma_tendsto (h : S.energy.IsClosable) {k : ℕ}
    {u : Fin k → ℕ → S.dom} {v : Fin k → S.energy.closureDom}
    (hu : ∀ i, S.energy.Approaches (u i) (v i)) :
    Tendsto (fun n => sqrtAbsLp (∑ i, S.Γ (u i n) (u i n))) atTop
      (𝓝 (sqrtAbsLp (∑ i, S.closureGamma h (v i) (v i)))) := by
  apply sqrtAbsLp_tendsto
  exact tendsto_finsetSum _ (fun i _ => S.closureGamma_characterization h (hu i) (hu i))

end ErrorData
end ErrorCalculus
