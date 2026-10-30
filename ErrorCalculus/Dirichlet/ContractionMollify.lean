import ErrorCalculus.Dirichlet.LipschitzContinuity

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/--
AA.3(a): the convolution with a nonnegative normalized ContDiffBump, with outer radius εₙ = 2⁻ⁿ.
-/
def mollifyLipschitz (F : ℝ → ℝ) (n : ℕ) : ℝ → ℝ := lipschitzMollify F n

theorem mollifyLipschitz_contDiff {F : ℝ → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L F) (n : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (mollifyLipschitz F n) :=
  lipschitzMollify_contDiff hL n

theorem mollifyLipschitz_lipschitz {F : ℝ → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L F) (n : ℕ) : LipschitzWith L (mollifyLipschitz F n) :=
  lipschitzMollify_lipschitz hL n

theorem mollifyLipschitz_error_le {F : ℝ → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L F) (n : ℕ) (x : ℝ) :
    |mollifyLipschitz F n x - F x| ≤ (L : ℝ) * (1/2 : ℝ)^n :=
  abs_lipschitzMollify_sub_le hL n x

variable (S : ErrorStructure Ω μ)

/-- AA.3(a): the regularized compositions converge in L², for any Lipschitz F. -/
theorem tendsto_lipschitzComp_mollify_L2 {F : ℝ → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L F) (u : S.dom) :
    Tendsto (fun n => (S.lipschitzComp (mollifyLipschitz_lipschitz hL n) u : Lp ℝ 2 μ))
      atTop (𝓝 (S.lipschitzComp hL u : Lp ℝ 2 μ)) := by
  apply tendsto_Lp_of_uniform_error (e := fun n => (L : ℝ) * (1/2 : ℝ)^n)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).const_mul (L : ℝ)
  · intro n
    filter_upwards [S.coeFn_lipschitzComp (mollifyLipschitz_lipschitz hL n) u,
      S.coeFn_lipschitzComp hL u] with ω hn hu
    rw [hn, hu]
    exact mollifyLipschitz_error_le hL n _

/--
AA.3(a): lower semicontinuity along the smooth regularizations, together with the uniform
contraction bound. This re-proves the energy bound; it does not assert convergence in the form
norm for a nonsmooth F.
-/
theorem energy_lipschitzComp_le_liminf {F : ℝ → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L F) (u : S.dom) :
    S.energy.E (S.lipschitzComp hL u) (S.lipschitzComp hL u) ≤
      liminf (fun n => S.energy.E (S.lipschitzComp (mollifyLipschitz_lipschitz hL n) u)
        (S.lipschitzComp (mollifyLipschitz_lipschitz hL n) u)) atTop ∧
    liminf (fun n => S.energy.E (S.lipschitzComp (mollifyLipschitz_lipschitz hL n) u)
      (S.lipschitzComp (mollifyLipschitz_lipschitz hL n) u)) atTop ≤
        (L : ℝ)^2 * S.energy.E u u := by
  let x n := S.lipschitzComp (mollifyLipschitz_lipschitz hL n) u
  have hb n : S.energy.E (x n) (x n) ≤ (L : ℝ)^2 * S.energy.E u u :=
    S.energy_contraction ((mollifyLipschitz_contDiff hL n).of_le (by simp))
      (mollifyLipschitz_lipschitz hL n) u (x n)
      (S.coeFn_lipschitzComp (mollifyLipschitz_lipschitz hL n) u)
  constructor
  · exact S.energy_closed.energy_le_liminf (S.tendsto_lipschitzComp_mollify_L2 hL u)
      ⟨_, (Eventually.of_forall hb).frequently⟩ (S.lipschitzComp hL u).property
  · apply liminf_le_of_le
      (show IsBoundedUnder (· ≥ ·) atTop (fun n => S.energy.E (x n) (x n)) from
        ⟨0, show ∀ᶠ n in atTop, 0 ≤ S.energy.E (x n) (x n) from
          Eventually.of_forall fun n => S.energy.nonneg (x n)⟩)
    intro b h
    obtain ⟨n, hn⟩ := h.exists
    exact hn.trans (hb n)

/-- The normal contraction specialization has the exact constant one. -/
theorem energy_normalContraction_mollify_le_liminf {F : ℝ → ℝ}
    (hL : LipschitzWith 1 F) (u : S.dom) :
    S.energy.E (S.lipschitzComp hL u) (S.lipschitzComp hL u) ≤
      liminf (fun n => S.energy.E (S.lipschitzComp (mollifyLipschitz_lipschitz hL n) u)
        (S.lipschitzComp (mollifyLipschitz_lipschitz hL n) u)) atTop ∧
    liminf (fun n => S.energy.E (S.lipschitzComp (mollifyLipschitz_lipschitz hL n) u)
      (S.lipschitzComp (mollifyLipschitz_lipschitz hL n) u)) atTop ≤ S.energy.E u u := by
  simpa using S.energy_lipschitzComp_le_liminf hL u

end ErrorCalculus.ErrorStructure
