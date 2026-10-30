import GeometricMeasure.VectorMeasure.Differentiation

/-!
# Good radii for a singular measure

## Main results
For a locally finite measure `s` singular with respect to Lebesgue measure on `EuclideanSpace ℝ (Fin
d)`, at `s`-almost every point `x` there are arbitrarily small radii `r > 0` such that `s
(closedBall x r) ≤ 2 ^ d * s (closedBall x (r / 2))`.

Proof by Besicovitch, `volume (B̄ x r) / s (B̄ x r) → 0` `s`-almost everywhere; if the reverse
strict inequality held on an entire interval `]0, ε[`, this ratio would not decrease along `r₀ 2⁻ᵏ`,
contradicting the zero limit.

No `Nontrivial`, `d ≥ 1` or global finiteness assumption on `s`.
-/

noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ}

/-- Lebesgue scaling for r ≥ 0: `vol (B̄ x r) = 2ᵈ vol (B̄ x (r/2))`. -/
theorem volume_closedBall_eq_two_pow_mul_half (x : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hr : 0 ≤ r) :
    volume (closedBall x r) = 2 ^ d * volume (closedBall x (r / 2)) := by
  rw [Measure.addHaar_closedBall' volume x hr,
    Measure.addHaar_closedBall' volume x (by positivity : 0 ≤ r / 2),
    finrank_euclideanSpace_fin, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  congr 2
  ring

/--
For r ≥ 0, if `2ᵈ s(B̄_{r/2}) ≤ s(B̄_r)`, the ratio `vol/s` does not decrease from `r` to `r/2`.
-/
theorem volume_div_closedBall_le_half (s : Measure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 ≤ r)
    (h : 2 ^ d * s (closedBall x (r / 2)) ≤ s (closedBall x r)) :
    volume (closedBall x r) / s (closedBall x r) ≤
      volume (closedBall x (r / 2)) / s (closedBall x (r / 2)) := by
  rw [volume_closedBall_eq_two_pow_mul_half x hr]
  calc
    _ ≤ 2 ^ d * volume (closedBall x (r / 2)) / (2 ^ d * s (closedBall x (r / 2))) :=
      ENNReal.div_le_div_left h _
    _ = _ := ENNReal.mul_div_mul_left _ _ (by simp) (by simp)

/-- Pointwise version: if `vol/s → 0` at `x`, good radii occur frequently. -/
theorem frequently_closedBall_le_two_pow_mul_half_of_tendsto
    (s : Measure (EuclideanSpace ℝ (Fin d))) [IsLocallyFiniteMeasure s]
    (x : EuclideanSpace ℝ (Fin d))
    (hx : Tendsto (fun r => volume (closedBall x r) / s (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∃ᶠ r in 𝓝[>] (0 : ℝ), s (closedBall x r) ≤ 2 ^ d * s (closedBall x (r / 2)) := by
  intro hev
  simp only [not_le] at hev
  obtain ⟨ε, hε, hεP⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  set r₀ := ε / 2 with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  set g : ℝ → ℝ≥0∞ := fun r => volume (closedBall x r) / s (closedBall x r) with hg
  have hstep : ∀ k : ℕ, g r₀ ≤ g (r₀ * (1 / 2) ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hrk : 0 < r₀ * (1 / 2) ^ k := by positivity
      have hlt : r₀ * (1 / 2) ^ k < ε := by
        calc
          r₀ * (1 / 2) ^ k ≤ r₀ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hr₀pos.le
          _ < ε := by rw [mul_one, hr₀]; linarith
      have hh := hεP ⟨hrk, hlt⟩
      have heq : r₀ * (1 / 2) ^ (k + 1) = r₀ * (1 / 2) ^ k / 2 := by ring
      rw [heq]
      exact ih.trans (volume_div_closedBall_le_half s x hrk.le hh.le)
  have hpos : 0 < g r₀ := by
    apply ENNReal.div_pos_iff.mpr
    exact ⟨(measure_closedBall_pos volume x hr₀pos).ne', measure_closedBall_lt_top.ne⟩
  have hseq : Tendsto (fun k : ℕ => r₀ * (1 / 2) ^ k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall (fun k => ?_)⟩
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul r₀
    · exact mem_Ioi.mpr (by positivity)
  obtain ⟨k, hk⟩ := ((hx.comp hseq).eventually_lt_const hpos).exists
  exact absurd (hstep k) (not_le.mpr hk)

/--
**Good radii**: for locally finite `s ⟂ₘ volume`, at `s`-almost every point there are
arbitrarily small radii with `s(B̄_r) ≤ 2ᵈ s(B̄_{r/2})` (“frequently”).
-/
theorem ae_frequently_closedBall_le_two_pow_mul_half
    (s : Measure (EuclideanSpace ℝ (Fin d))) [IsLocallyFiniteMeasure s]
    (hs : s ⟂ₘ (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ∀ᵐ x ∂s, ∃ᶠ r in 𝓝[>] (0 : ℝ),
      s (closedBall x r) ≤ 2 ^ d * s (closedBall x (r / 2)) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv volume s, hs.symm.rnDeriv_ae_eq_zero]
    with x hx hz
  apply frequently_closedBall_le_two_pow_mul_half_of_tendsto s x
  simpa only [hz, Pi.zero_apply] using hx

end GeometricMeasure
