import Foundations.Semigroup.Generator

noncomputable section
open Filter Topology Set
namespace Foundations

/-- A strongly continuous contraction semigroup; negative times are ignored. -/
structure ContractionSemigroup (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  S : ℝ → H →L[ℝ] H
  norm_le : ∀ {t}, 0 ≤ t → ‖S t‖ ≤ 1
  zero : S 0 = 1
  add : ∀ {s t}, 0 ≤ s → 0 ≤ t → S (s+t) = S s * S t
  continuous : ∀ x, ContinuousOn (fun t => S t x) (Ici 0)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
namespace ContractionSemigroup
variable (S : ContractionSemigroup H)

theorem norm_apply_le {t : ℝ} (ht : 0 ≤ t) (x : H) : ‖S.S t x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using (S.S t).le_of_opNorm_le (S.norm_le ht) x

theorem commute {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : Commute (S.S s) (S.S t) := by
  change S.S s * S.S t = S.S t * S.S s
  rw [← S.add hs ht, ← S.add ht hs, add_comm]

theorem tendsto_zero (x : H) : Tendsto (fun t => S.S t x) (𝓝[≥] 0) (𝓝 x) := by
  simpa [ContinuousWithinAt, S.zero] using S.continuous x 0 (show (0:ℝ) ∈ Ici 0 by simp)

end ContractionSemigroup

def ContractionResolvent.toSemigroup [CompleteSpace H] (R : ContractionResolvent H) :
    ContractionSemigroup H where
  S := R.semigroup
  norm_le := R.norm_semigroup_le_one
  zero := R.semigroup_zero
  add := R.semigroup_add
  continuous := R.continuous_semigroup_apply

end Foundations
