import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Separation.Hausdorff

noncomputable section
open Filter Topology
namespace ErrorCalculus
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/--
Banach--Alaoglu and Riesz, along the filter of bounded indices. No separability assumption or
subsequence extraction is used.
-/
theorem exists_weak_clusterPt_of_frequently_norm_le (g : ℕ → V) (R : ℝ)
    (hb : ∃ᶠ n in atTop, ‖g n‖ ≤ R) :
    ∃ v : V, ‖v‖ ≤ R ∧ ∀ w : V,
      ClusterPt (inner ℝ v w)
        (map (fun n => inner ℝ (g n) w) (atTop ⊓ 𝓟 {n | ‖g n‖ ≤ R})) := by
  let l : Filter ℕ := atTop ⊓ 𝓟 {n | ‖g n‖ ≤ R}
  haveI : l.NeBot := frequently_iff_neBot.mp hb
  let f : ℕ → WeakDual ℝ V := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ V (g n))
  have hf : map f l ≤ 𝓟 (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R) := by
    rw [Filter.map_le_iff_le_comap, Filter.comap_principal]
    apply inf_le_right.trans
    apply Filter.principal_mono.mpr
    intro n hn
    simpa [f, Metric.mem_closedBall, dist_zero_right] using hn
  obtain ⟨φ, hφ, hc⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ V) R).exists_clusterPt hf
  let v := (InnerProductSpace.toDual ℝ V).symm (WeakDual.toStrongDual φ)
  refine ⟨v, ?_, fun w => ?_⟩
  · simpa only [v, LinearIsometryEquiv.norm_map, Set.mem_preimage,
      Metric.mem_closedBall, dist_zero_right] using hφ
  · have he := hc.map (WeakDual.eval_continuous w).continuousAt tendsto_map
    rw [show inner ℝ v w = φ w from InnerProductSpace.toDual_symm_apply]
    simpa [Filter.map_map, Function.comp_def, f, l] using he

/-- a scalar cluster point of a convergent filtered family is its limit. -/
theorem clusterPt_eq_of_tendsto {α : Type*} {l : Filter α} {f : α → ℝ} {a b : ℝ}
    (hc : ClusterPt a (map f l)) (ht : Tendsto f l (𝓝 b)) : a = b :=
  eq_of_nhds_neBot (hc.mono ht).neBot

/-- identification by any continuous linear evaluation, using Riesz. -/
theorem weak_cluster_eval_eq {g : ℕ → V} {v : V} {l : Filter ℕ}
    (hc : ∀ w : V, ClusterPt (inner ℝ v w) (map (fun n => inner ℝ (g n) w) l))
    (hl : l ≤ atTop) (ℓ : V →L[ℝ] ℝ) {a : ℝ}
    (ht : Tendsto (fun n => ℓ (g n)) atTop (𝓝 a)) : ℓ v = a := by
  let w := (InnerProductSpace.toDual ℝ V).symm ℓ
  have he (x : V) : inner ℝ x w = ℓ x := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hh := hc w
  simp only [he] at hh
  exact clusterPt_eq_of_tendsto hh (ht.mono_left hl)

end ErrorCalculus
