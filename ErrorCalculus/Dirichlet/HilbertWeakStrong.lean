import ErrorCalculus.Dirichlet.WeakCluster
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Tactic

noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace ErrorCalculus
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/--
weak convergence and an upper norm limsup imply strong convergence. The boundedness assumption makes
the real-valued limsup nondegenerate.
-/
theorem tendsto_of_weak_tendsto_of_limsup_norm_le_of_bounded {g : ℕ → V} {x : V}
    (hw : ∀ w, Tendsto (fun n => inner ℝ (g n) w) atTop (𝓝 (inner ℝ x w)))
    (hb : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖g n‖))
    (hs : limsup (fun n => ‖g n‖) atTop ≤ ‖x‖) :
    Tendsto g atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : Tendsto (fun n => ‖g n - x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall fun n => ha.trans_le (sq_nonneg _)
    · intro b hbpos
      have hr : ‖x‖ < Real.sqrt (‖x‖ ^ 2 + b / 2) := by
        apply (Real.lt_sqrt (norm_nonneg _)).mpr
        linarith
      have hn := eventually_lt_of_limsup_lt (hs.trans_lt hr) hb
      have hi : Tendsto (fun n => -2 * inner ℝ (g n) x + ‖x‖ ^ 2)
          atTop (𝓝 (-‖x‖ ^ 2)) := by
        have hi0 := ((hw x).const_mul (-2)).add_const (‖x‖ ^ 2)
        simpa only [real_inner_self_eq_norm_sq,
          show -2 * ‖x‖^2 + ‖x‖^2 = -‖x‖^2 by ring] using hi0
      have hi' := hi.eventually (gt_mem_nhds (show -‖x‖ ^ 2 < -‖x‖ ^ 2 + b/2 by linarith))
      filter_upwards [hn, hi'] with n hn hi'
      have hnn := (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hn
      rw [Real.sq_sqrt (by positivity)] at hnn
      rw [norm_sub_sq_real]
      linarith
  simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hsq.sqrt

variable [CompleteSpace V]

/-- Weakly convergent sequences in a Hilbert space are norm bounded, by
Banach--Steinhaus applied to their Riesz functionals. -/
theorem bounded_norm_of_weak_tendsto {g : ℕ → V} {x : V}
    (hw : ∀ w, Tendsto (fun n => inner ℝ (g n) w) atTop (𝓝 (inner ℝ x w))) :
    ∃ R : ℝ, ∀ n, ‖g n‖ ≤ R := by
  have hp : ∀ w : V, ∃ C : ℝ, ∀ n,
      ‖(InnerProductSpace.toDual ℝ V (g n)) w‖ ≤ C := by
    intro w
    obtain ⟨C, hC⟩ := (hw w).norm.bddAbove_range
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩
  obtain ⟨R, hR⟩ := banach_steinhaus hp
  exact ⟨R, fun n => by simpa only [LinearIsometryEquiv.norm_map] using hR n⟩

/--
Weak convergence of a Hilbert-space sequence to x, together with limsup ‖gₙ‖ ≤ ‖x‖, implies norm
convergence to x.
-/
theorem tendsto_of_weak_tendsto_of_limsup_norm_le {g : ℕ → V} {x : V}
    (hw : ∀ w, Tendsto (fun n => inner ℝ (g n) w) atTop (𝓝 (inner ℝ x w)))
    (hs : limsup (fun n => ‖g n‖) atTop ≤ ‖x‖) :
    Tendsto g atTop (𝓝 x) := by
  obtain ⟨R, hR⟩ := bounded_norm_of_weak_tendsto hw
  exact tendsto_of_weak_tendsto_of_limsup_norm_le_of_bounded hw
    (isBoundedUnder_of_eventually_le (Eventually.of_forall hR)) hs

/--
Filter version of Banach--Alaoglu/Riesz extraction, for arbitrary nontrivial filters. In particular
this applies to `atTop ⊓ 𝓟 A`.
-/
theorem exists_weak_clusterPt_of_eventually_norm_le {α : Type*} {l : Filter α}
    [l.NeBot] (g : α → V) (R : ℝ) (hb : ∀ᶠ n in l, ‖g n‖ ≤ R) :
    ∃ v : V, ‖v‖ ≤ R ∧ ∀ w : V,
      ClusterPt (inner ℝ v w) (map (fun n => inner ℝ (g n) w) l) := by
  let f : α → WeakDual ℝ V := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ V (g n))
  have hf : map f l ≤ 𝓟 (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R) := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    change ∀ᶠ n in l, f n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R
    filter_upwards [hb] with n hn
    simpa [f, Metric.mem_closedBall, dist_zero_right] using hn
  obtain ⟨φ, hφ, hc⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ V) R).exists_clusterPt hf
  let v := (InnerProductSpace.toDual ℝ V).symm (WeakDual.toStrongDual φ)
  refine ⟨v, ?_, fun w => ?_⟩
  · simpa only [v, LinearIsometryEquiv.norm_map, Set.mem_preimage,
      Metric.mem_closedBall, dist_zero_right] using hφ
  · have he := hc.map (WeakDual.eval_continuous w).continuousAt tendsto_map
    rw [show inner ℝ v w = φ w from InnerProductSpace.toDual_symm_apply]
    simpa [Filter.map_map, Function.comp_def, f] using he

/--
boundedness and uniqueness of weak cluster points along every frequent set of indices imply weak
convergence, without separability.
-/
theorem weak_tendsto_of_bounded_of_clusterPt_unique {g : ℕ → V} {x : V} {R : ℝ}
    (hb : ∀ᶠ n in atTop, ‖g n‖ ≤ R)
    (hu : ∀ (A : Set ℕ), (∃ᶠ n in atTop, n ∈ A) → ∀ v : V,
      (∀ w, ClusterPt (inner ℝ v w)
        (map (fun n => inner ℝ (g n) w) (atTop ⊓ 𝓟 A))) → v = x) :
    ∀ w, Tendsto (fun n => inner ℝ (g n) w) atTop (𝓝 (inner ℝ x w)) := by
  intro w
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_contra h
  let A : Set ℕ := {n | ε ≤ dist (inner ℝ (g n) w) (inner ℝ x w)}
  have hA : ∃ᶠ n in atTop, n ∈ A := by
    simpa only [A, Set.mem_setOf_eq, Filter.Frequently, not_le] using h
  let l : Filter ℕ := atTop ⊓ 𝓟 A
  haveI : l.NeBot := frequently_iff_neBot.mp hA
  obtain ⟨v, _, hv⟩ := exists_weak_clusterPt_of_eventually_norm_le g R
    (show ∀ᶠ n in l, ‖g n‖ ≤ R from hb.filter_mono inf_le_left)
  have he := hu A hA v hv
  have hm : {a : ℝ | ε ≤ dist a (inner ℝ x w)} ∈
      map (fun n => inner ℝ (g n) w) l := by
    change A ∈ atTop ⊓ 𝓟 A
    exact Filter.mem_of_superset (Filter.mem_inf_of_right (Filter.mem_principal_self A))
      (fun _ hn => hn)
  have hc := (hv w).mem_closure_of_mem _ hm
  have hclosed : IsClosed {a : ℝ | ε ≤ dist a (inner ℝ x w)} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  rw [hclosed.closure_eq] at hc
  have hh : ε ≤ 0 := by simpa [he] using hc
  linarith

/-- The combined weak-compactness and Hilbert norm criterion. -/
theorem tendsto_of_bounded_of_clusterPt_eq_of_limsup_norm_le {g : ℕ → V} {x : V} {R : ℝ}
    (hb : ∀ᶠ n in atTop, ‖g n‖ ≤ R)
    (hu : ∀ (A : Set ℕ), (∃ᶠ n in atTop, n ∈ A) → ∀ v : V,
      (∀ w, ClusterPt (inner ℝ v w)
        (map (fun n => inner ℝ (g n) w) (atTop ⊓ 𝓟 A))) → v = x)
    (hs : limsup (fun n => ‖g n‖) atTop ≤ ‖x‖) :
    Tendsto g atTop (𝓝 x) := by
  exact tendsto_of_weak_tendsto_of_limsup_norm_le
    (weak_tendsto_of_bounded_of_clusterPt_unique hb hu) hs

end ErrorCalculus
