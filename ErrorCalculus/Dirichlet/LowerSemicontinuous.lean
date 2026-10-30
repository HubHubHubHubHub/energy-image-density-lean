import ErrorCalculus.Dirichlet.FormSpace
import ErrorCalculus.Dirichlet.WeakCluster
import ErrorCalculus.Dirichlet.Closure
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open Filter Topology
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Q : QuadForm H}

omit [CompleteSpace H] in
/-- identification of a weak form-space cluster point in the ambient space. -/
theorem formInclusion_eq_of_weak_cluster {x : ℕ → Q.FormSpace} {v : Q.FormSpace}
    {u : H} {l : Filter ℕ} [CompleteSpace Q.FormSpace]
    (hc : ∀ w, ClusterPt (inner ℝ v w) (map (fun n => inner ℝ (x n) w) l))
    (hl : l ≤ atTop) (ht : Tendsto (fun n => Q.formInclusion (x n)) atTop (𝓝 u)) :
    Q.formInclusion v = u := by
  apply ext_inner_left ℝ
  intro z
  exact weak_cluster_eval_eq hc hl ((InnerProductSpace.toDualMap ℝ H z).comp Q.formInclusion)
    (tendsto_const_nhds.inner (𝕜 := ℝ) ht)

/-- a frequently bounded energy controls the limit, up to any positive error. -/
theorem IsClosed.mem_dom_energy_le_add (hQ : Q.IsClosed) {x : ℕ → Q.dom} {u : H} {C : ℝ}
    (ht : Tendsto (fun n => (x n : H)) atTop (𝓝 u))
    (hb : ∃ᶠ n in atTop, Q.E (x n) (x n) ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ hu : u ∈ Q.dom, Q.E ⟨u, hu⟩ ⟨u, hu⟩ ≤ C + ε := by
  letI := hQ.completeSpace_formSpace
  let g : ℕ → Q.FormSpace := fun n => Q.formToDomain.symm (x n)
  have hC : 0 ≤ C := by
    obtain ⟨n, hn⟩ := hb.exists
    exact (Q.nonneg (x n)).trans hn
  have hr : 0 ≤ ‖u‖ ^ 2 + C + ε := by positivity
  have hn : ∀ᶠ n in atTop, ‖(x n : H)‖ ^ 2 < ‖u‖ ^ 2 + ε :=
    (ht.norm.pow 2).eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))
  have hg : ∃ᶠ n in atTop, ‖g n‖ ≤ Real.sqrt (‖u‖ ^ 2 + C + ε) := by
    apply (hb.and_eventually hn).mono
    intro n hn
    apply (Real.le_sqrt (norm_nonneg _) hr).mpr
    rw [Q.formSpace_norm_sq]
    change ‖(x n : H)‖ ^ 2 + Q.E (x n) (x n) ≤ _
    linarith [hn.1, hn.2]
  obtain ⟨v, hv, hc⟩ := exists_weak_clusterPt_of_frequently_norm_le g _ hg
  have he : Q.formInclusion v = u := formInclusion_eq_of_weak_cluster hc inf_le_left ht
  have hd : u ∈ Q.dom := he ▸ (Q.formToDomain v).property
  refine ⟨hd, ?_⟩
  have hn : ‖v‖ ^ 2 ≤ ‖u‖ ^ 2 + C + ε := by
    nlinarith [Real.sq_sqrt hr, norm_nonneg v, Real.sqrt_nonneg (‖u‖ ^ 2 + C + ε)]
  rw [Q.formSpace_norm_sq] at hn
  have he' : Q.formToDomain v = ⟨u, hd⟩ := Subtype.ext he
  rw [he'] at hn
  simpa using (by linarith : Q.E ⟨u, hd⟩ ⟨u, hd⟩ ≤ C + ε)

/-- Only a frequent energy bound is needed; no energy-Cauchy hypothesis. -/
theorem IsClosed.mem_dom_of_tendsto_of_energy_frequently_le (hQ : Q.IsClosed)
    {x : ℕ → Q.dom} {u : H} {C : ℝ}
    (ht : Tendsto (fun n => (x n : H)) atTop (𝓝 u))
    (hb : ∃ᶠ n in atTop, Q.E (x n) (x n) ≤ C) :
    ∃ hu : u ∈ Q.dom, Q.E ⟨u, hu⟩ ⟨u, hu⟩ ≤ C := by
  obtain ⟨hu, _⟩ := hQ.mem_dom_energy_le_add ht hb zero_lt_one
  refine ⟨hu, le_of_forall_pos_le_add fun ε hε => ?_⟩
  exact (hQ.mem_dom_energy_le_add ht hb hε).choose_spec

/-- The usual bounded-energy strong-limit theorem. -/
theorem IsClosed.mem_dom_of_tendsto_of_energy_le (hQ : Q.IsClosed)
    {x : ℕ → Q.dom} {u : H} {C : ℝ}
    (ht : Tendsto (fun n => (x n : H)) atTop (𝓝 u))
    (hb : ∀ n, Q.E (x n) (x n) ≤ C) :
    ∃ hu : u ∈ Q.dom, Q.E ⟨u, hu⟩ ⟨u, hu⟩ ≤ C :=
  hQ.mem_dom_of_tendsto_of_energy_frequently_le ht (Eventually.of_forall hb).frequently

/-- lower semicontinuity, with a finite frequent upper bound for the real liminf. -/
theorem IsClosed.energy_le_liminf (hQ : Q.IsClosed) {x : ℕ → Q.dom} {u : H}
    (ht : Tendsto (fun n => (x n : H)) atTop (𝓝 u))
    (hb : ∃ C : ℝ, ∃ᶠ n in atTop, Q.E (x n) (x n) ≤ C) (hu : u ∈ Q.dom) :
    Q.E ⟨u, hu⟩ ⟨u, hu⟩ ≤ liminf (fun n => Q.E (x n) (x n)) atTop := by
  obtain ⟨C, hC⟩ := hb
  have hco : IsCoboundedUnder (· ≥ ·) atTop (fun n => Q.E (x n) (x n)) := by
    refine ⟨C, fun b hb => ?_⟩
    obtain ⟨n, hn, hn'⟩ := (hC.and_eventually hb).exists
    exact hn'.trans hn
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  have hf := frequently_lt_of_liminf_lt hco hb
  exact (hQ.mem_dom_of_tendsto_of_energy_frequently_le ht (hf.mono fun _ h => h.le)).choose_spec

/--
For the closure of a closable form, ambient convergence of domain elements with energies bounded by
C places the limit in the closed domain with energy at most C.
-/
theorem IsClosable.closure_mem_dom_of_tendsto_of_energy_le (hQ : Q.IsClosable)
    {x : ℕ → Q.closureDom} {u : H} {C : ℝ}
    (ht : Tendsto (fun n => (x n : H)) atTop (𝓝 u))
    (hb : ∀ n, (Q.closure hQ).E (x n) (x n) ≤ C) :
    ∃ hu : u ∈ Q.closureDom, (Q.closure hQ).E ⟨u, hu⟩ ⟨u, hu⟩ ≤ C :=
  (Q.closure_isClosed hQ).mem_dom_of_tendsto_of_energy_le ht hb

end ErrorCalculus.QuadForm
