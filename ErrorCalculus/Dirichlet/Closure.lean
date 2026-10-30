import ErrorCalculus.Dirichlet.QuadForm

noncomputable section

open Filter Topology
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (Q : QuadForm H)

/-- a sequence approaching an ambient point. -/
def Approaches (u : ℕ → Q.dom) (v : H) : Prop :=
  Q.IsCauchy u ∧ Tendsto (fun n => (u n : H)) atTop (𝓝 v)

/-- auxiliary closed graph in the ambient space times the energy completion. -/
def closedGraph : Submodule ℝ (H × Q.EnergyHilbert) :=
  (LinearMap.range Q.graphMap).topologicalClosure

/-- graph closure is exactly simultaneous sequential approximation. -/
theorem mem_closedGraph_iff (v : H) (a : Q.EnergyHilbert) :
    (v, a) ∈ Q.closedGraph ↔ ∃ u : ℕ → Q.dom,
      Tendsto (fun n => (u n : H)) atTop (𝓝 v) ∧
      Tendsto (fun n => Q.j (u n)) atTop (𝓝 a) := by
  change (v, a) ∈ _root_.closure (LinearMap.range Q.graphMap : Set (H × Q.EnergyHilbert)) ↔ _
  rw [mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨x, hx, ht⟩
    choose u hu using hx
    have he : x = fun n => Q.graphMap (u n) := funext fun n => (hu n).symm
    subst x
    change Tendsto (fun n => ((u n : H), Q.j (u n))) atTop (𝓝 (v, a)) at ht
    exact ⟨u, continuous_fst.tendsto (v, a) |>.comp ht, continuous_snd.tendsto (v, a) |>.comp ht⟩
  · rintro ⟨u, hv, ha⟩
    exact ⟨fun n => Q.graphMap (u n), fun n => ⟨u n, rfl⟩, hv.prodMk_nhds ha⟩

/-- closability removes the vertical part of the closed graph. -/
theorem closedGraph_zero (h : Q.IsClosable) {a : Q.EnergyHilbert}
    (ha : (0, a) ∈ Q.closedGraph) : a = 0 := by
  obtain ⟨u, hu, hju⟩ := (Q.mem_closedGraph_iff 0 a).mp ha
  have hz := (Q.energy_tendsto_zero_iff).mp (h u ⟨hu.cauchySeq, hju.cauchySeq⟩ hu)
  exact tendsto_nhds_unique hju hz

/-- The energy limit is independent of the approximating sequence. -/
theorem closedGraph_unique (h : Q.IsClosable) {v : H} {a b : Q.EnergyHilbert}
    (ha : (v, a) ∈ Q.closedGraph) (hb : (v, b) ∈ Q.closedGraph) : a = b := by
  apply sub_eq_zero.mp
  apply Q.closedGraph_zero h
  simpa using Q.closedGraph.sub_mem ha hb

/-- The closure domain, as the first projection of the closed graph. -/
def closureDom : Submodule ℝ H := Q.closedGraph.map (LinearMap.fst ℝ H Q.EnergyHilbert)

/-- The closure domain agrees with the domain specified in B. -/
theorem mem_closureDom_iff (v : H) : v ∈ Q.closureDom ↔ ∃ u, Q.Approaches u v := by
  constructor
  · rintro ⟨⟨w, a⟩, hw, rfl⟩
    obtain ⟨u, hu, ha⟩ := (Q.mem_closedGraph_iff w a).mp hw
    exact ⟨u, ⟨hu.cauchySeq, ha.cauchySeq⟩, hu⟩
  · rintro ⟨u, hu, hv⟩
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hu.2
    exact ⟨(v, a), (Q.mem_closedGraph_iff v a).mpr ⟨u, hv, ha⟩, rfl⟩

/-- Every original domain element belongs to the closure domain. -/
theorem le_closureDom : Q.dom ≤ Q.closureDom := by
  intro v hv
  apply (Q.mem_closureDom_iff v).mpr
  exact ⟨fun _ => ⟨v, hv⟩, ⟨cauchySeq_const _, cauchySeq_const _⟩, tendsto_const_nhds⟩

/-- existence of an energy coordinate over the closure domain. -/
theorem exists_closureValue (v : Q.closureDom) : ∃ a, ((v : H), a) ∈ Q.closedGraph := by
  obtain ⟨⟨w, a⟩, ha, he⟩ := v.property
  change w = (v : H) at he
  exact ⟨a, he ▸ ha⟩

/-- a chosen energy coordinate above a closure-domain point. -/
def closureValue (v : Q.closureDom) : Q.EnergyHilbert :=
  Classical.choose (Q.exists_closureValue v)

/-- The chosen point lies in the closed graph. -/
theorem closureValue_mem (v : Q.closureDom) : ((v : H), Q.closureValue v) ∈ Q.closedGraph :=
  Classical.choose_spec (Q.exists_closureValue v)

/-- independence makes the chosen coordinate a linear map. -/
def closureLift (h : Q.IsClosable) : Q.closureDom →ₗ[ℝ] Q.EnergyHilbert where
  toFun := Q.closureValue
  map_add' v w := Q.closedGraph_unique h (Q.closureValue_mem (v + w))
    (Q.closedGraph.add_mem (Q.closureValue_mem v) (Q.closureValue_mem w))
  map_smul' c v := Q.closedGraph_unique h (Q.closureValue_mem (c • v))
    (Q.closedGraph.smul_mem c (Q.closureValue_mem v))

/-- form obtained by pulling back a Hilbert inner product. -/
def ofEnergyMap {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (D : Submodule ℝ H) (f : D →ₗ[ℝ] K) : QuadForm H where
  dom := D
  E :=
    { toFun := fun u =>
        { toFun := fun v => inner ℝ (f u) (f v)
          map_add' := by intro v w; simp [inner_add_right]
          map_smul' := by intro c v; simp [inner_smul_right] }
      map_add' := by intro u v; ext w; simp [inner_add_left]
      map_smul' := by intro c u; ext w; simp [real_inner_smul_left] }
  symm u v := real_inner_comm _ _
  nonneg u := real_inner_self_nonneg

/-- closure, represented on its domain without meaningless off-domain values. -/
def closure (h : Q.IsClosable) : QuadForm H := ofEnergyMap Q.closureDom (Q.closureLift h)

/-- The closure energy is the inner product of the canonical energy limits. -/
theorem closure_energy (h : Q.IsClosable) (v w : Q.closureDom) :
    (Q.closure h).E v w = inner ℝ (Q.closureLift h v) (Q.closureLift h w) := rfl

/-- Every approaching sequence has the chosen energy limit. -/
theorem approaches_tendsto_lift (h : Q.IsClosable) {u : ℕ → Q.dom} {v : H}
    (hu : Q.Approaches u v) (hv : v ∈ Q.closureDom) :
    Tendsto (fun n => Q.j (u n)) atTop (𝓝 (Q.closureLift h ⟨v, hv⟩)) := by
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hu.1.2
  have he := Q.closedGraph_unique h
    ((Q.mem_closedGraph_iff v a).mpr ⟨u, hu.2, ha⟩) (Q.closureValue_mem ⟨v, hv⟩)
  rw [he] at ha
  exact ha

/-- characterization by arbitrary pairs of approximating sequences. -/
theorem closure_characterization (h : Q.IsClosable) {u w : ℕ → Q.dom} {v z : H}
    (hu : Q.Approaches u v) (hw : Q.Approaches w z)
    (hv : v ∈ Q.closureDom) (hz : z ∈ Q.closureDom) :
    Tendsto (fun n => Q.E (u n) (w n)) atTop
      (𝓝 ((Q.closure h).E ⟨v, hv⟩ ⟨z, hz⟩)) := by
  change Tendsto _ atTop (𝓝 (inner ℝ (Q.closureLift h ⟨v, hv⟩) (Q.closureLift h ⟨z, hz⟩)))
  simpa only [Q.inner_j] using
    (Q.approaches_tendsto_lift h hu hv).inner (𝕜 := ℝ) (Q.approaches_tendsto_lift h hw hz)

/-- agreement with the requested scalar `limUnder` construction. -/
theorem closure_eq_limUnder (h : Q.IsClosable) {u w : ℕ → Q.dom} {v z : H}
    (hu : Q.Approaches u v) (hw : Q.Approaches w z)
    (hv : v ∈ Q.closureDom) (hz : z ∈ Q.closureDom) :
    (Q.closure h).E ⟨v, hv⟩ ⟨z, hz⟩ = limUnder atTop (fun n => Q.E (u n) (w n)) :=
  (Q.closure_characterization h hu hw hv hz).limUnder_eq.symm

/-- scalar independence, for both pairs of approximants. -/
theorem closure_independent (h : Q.IsClosable) {u u' w w' : ℕ → Q.dom} {v z : H}
    (hu : Q.Approaches u v) (hu' : Q.Approaches u' v)
    (hw : Q.Approaches w z) (hw' : Q.Approaches w' z) :
    limUnder atTop (fun n => Q.E (u n) (w n)) =
      limUnder atTop (fun n => Q.E (u' n) (w' n)) := by
  have hv := (Q.mem_closureDom_iff v).mpr ⟨u, hu⟩
  have hz := (Q.mem_closureDom_iff z).mpr ⟨w, hw⟩
  rw [← Q.closure_eq_limUnder h hu hw hv hz, ← Q.closure_eq_limUnder h hu' hw' hv hz]

/-- canonical domain inclusion. -/
def inclusion : Q.dom →ₗ[ℝ] Q.closureDom := Submodule.inclusion Q.le_closureDom

@[simp] theorem closureLift_inclusion (h : Q.IsClosable) (u : Q.dom) :
    Q.closureLift h (Q.inclusion u) = Q.j u := by
  apply Q.closedGraph_unique h (Q.closureValue_mem _)
  exact (LinearMap.range Q.graphMap).le_topologicalClosure ⟨u, rfl⟩

/-- approximation in the closure energy. -/
theorem closure_approx (h : Q.IsClosable) {u : ℕ → Q.dom} {v : H}
    (hu : Q.Approaches u v) (hv : v ∈ Q.closureDom) :
    Tendsto (fun n => (Q.closure h).E (Q.inclusion (u n) - (⟨v, hv⟩ : Q.closureDom))
      (Q.inclusion (u n) - (⟨v, hv⟩ : Q.closureDom))) atTop (𝓝 0) := by
  have ht := (Q.approaches_tendsto_lift h hu hv).sub_const (Q.closureLift h ⟨v, hv⟩)
  simp only [sub_self] at ht
  have ht' := ht.inner (𝕜 := ℝ) ht
  rw [inner_zero_left] at ht'
  apply ht'.congr'
  filter_upwards [] with n
  change inner ℝ (Q.j (u n) - Q.closureLift h ⟨v, hv⟩)
    (Q.j (u n) - Q.closureLift h ⟨v, hv⟩) =
    inner ℝ (Q.closureLift h (Q.inclusion (u n) - ⟨v, hv⟩))
      (Q.closureLift h (Q.inclusion (u n) - ⟨v, hv⟩))
  rw [map_sub, Q.closureLift_inclusion h (u n)]

/-- The closure seminorm is the norm of its energy coordinate. -/
theorem closure_seminorm (h : Q.IsClosable) (v : Q.closureDom) :
    (Q.closure h).seminorm v = ‖Q.closureLift h v‖ :=
  by
    change Real.sqrt (inner ℝ (Q.closureLift h v) (Q.closureLift h v)) = _
    exact (norm_eq_sqrt_real_inner (Q.closureLift h v)).symm

/-- closed-graph completeness identifies every form-Cauchy ambient limit. -/
theorem closure_complete_limit (h : Q.IsClosable) (u : ℕ → Q.closureDom)
    (hu : (Q.closure h).IsCauchy u) (v : H)
    (hv : Tendsto (fun n => (u n : H)) atTop (𝓝 v)) :
    ∃ hd : v ∈ Q.closureDom,
      Tendsto (fun n => (Q.closure h).E (u n - (⟨v, hd⟩ : Q.closureDom))
        (u n - (⟨v, hd⟩ : Q.closureDom))) atTop (𝓝 0) := by
  have hc : CauchySeq (fun n => Q.closureLift h (u n)) := by
    rw [Metric.cauchySeq_iff]
    have hc := ((Q.closure h).isCauchy_iff u).mp hu |>.2
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have he := hN m hm n hn
    rw [Q.closure_seminorm] at he
    change ‖Q.closureLift h ((u m : Q.closureDom) - (u n : Q.closureDom))‖ < ε at he
    rw [map_sub] at he
    simpa only [dist_eq_norm] using he
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  have hg : (v, a) ∈ Q.closedGraph :=
    (LinearMap.range Q.graphMap).isClosed_topologicalClosure.mem_of_tendsto
      (hv.prodMk_nhds ha) (Eventually.of_forall fun n => Q.closureValue_mem (u n))
  have hd : v ∈ Q.closureDom := ⟨(v, a), hg, rfl⟩
  have he := Q.closedGraph_unique h hg (Q.closureValue_mem ⟨v, hd⟩)
  have ha' : Tendsto (fun n => Q.closureLift h (u n)) atTop (𝓝 (Q.closureLift h ⟨v, hd⟩)) := by
    rw [he] at ha
    exact ha
  have ht := ha'.sub_const (Q.closureLift h ⟨v, hd⟩)
  simp only [sub_self] at ht
  have ht' := ht.inner (𝕜 := ℝ) ht
  rw [inner_zero_left] at ht'
  refine ⟨hd, ht'.congr' ?_⟩
  filter_upwards [] with n
  change inner ℝ (Q.closureLift h (u n) - Q.closureLift h ⟨v, hd⟩)
    (Q.closureLift h (u n) - Q.closureLift h ⟨v, hd⟩) =
    inner ℝ (Q.closureLift h (u n - ⟨v, hd⟩)) (Q.closureLift h (u n - ⟨v, hd⟩))
  rw [map_sub]

/-- The closure is closed. -/
theorem closure_isClosed (h : Q.IsClosable) : (Q.closure h).IsClosed := by
  intro u hu v hv
  exact Q.closure_complete_limit h u hu v hv

end ErrorCalculus.QuadForm
