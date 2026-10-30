import ErrorCalculus.Dirichlet.TransportL2

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

namespace ErrorData
variable (S : ErrorData Ω μ) (e : MeasureIsoModZero μ ν)

/-- The transported domain, before imposing the analytic axioms. -/
def transportDom : Submodule ℝ (Lp ℝ 2 ν) := S.dom.comap (e.lp 2).toLinearMap

/-- Pullback on domain elements. -/
def transportDomMap : S.transportDom e →ₗ[ℝ] S.dom :=
  LinearMap.codRestrict S.dom
    ((e.lp 2).toLinearMap.comp (S.transportDom e).subtype) (fun u => u.property)

omit [IsProbabilityMeasure ν] in
@[simp] theorem coe_transportDomMap (u : S.transportDom e) :
    (S.transportDomMap e u : Lp ℝ 2 μ) = e.lp 2 u := rfl

/-- transport the bilinear L¹ error by the inverse pullback. -/
def transport : ErrorData Ω' ν where
  dom := S.transportDom e
  Γ := LinearMap.mk₂ ℝ (fun u v => (e.lp 1).symm
    (S.Γ (S.transportDomMap e u) (S.transportDomMap e v)))
    (by intros; simp [map_add]) (by intros; simp [map_smul])
    (by intros; simp [map_add]) (by intros; simp [map_smul])
  Γ_symm u v := by
    change (e.lp 1).symm (S.Γ _ _) = (e.lp 1).symm (S.Γ _ _)
    rw [S.Γ_symm]
  Γ_nonneg u := by
    filter_upwards [e.coe_lp_symm 1 (S.Γ (S.transportDomMap e u) (S.transportDomMap e u)),
      e.backward_preserving.quasiMeasurePreserving.ae (S.Γ_nonneg (S.transportDomMap e u))]
      with y hy hp
    change 0 ≤ (e.lp 1).symm (S.Γ (S.transportDomMap e u) (S.transportDomMap e u)) y
    simpa only [hy, Function.comp_apply, Pi.zero_apply] using hp

@[simp] theorem transport_Γ (u v : (S.transport e).dom) :
    (S.transport e).Γ u v = (e.lp 1).symm
      (S.Γ (S.transportDomMap e u) (S.transportDomMap e v)) := rfl

theorem transport_energy (u v : (S.transport e).dom) :
    (S.transport e).energy.E u v =
      S.energy.E (S.transportDomMap e u) (S.transportDomMap e v) := by
  simp only [energy_apply, transport_Γ, e.integral_lp_symm]

theorem transport_isClosed (hS : S.energy.IsClosed) : (S.transport e).energy.IsClosed := by
  intro u hu v hv
  have ht := (e.lp 2).continuous.continuousAt.tendsto.comp hv
  have hc : S.energy.IsCauchy (fun n => S.transportDomMap e (u n)) := by
    rw [S.energy.isCauchy_iff]
    refine ⟨ht.cauchySeq, ?_⟩
    intro ε hε
    obtain ⟨N, hN⟩ := ((S.transport e).energy.isCauchy_iff u).mp hu |>.2 ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn
    change Real.sqrt ((S.transport e).energy.E (u m - u n) (u m - u n)) < ε at h
    rw [transport_energy] at h
    simpa only [QuadForm.seminorm, map_sub] using h
  obtain ⟨hd, he⟩ := hS _ hc (e.lp 2 v) ht
  refine ⟨hd, ?_⟩
  have hD : S.transportDomMap e ⟨v, hd⟩ = ⟨e.lp 2 v, hd⟩ := Subtype.ext rfl
  simp_rw [transport_energy]
  simpa only [map_sub, hD] using he

end ErrorData

namespace ErrorStructure
variable (S : ErrorStructure Ω μ) (e : MeasureIsoModZero μ ν)

/-- transport all five axioms through a mod-zero isomorphism. -/
def transport : ErrorStructure Ω' ν where
  toErrorData := S.toErrorData.transport e
  dense := S.dense.preimage (e.lp 2).toHomeomorph.isOpenMap
  «calc» m hm u F L hC hL w hw := by
    let D := S.toErrorData.transportDomMap e
    have hw' : ⇑(e.lp 2 w) =ᵐ[μ]
        fun x => F (fun i => (D (u i) : Lp ℝ 2 μ) x) := by
      filter_upwards [e.coe_lp 2 w, e.forward_preserving.quasiMeasurePreserving.ae hw,
        ae_all_iff.mpr (fun i => e.coe_lp 2 (u i))] with x hx hf hu
      exact hx.trans (hf.trans (congrArg F (funext fun i => (hu i).symm)))
    obtain ⟨hd, hg⟩ := S.calc m hm (fun i => D (u i)) F L hC hL (e.lp 2 w) hw'
    refine ⟨hd, fun v => ?_⟩
    have hg' := e.backward_preserving.quasiMeasurePreserving.ae (hg (D v))
    filter_upwards [hg',
      e.coe_lp_symm 1 (S.Γ ⟨e.lp 2 w, hd⟩ (D v)),
      ae_all_iff.mpr (fun i => e.coe_lp_symm 1 (S.Γ (D (u i)) (D v))),
      ae_all_iff.mpr (fun i => e.coe_lp_at_backward 2 (u i))] with y hg hy hi hu
    change ((e.lp 1).symm (S.Γ ⟨e.lp 2 w, hd⟩ (D v))) y = _
    rw [hy, Function.comp_apply, hg]
    have he : (fun j => (D (u j) : Lp ℝ 2 μ) (e.backward y)) =
        (fun j => (u j : Lp ℝ 2 ν) y) := funext hu
    rw [he]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z => fderiv ℝ F (fun j => (u j : Lp ℝ 2 ν) y)
      (Pi.single i 1) * z) (hi i).symm
  energy_closed := S.toErrorData.transport_isClosed e S.energy_closed
  one_mem := by
    change e.lp 2 (Lp.const 2 ν 1) ∈ S.dom
    simpa using S.one_mem

@[simp] theorem mem_transport_dom_iff (f : Lp ℝ 2 ν) :
    f ∈ (S.transport e).dom ↔ e.lp 2 f ∈ S.dom := Iff.rfl

/-- Pullback on the closed domains. -/
abbrev transportDomMap : (S.transport e).dom →ₗ[ℝ] S.dom :=
  S.toErrorData.transportDomMap e

/-- The transported error pulled back to the source. -/
theorem transport_Γ (u v : (S.transport e).dom) :
    e.lp 1 ((S.transport e).Γ u v) = S.Γ (S.transportDomMap e u) (S.transportDomMap e v) :=
  (e.lp 1).apply_symm_apply _

theorem transport_Γ_ae (u v : (S.transport e).dom) :
    ⇑((S.transport e).Γ u v) =ᵐ[ν]
      fun y => S.Γ (S.transportDomMap e u) (S.transportDomMap e v) (e.backward y) :=
  e.coe_lp_symm 1 _

theorem transport_energy (u v : (S.transport e).dom) :
    (S.transport e).energy.E u v =
      S.energy.E (S.transportDomMap e u) (S.transportDomMap e v) :=
  S.toErrorData.transport_energy e u v

end ErrorStructure
end ErrorCalculus
