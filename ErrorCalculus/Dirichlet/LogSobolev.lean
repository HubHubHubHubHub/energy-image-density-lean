import ErrorCalculus.Dirichlet.EntropyLimit
import ErrorCalculus.Dirichlet.ClosureStructure
import ErrorCalculus.Dirichlet.TransportStructure
import ErrorCalculus.Dirichlet.ImageStructure

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Logarithmic Sobolev inequality, including finiteness, in the normalization E = ½∫Γ. -/
def ErrorStructure.HasLogSobolev (S : ErrorStructure Ω μ) (c : ℝ) : Prop :=
  ∀ u : S.dom,
    Integrable (fun x => ((u : Lp ℝ 2 μ) x)^2 * Real.log (((u : Lp ℝ 2 μ) x)^2)) μ ∧
      entropy μ (fun x => ((u : Lp ℝ 2 μ) x)^2) ≤ c * S.energy.E u u

theorem ErrorStructure.HasLogSobolev.mono {S : ErrorStructure Ω μ} {c c' : ℝ}
    (h : S.HasLogSobolev c) (hc : c ≤ c') : S.HasLogSobolev c' := by
  intro u
  exact ⟨(h u).1, (h u).2.trans (mul_le_mul_of_nonneg_right hc (S.energy.nonneg u))⟩

/-- Sequential form density: L² convergence and convergence of the diagonal energies.
No algebraic or topological structure on the approximating set is required. -/
theorem hasLogSobolev_of_dense {S : ErrorStructure Ω μ} {c : ℝ} (D : Set S.dom)
    (hd : ∀ u : S.dom, ∃ v : ℕ → S.dom, (∀ n, v n ∈ D) ∧
      Tendsto (fun n => (v n : Lp ℝ 2 μ)) atTop (𝓝 (u : Lp ℝ 2 μ)) ∧
      Tendsto (fun n => S.energy.E (v n) (v n)) atTop (𝓝 (S.energy.E u u)))
    (hb : ∀ u ∈ D,
      Integrable (fun x => ((u : Lp ℝ 2 μ) x)^2 * Real.log (((u : Lp ℝ 2 μ) x)^2)) μ ∧
        entropy μ (fun x => ((u : Lp ℝ 2 μ) x)^2) ≤ c * S.energy.E u u) :
    S.HasLogSobolev c := by
  intro u
  obtain ⟨v, hv, ht, he⟩ := hd u
  exact entropy_le_of_tendsto_L2 ht (fun n => (hb (v n) (hv n)).1)
    (fun n => (hb (v n) (hv n)).2) (he.const_mul c)

/--
A closable proto-structure transfers its logarithmic Sobolev inequality to its closure, using
convergence of the approximating energies.
-/
theorem ProtoErrorStructure.closure_hasLogSobolev (P : ProtoErrorStructure Ω μ)
    (hc : P.energy.IsClosable) {c : ℝ}
    (hb : ∀ u : P.dom,
      Integrable (fun x => ((u : Lp ℝ 2 μ) x)^2 * Real.log (((u : Lp ℝ 2 μ) x)^2)) μ ∧
        entropy μ (fun x => ((u : Lp ℝ 2 μ) x)^2) ≤ c * P.energy.E u u) :
    (P.closure hc).HasLogSobolev c := by
  intro u
  obtain ⟨v, hv⟩ := (P.energy.mem_closureDom_iff u).mp u.property
  apply entropy_le_of_tendsto_L2 hv.2 (fun n => (hb (v n)).1) (fun n => (hb (v n)).2)
  have he : Tendsto (fun n => P.energy.E (v n) (v n)) atTop
      (𝓝 ((P.closure hc).energy.E u u)) := by
    have heq : (P.closure hc).energy.E u u = (P.energy.closure hc).E u u :=
      P.toErrorData.closureGamma_energy hc u u
    rw [heq]
    exact P.energy.closure_characterization hc hv hv u.property u.property
  exact he.const_mul c

/-- LSI is invariant under transport by a measure isomorphism modulo null sets. -/
theorem transport_hasLogSobolev {Ω' : Type*} [MeasurableSpace Ω']
    {ν : Measure Ω'} [IsProbabilityMeasure ν] {S : ErrorStructure Ω μ}
    (e : MeasureIsoModZero μ ν) {c : ℝ} (h : S.HasLogSobolev c) :
    (S.transport e).HasLogSobolev c := by
  intro u
  let v := S.transportDomMap e u
  have hv : (v : Lp ℝ 2 μ) =ᵐ[μ] (u : Lp ℝ 2 ν) ∘ e.forward := e.coe_lp 2 u
  have hs : entropy μ (fun x => ((v : Lp ℝ 2 μ) x)^2) =
      entropy ν (fun x => ((u : Lp ℝ 2 ν) x)^2) := by
    calc
      _ = entropy μ ((fun x => ((u : Lp ℝ 2 ν) x)^2) ∘ e.forward) :=
        entropy_congr_ae (hv.fun_comp (fun z => z^2))
      _ = _ := entropy_comp_measurePreserving e.forward_preserving
        ((Lp.aestronglyMeasurable (u : Lp ℝ 2 ν)).pow 2)
  have hi : Integrable ((fun x => ((u : Lp ℝ 2 ν) x)^2 *
      Real.log (((u : Lp ℝ 2 ν) x)^2)) ∘ e.forward) μ :=
    (h v).1.congr (hv.fun_comp (fun z => z^2 * Real.log (z^2)))
  refine ⟨(e.forward_preserving.integrable_comp
    (Real.continuous_mul_log.comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable (u : Lp ℝ 2 ν)).pow 2))).mp hi, ?_⟩
  rw [S.transport_energy e u u, ← hs]
  exact (h v).2

/-- LSI passes to an image error structure; the image API gives equality of energies. -/
theorem image_hasLogSobolev {S : ErrorStructure Ω μ} {m : ℕ}
    (X : Fin m → Lp ℝ 2 μ) (hX : ∀ i, X i ∈ S.dom) {c : ℝ}
    (h : S.HasLogSobolev c) : (S.image X hX).HasLogSobolev c := by
  intro u
  let v := S.toErrorData.imageLift X u
  have hv : (v : Lp ℝ 2 μ) =ᵐ[μ]
      (u : Lp ℝ 2 (imageLaw X)) ∘ imageRepresentative X := pullback_ae_eq X u
  have hs : entropy μ (fun x => ((v : Lp ℝ 2 μ) x)^2) =
      entropy (imageLaw X) (fun x => ((u : Lp ℝ 2 (imageLaw X)) x)^2) := by
    calc
      _ = entropy μ ((fun x => ((u : Lp ℝ 2 (imageLaw X)) x)^2) ∘
          imageRepresentative X) := entropy_congr_ae (hv.fun_comp (fun z => z^2))
      _ = _ := entropy_comp_measurePreserving (imageRepresentative_preserving X)
        ((Lp.aestronglyMeasurable (u : Lp ℝ 2 (imageLaw X))).pow 2)
  have hi : Integrable ((fun x => ((u : Lp ℝ 2 (imageLaw X)) x)^2 *
      Real.log (((u : Lp ℝ 2 (imageLaw X)) x)^2)) ∘ imageRepresentative X) μ :=
    (h v).1.congr (hv.fun_comp (fun z => z^2 * Real.log (z^2)))
  refine ⟨((imageRepresentative_preserving X).integrable_comp
    (Real.continuous_mul_log.comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable (u : Lp ℝ 2 (imageLaw X))).pow 2))).mp hi, ?_⟩
  rw [S.image_energy X hX u u, ← hs]
  exact (h v).2

end ErrorCalculus
