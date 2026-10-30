import ErrorCalculus.Dirichlet.Capacity
import Mathlib.Tactic

/-!
# variational characterization of the equilibrium potential (Fukushima 1980, Lemma 3.1.1 (iii)–(iv))

## Main results
For arbitrary G (openness of G is not used) with nonempty 𝓛_G: ℰ₁(e_G, v) ≥ 0 for every v ≥ 0 a.e.
on G (Lemma 3.1.1 (iii), forward direction, p. 62), ℰ₁(e_G, v) = ‖e_G‖² if v = 1 a.e. on G (iv), and
the full characterization in (iii): e_G is the unique u equal to 1 a.e. on G and satisfying the
variational condition. No topology or quasi-continuity: this module depends only on capacity.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity
namespace DirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-!
## F. Variational characterization of the equilibrium potential (Fukushima, Lemma 3.1.1)
and controls
-/

section Variational
variable (D : DirichletForm μ)

/--
Fukushima 1980, § 3.1, Lemma 3.1.1 (iii), forward direction (p. 62).

Fukushima 1980, Lemma 3.1.1 (iii), forward direction: ℰ₁(e_G, v) ≥ 0 for every v ≥ 0 a.e. on G.
-/
theorem inner_equilibrium_nonneg {G : Set Ω} (h : (D.adm G).Nonempty) {v : D.Space}
    (hv : ∀ᵐ ω ∂μ, ω ∈ G → 0 ≤ D.toLp v ω) : 0 ≤ ⟪D.equilibrium G, v⟫_ℝ := by
  obtain ⟨hm, hmin⟩ := D.equilibrium_spec h
  haveI : Nonempty (D.adm G) := h.to_subtype
  have hmem : D.equilibrium G + v ∈ D.adm G := by
    show ∀ᵐ ω ∂μ, ω ∈ G → 1 ≤ D.toLp (D.equilibrium G + v) ω
    rw [map_add]
    filter_upwards [hm, hv, Lp.coeFn_add (D.toLp (D.equilibrium G)) (D.toLp v)]
      with ω h1 h2 h3 hω
    rw [h3, Pi.add_apply]
    linarith [h1 hω, h2 hω]
  have hb : BddBelow (Set.range fun w : D.adm G => ‖(0 : D.Space) - w‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have heq : ‖(0 : D.Space) - D.equilibrium G‖ = ⨅ w : D.adm G, ‖(0 : D.Space) - w‖ := by
    refine le_antisymm (le_ciInf fun w => ?_) (ciInf_le hb ⟨_, hm⟩)
    simpa using hmin w w.2
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero (D.convex_adm G) hm).1 heq _ hmem
  rw [zero_sub, add_sub_cancel_left, inner_neg_left] at hvar
  linarith

/--
Fukushima 1980, § 3.1, Lemma 3.1.1 (iv) (p. 62).

Fukushima 1980, Lemma 3.1.1 (iv): if v = 1 a.e. on G, then ℰ₁(e_G, v) = ‖e_G‖² = c(G).
-/
theorem inner_equilibrium_eq {G : Set Ω} (h : (D.adm G).Nonempty) {v : D.Space}
    (hv : ∀ᵐ ω ∂μ, ω ∈ G → D.toLp v ω = 1) :
    ⟪D.equilibrium G, v⟫_ℝ = ‖D.equilibrium G‖ ^ 2 := by
  have hm := (D.equilibrium_spec h).1
  have hle := (D.bh_8_1_2_a (D.capAE_ne_top_iff.2 h)).2
  have hzero : ∀ᵐ ω ∂μ, ω ∈ G → D.toLp (v - D.equilibrium G) ω = 0 := by
    rw [map_sub]
    filter_upwards [hm, hv, hle, Lp.coeFn_sub (D.toLp v) (D.toLp (D.equilibrium G))]
      with ω h1 h2 h3 h4 hω
    rw [h4, Pi.sub_apply, h2 hω]
    linarith [h1 hω, h3.2]
  have hneg : ∀ᵐ ω ∂μ, ω ∈ G → D.toLp (-(v - D.equilibrium G)) ω = 0 := by
    rw [map_neg]
    filter_upwards [hzero, Lp.coeFn_neg (D.toLp (v - D.equilibrium G))] with ω h1 h2 hω
    rw [h2, Pi.neg_apply, h1 hω, neg_zero]
  have a := D.inner_equilibrium_nonneg h (v := v - D.equilibrium G)
    (hzero.mono fun ω h1 hω => (h1 hω).symm.le)
  have b := D.inner_equilibrium_nonneg h (v := -(v - D.equilibrium G))
    (hneg.mono fun ω h1 hω => (h1 hω).symm.le)
  rw [inner_neg_right] at b
  have hz : ⟪D.equilibrium G, v - D.equilibrium G⟫_ℝ = 0 := by linarith
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at hz
  linarith

/--
Fukushima 1980, § 3.1, Lemma 3.1.1 (iii), p. 62: for an arbitrary set with nonempty
admissible class, the equilibrium potential is the unique u equal to one almost everywhere on
the set and
satisfying the variational inequality against every form element nonnegative a.e. on the set.
Openness is not required.
-/
theorem eq_equilibrium_iff_variational {G : Set Ω}
    (hne : (D.adm G).Nonempty) {u : D.Space} :
    u = D.equilibrium G ↔
      (∀ᵐ ω ∂μ, ω ∈ G → D.toLp u ω = 1) ∧
      ∀ v : D.Space, (∀ᵐ ω ∂μ, ω ∈ G → 0 ≤ D.toLp v ω) →
        0 ≤ ⟪u, v⟫_ℝ := by
  constructor
  · rintro rfl
    refine ⟨?_, fun v hv => D.inner_equilibrium_nonneg hne hv⟩
    filter_upwards [(D.equilibrium_spec hne).1,
      (D.bh_8_1_2_a (D.capAE_ne_top_iff.2 hne)).2] with ω h1 h2 hω
    exact le_antisymm h2.2 (h1 hω)
  · rintro ⟨hu1, huvar⟩
    have hu : u ∈ D.adm G := hu1.mono fun ω hω hG => (hω hG).ge
    have hopt : ∀ w ∈ D.adm G, ⟪(0 : D.Space) - u, w - u⟫_ℝ ≤ 0 := by
      intro w hw
      have hnonneg : ∀ᵐ ω ∂μ, ω ∈ G → 0 ≤ D.toLp (w - u) ω := by
        rw [map_sub]
        filter_upwards [hw, hu1, Lp.coeFn_sub (D.toLp w) (D.toLp u)]
          with ω hwω huω hsub hω
        rw [hsub, Pi.sub_apply, huω hω]
        exact sub_nonneg.mpr (hwω hω)
      simpa only [zero_sub, inner_neg_left] using neg_nonpos.mpr (huvar (w - u) hnonneg)
    have heq := (norm_eq_iInf_iff_real_inner_le_zero (D.convex_adm G) hu).2 hopt
    have hb : BddBelow (Set.range fun w : D.adm G => ‖(0 : D.Space) - w‖) :=
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    have hle := ciInf_le hb ⟨D.equilibrium G, (D.equilibrium_spec hne).1⟩
    rw [← heq] at hle
    exact D.eq_equilibrium hne hu (by simpa using hle)

end Variational

end DirichletForm
end ErrorCalculus.Capacity
