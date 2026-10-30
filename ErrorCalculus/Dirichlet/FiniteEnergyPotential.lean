import ErrorCalculus.Dirichlet.FiniteEnergyDual
import ErrorCalculus.Dirichlet.CapacityVariational
import Mathlib.Tactic

/-!
# potentials, positivity, equilibrium distribution, capacity duality (Fukushima 1980, § 3.2–3.3; BH
1991, ch. I § 9.1)

## Main results
Potential U₁T of a finite-energy distribution by Riesz representation (Fukushima (3.2.2), p. 69, α =
1); positivity of the potential of a positive distribution (Fukushima th. 3.2.1 (iv) ⇒ u ≥ 0, p. 69,
here using BH Lemma 8.1.2.1, p. 52); equilibrium distribution T_G = (e_G, ·)_𝔻 with potential e_G,
positive, "supported on G" in the weak sense, with (3.3.3)–(3.3.4) (Fukushima § 3.3, p. 75) and
‖T_G‖² = c(G) ((3.2.9), p. 71); dual capacity formula (a Hilbert-space variant not transcribed from
the text). The measure ν_G representing T_G (BH proposition 9.2.1, Daniell) is not constructed in
this module. Depends only on capacity and `CapacityVariational`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity
namespace DirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (D : DirichletForm μ)

/-! ## B. Potentials, positivity, equilibrium distribution (Fukushima § 3.2–3.3) -/

section Potentials

/--
Fukushima 1980, § 3.2, (3.2.2) (p. 69), α = 1, and BH 1991, ch. I § 9.1, proposition 9.1.3 a) (p.
62): the potential U₁T of a finite-energy distribution (Riesz representation).

The potential of T ∈ 𝔻': the unique u ∈ 𝔻 such that (u, v)_𝔻 = ⟨v, T⟩ for every v ∈ 𝔻.
-/
def potential (T : D.Dual) : D.Space := (InnerProductSpace.toDual ℝ D.Space).symm T

/-- The potential of T pairs with every form element v to give T(v). -/
theorem inner_potential (T : D.Dual) (v : D.Space) : ⟪D.potential T, v⟫_ℝ = T v :=
  InnerProductSpace.toDual_symm_apply

/-- The form norm of a potential equals the dual norm of its functional. -/
theorem norm_potential (T : D.Dual) : ‖D.potential T‖ = ‖T‖ :=
  LinearIsometryEquiv.norm_map _ _

/--
Fukushima 1980, § 3.2, (3.2.2) (p. 69): uniqueness of the potential.

If (u, v)_𝔻 = ⟨v, T⟩ for every v, then u is the potential of T.
-/
theorem eq_potential {T : D.Dual} {u : D.Space} (h : ∀ v, ⟪u, v⟫_ℝ = T v) : u = D.potential T :=
  ext_inner_right ℝ fun v => by rw [h, inner_potential]

/-- Taking the potential of the Riesz functional associated with u recovers u. -/
theorem potential_toDual (u : D.Space) :
    D.potential (InnerProductSpace.toDual ℝ D.Space u) = u :=
  (InnerProductSpace.toDual ℝ D.Space).symm_apply_apply u

/-- u = u ∨ 0 + u ∧ 0 in 𝔻. -/
theorem supS_add_infS_zero (u : D.Space) : D.supS u 0 + D.infS u 0 = u := by
  apply D.toLp_injective
  rw [map_add, D.toLp_supS, D.toLp_infS, map_zero, add_comm, inf_add_sup, add_zero]

/--
Fukushima 1980, § 3.2, Theorem 3.2.1, (iv) ⇒ u ≥ 0 (proof, p. 69); argument using BH Lemma 8.1.2.1
(p. 52) in place of minimization on 𝓛_u.

If ℰ₁(u, v) ≥ 0 for every v ∈ 𝔻⁺, then u ∈ 𝔻⁺.
-/
theorem mem_posCone_of_inner_nonneg {u : D.Space} (hu : ∀ v ∈ D.posCone, 0 ≤ ⟪u, v⟫_ℝ) :
    u ∈ D.posCone := by
  set s := D.supS u 0 with hs
  set i := D.infS u 0 with hi
  have hsi : s + i = u := D.supS_add_infS_zero u
  have hl : ‖s‖ ^ 2 + ‖i‖ ^ 2 ≤ ‖u‖ ^ 2 + ‖(0 : D.Space)‖ ^ 2 := D.bh_8_1_2_1 u 0
  have hneg : -i ∈ D.posCone := by
    show 0 ≤ D.toLp (-i)
    rw [map_neg, hi, D.toLp_infS, map_zero, neg_nonneg]
    exact inf_le_right
  have h1 := hu _ hneg
  have hu2 : ‖u‖ ^ 2 = ‖s‖ ^ 2 + 2 * ⟪s, i⟫_ℝ + ‖i‖ ^ 2 := by
    rw [← hsi]
    exact norm_add_sq_real s i
  have hui : ⟪u, -i⟫_ℝ = -(⟪s, i⟫_ℝ + ‖i‖ ^ 2) := by
    rw [inner_neg_right, ← hsi, inner_add_left, real_inner_self_eq_norm_sq]
  rw [hui] at h1
  rw [norm_zero] at hl
  have hi2 : ‖i‖ ^ 2 ≤ 0 := by nlinarith
  have hi0 : i = 0 := norm_eq_zero.1 (by nlinarith [norm_nonneg i])
  have hinf : D.toLp u ⊓ 0 = 0 := by
    have h := congrArg D.toLp hi0
    rw [hi, D.toLp_infS, map_zero] at h
    exact h
  exact inf_eq_right.1 hinf

/--
Fukushima 1980, § 3.2, Theorem 3.2.1, (i) ⇔ (iv) and (iv) ⇒ u ≥ 0 (p. 69), in Hilbert-space form:
the potential of a positive distribution is nonnegative.

The potential of T ∈ 𝔻'⁺ belongs to 𝔻⁺.
-/
theorem potential_mem_posCone {T : D.Dual} (hT : T ∈ D.dualPos) : D.potential T ∈ D.posCone :=
  D.mem_posCone_of_inner_nonneg fun v hv => by rw [inner_potential]; exact hT v hv

/--
The Riesz functional of u is positive exactly when u pairs nonnegatively with the positive cone.
-/
theorem toDual_mem_dualPos_iff (u : D.Space) :
    InnerProductSpace.toDual ℝ D.Space u ∈ D.dualPos ↔ ∀ v ∈ D.posCone, 0 ≤ ⟪u, v⟫_ℝ := by
  simp only [dualPos, Set.mem_setOf_eq, InnerProductSpace.toDual_apply_apply]

/--
Fukushima 1980, § 3.3, (3.3.3) and the equilibrium measure ν_B (p. 75), at the distribution level:
the equilibrium distribution of G.

The equilibrium distribution of G: T_G = (e_G, ·)_𝔻, with potential e_G.
-/
def eqDist (G : Set Ω) : D.Dual := InnerProductSpace.toDual ℝ D.Space (D.equilibrium G)

/--
The equilibrium distribution evaluates by the form-space inner product with the equilibrium
potential.
-/
theorem eqDist_apply (G : Set Ω) (v : D.Space) : D.eqDist G v = ⟪D.equilibrium G, v⟫_ℝ :=
  InnerProductSpace.toDual_apply_apply

/--
Fukushima 1980, § 3.3 (p. 75): "the equilibrium potential e_B is a 1-potential of … ν_B", at the
distribution level.

The equilibrium potential is the potential of the equilibrium distribution.
-/
theorem potential_eqDist (G : Set Ω) : D.potential (D.eqDist G) = D.equilibrium G :=
  D.potential_toDual _

/--
Fukushima 1980, § 3.3, (3.3.3) (p. 75) and Lemma 3.1.1 (iii) (p. 62): T_G is positive on v ≥ 0 a.e.
on G ("supported on G" in the weak sense).

If v ≥ 0 μ-a.e. on G, then ⟨v, T_G⟩ ≥ 0.
-/
theorem eqDist_nonneg_of_nonneg_on {G : Set Ω} (hne : (D.adm G).Nonempty) {v : D.Space}
    (hv : ∀ᵐ ω ∂μ, ω ∈ G → 0 ≤ D.toLp v ω) : 0 ≤ D.eqDist G v := by
  rw [eqDist_apply]
  exact D.inner_equilibrium_nonneg hne hv

/--
Fukushima 1980, § 3.3 (p. 75): T_G ∈ 𝔻'⁺.

The equilibrium distribution is positive.
-/
theorem eqDist_mem_dualPos {G : Set Ω} (hne : (D.adm G).Nonempty) : D.eqDist G ∈ D.dualPos := by
  intro v hv
  refine D.eqDist_nonneg_of_nonneg_on hne ?_
  filter_upwards [(D.mem_posCone_iff).1 hv] with ω h _
  exact h

/--
Fukushima 1980, § 3.3 (p. 75): "ν_B supported by B̄", at the distribution level and in the weak
sense: T_G vanishes on v that are zero a.e. on G.

If v = 0 μ-a.e. on G, then ⟨v, T_G⟩ = 0.
-/
theorem eqDist_eq_zero_of_eq_zero_on {G : Set Ω} (hne : (D.adm G).Nonempty) {v : D.Space}
    (hv : ∀ᵐ ω ∂μ, ω ∈ G → D.toLp v ω = 0) : D.eqDist G v = 0 := by
  have a := D.eqDist_nonneg_of_nonneg_on hne (v := v) (hv.mono fun ω h hω => (h hω).symm.le)
  have hneg : ∀ᵐ ω ∂μ, ω ∈ G → 0 ≤ D.toLp (-v) ω := by
    rw [map_neg]
    filter_upwards [hv, Lp.coeFn_neg (D.toLp v)] with ω h1 h2 hω
    rw [h2, Pi.neg_apply, h1 hω, neg_zero]
  have b := D.eqDist_nonneg_of_nonneg_on hne hneg
  rw [map_neg] at b
  linarith

/--
Fukushima 1980, § 3.3, (3.3.4) (p. 75): ν_A(Ā) = Cap(A), by Lemma 3.1.1 (iv); here for every G and
every v = 1 a.e. on G.

If v = 1 μ-a.e. on G, then ⟨v, T_G⟩ = c(G) (a.e. capacity).
-/
theorem eqDist_apply_of_eq_one_on {G : Set Ω} (hne : (D.adm G).Nonempty) {v : D.Space}
    (hv : ∀ᵐ ω ∂μ, ω ∈ G → D.toLp v ω = 1) : ENNReal.ofReal (D.eqDist G v) = D.capAE G := by
  rw [eqDist_apply, D.inner_equilibrium_eq hne hv, D.capAE_eq_equilibrium hne]

/--
Fukushima 1980, § 3.2, (3.2.9) (p. 71): energy of the equilibrium distribution = capacity (BH 8.1.2
a)).

‖T_G‖²_{𝔻'} = c(G).
-/
theorem norm_eqDist_sq {G : Set Ω} (hne : (D.adm G).Nonempty) :
    ENNReal.ofReal (‖D.eqDist G‖ ^ 2) = D.capAE G := by
  rw [eqDist, LinearIsometryEquiv.norm_map, D.capAE_eq_equilibrium hne]

/-- Positivity of T "on G" (on v ≥ 0 a.e. on G). -/
def IsPosOn (G : Set Ω) (T : D.Dual) : Prop :=
  ∀ v : D.Space, (∀ᵐ ω ∂μ, ω ∈ G → 0 ≤ D.toLp v ω) → 0 ≤ T v

/-- A distribution positive on G attains its minimum over 𝓛_G at e_G. -/
theorem apply_equilibrium_le {G : Set Ω} (hne : (D.adm G).Nonempty) {T : D.Dual}
    (hT : D.IsPosOn G T) {u : D.Space} (hu : u ∈ D.adm G) : T (D.equilibrium G) ≤ T u := by
  have hle := (D.bh_8_1_2_a (D.capAE_ne_top_iff.2 hne)).2
  have h : ∀ᵐ ω ∂μ, ω ∈ G → 0 ≤ D.toLp (u - D.equilibrium G) ω := by
    rw [map_sub]
    filter_upwards [hu, hle, Lp.coeFn_sub (D.toLp u) (D.toLp (D.equilibrium G))]
      with ω h1 h2 h3 hω
    rw [h3, Pi.sub_apply]
    linarith [h1 hω, h2.2]
  have := hT _ h
  rw [map_sub] at this
  linarith

/--
a Hilbert-space variant (not transcribed from the text) of the dual characterization of capacity; it
relies on BH 8.1.2 a) (p. 52) and Fukushima, Lemma 3.1.1 (iii) (p. 62).

c(G)^{1/2} = ‖e_G‖ is the largest r such that there exists T ∈ 𝔻', ‖T‖ ≤ 1, positive on G, with ⟨u,
T⟩ ≥ r for every u ∈ 𝓛_G.
-/
theorem capAE_dual {G : Set Ω} (hne : (D.adm G).Nonempty) :
    IsGreatest {r : ℝ | ∃ T : D.Dual, D.IsPosOn G T ∧ ‖T‖ ≤ 1 ∧ ∀ u ∈ D.adm G, r ≤ T u}
      ‖D.equilibrium G‖ := by
  set e := D.equilibrium G with he
  have hm : e ∈ D.adm G := (D.equilibrium_spec hne).1
  constructor
  · by_cases h0 : e = 0
    · refine ⟨0, fun v _ => le_refl _, by simp, fun u _ => ?_⟩
      rw [h0, norm_zero]
      simp
    · have hpos : 0 < ‖e‖ := norm_pos_iff.2 h0
      refine ⟨‖e‖⁻¹ • D.eqDist G, fun v hv => ?_, ?_, fun u hu => ?_⟩
      · rw [smul_apply, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 hpos.le) (D.eqDist_nonneg_of_nonneg_on hne hv)
      · rw [norm_smul, eqDist, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 hpos), inv_mul_cancel₀ hpos.ne']
      · have hT : D.IsPosOn G (‖e‖⁻¹ • D.eqDist G) := fun v hv => by
          rw [smul_apply, smul_eq_mul]
          exact mul_nonneg (inv_nonneg.2 hpos.le) (D.eqDist_nonneg_of_nonneg_on hne hv)
        refine le_trans ?_ (D.apply_equilibrium_le hne hT hu)
        rw [smul_apply, smul_eq_mul, eqDist_apply, ← he,
          real_inner_self_eq_norm_sq]
        field_simp
        rfl
  · rintro r ⟨T, _, hT1, hTu⟩
    calc r ≤ T e := hTu e hm
      _ ≤ |T e| := le_abs_self _
      _ ≤ ‖T‖ * ‖e‖ := by rw [← Real.norm_eq_abs]; exact T.le_opNorm e
      _ ≤ 1 * ‖e‖ := mul_le_mul_of_nonneg_right hT1 (norm_nonneg e)
      _ = ‖e‖ := one_mul _

end Potentials

end DirichletForm
end ErrorCalculus.Capacity
