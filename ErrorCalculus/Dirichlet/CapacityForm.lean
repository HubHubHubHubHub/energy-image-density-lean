import ErrorCalculus.Dirichlet.FormSpace
import ErrorCalculus.Dirichlet.LatticeGamma
import Mathlib.Tactic

/-!
# Dirichlet forms on L²(μ), normal contractions, lattices

## Main results
Sufficient framework for BH 1991, ch. I § 8 (p. 52): a closed form on L²(μ), for arbitrary μ, on
which normal contractions operate (a structure field; BH derives them from prop. 3.3.1, p. 14; no
equivalence with the Markov property alone is claimed). 𝔻 = `QuadForm.FormSpace`, with norm ‖u‖²_𝔻 =
‖u‖²_{L²} + ℰ(u) (BH 1.1.1, p. 1); |u|, u ∨ v, u ∧ v in 𝔻; BH Lemma 8.1.2.1 (pp. 52–53); the unit
contraction t ↦ (0 ∨ t) ∧ 1. Uses of the API (`Space`, `toLp`, `norm_sq_eq`, `norm_toLp_le`, …) are
adaptations, not new results.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity

/-! ## B. Dirichlet forms on L²(μ): framework, normal contractions, lattices -/

variable {Ω : Type*} [MeasurableSpace Ω]

/--
framework of BH 1991, ch. I § 8 (p. 52): 𝔻 with norm ‖u‖²_𝔻 = ‖u‖²_{L²} + ℰ(u) (BH 1.1.1, p. 1);
normal contractions taken as a field (BH derives them from prop. 3.3.1, p. 14). No equivalence with
the Markov property alone is claimed.

Sufficient framework for BH I.8: a closed form on L²(μ), with normal contractions. The domain need
not be dense and μ is arbitrary: this framework is broader than BH I.1/I.3. The contraction property
is supplied as data; its equivalence with the Markov property alone is not proved here.
-/
structure DirichletForm (μ : Measure Ω) where
  form : QuadForm (Lp ℝ 2 μ)
  closed : form.IsClosed
  contraction : ∀ {F : ℝ → ℝ}, LipschitzWith 1 F → F 0 = 0 → ∀ (u : form.dom) (w : Lp ℝ 2 μ),
    (⇑w =ᵐ[μ] fun ω => F ((u : Lp ℝ 2 μ) ω)) →
      ∃ hw : w ∈ form.dom, form.E ⟨w, hw⟩ ⟨w, hw⟩ ≤ form.E u u

namespace DirichletForm
variable {μ : Measure Ω} (D : DirichletForm μ)

/-- The space 𝔻 with norm ‖u‖²_𝔻 = ‖u‖²_{L²} + ℰ(u) (BH 1.1.1). -/
abbrev Space : Type _ := D.form.FormSpace

/-- The space of a closed Dirichlet form is complete in its form norm. -/
instance completeSpace_space : CompleteSpace D.Space :=
  QuadForm.IsClosed.completeSpace_formSpace D.form D.closed

/-- The continuous embedding 𝔻 → L²(μ). -/
def toLp : D.Space →L[ℝ] Lp ℝ 2 μ := D.form.formInclusion

/-- The canonical map to L² is the form-space equivalence followed by domain inclusion. -/
theorem toLp_apply (x : D.Space) : D.toLp x = (D.form.formToDomain x : Lp ℝ 2 μ) := rfl

/-- The squared form norm is the sum of the squared L² norm and the energy. -/
theorem norm_sq_eq (x : D.Space) : ‖x‖ ^ 2 = ‖D.toLp x‖ ^ 2 +
    D.form.E (D.form.formToDomain x) (D.form.formToDomain x) :=
  D.form.formSpace_norm_sq x

/-- Adaptation of `QuadForm.formInclusion_norm_le` to the bundled framework. -/
theorem norm_toLp_le (x : D.Space) : ‖D.toLp x‖ ≤ ‖x‖ := by
  exact (D.form.formInclusion.le_opNorm x).trans (by
    simpa using mul_le_mul_of_nonneg_right D.form.formInclusion_norm_le (norm_nonneg x))

section Contraction
variable {F : ℝ → ℝ}

/-- A 1-Lipschitz real function vanishing at zero sends a form-domain representative into L². -/
theorem contract_memLp (hF : LipschitzWith 1 F) (h0 : F 0 = 0) (x : D.Space) :
    MemLp (fun ω => F (D.toLp x ω)) 2 μ :=
  hF.comp_memLp h0 (Lp.memLp (D.toLp x))

/-- The class of F ∘ u in L². -/
def contractLp (hF : LipschitzWith 1 F) (h0 : F 0 = 0) (x : D.Space) : Lp ℝ 2 μ :=
  (D.contract_memLp hF h0 x).toLp _

/--
The L² contraction class has the prescribed composition as an almost-everywhere representative.
-/
theorem coe_contractLp (hF : LipschitzWith 1 F) (h0 : F 0 = 0) (x : D.Space) :
    ⇑(D.contractLp hF h0 x) =ᵐ[μ] fun ω => F (D.toLp x ω) :=
  MemLp.coeFn_toLp _

/-- A normal contraction of a form-domain element remains in the form domain. -/
theorem contractLp_mem (hF : LipschitzWith 1 F) (h0 : F 0 = 0) (x : D.Space) :
    D.contractLp hF h0 x ∈ D.form.dom :=
  (D.contraction hF h0 (D.form.formToDomain x) _ (D.coe_contractLp hF h0 x)).1

/-- The normal contraction F applied to an element of 𝔻. -/
def contract (hF : LipschitzWith 1 F) (h0 : F 0 = 0) (x : D.Space) : D.Space :=
  D.form.formToDomain.symm ⟨D.contractLp hF h0 x, D.contractLp_mem hF h0 x⟩

/-- The contracted form-space element maps to the contracted L² class. -/
theorem toLp_contract (hF : LipschitzWith 1 F) (h0 : F 0 = 0) (x : D.Space) :
    D.toLp (D.contract hF h0 x) = D.contractLp hF h0 x := rfl

/-- A normal contraction decreases the norm of 𝔻. -/
theorem norm_contract_le (hF : LipschitzWith 1 F) (h0 : F 0 = 0) (x : D.Space) :
    ‖D.contract hF h0 x‖ ≤ ‖x‖ := by
  obtain ⟨hw, hE⟩ := D.contraction hF h0 (D.form.formToDomain x) _ (D.coe_contractLp hF h0 x)
  have hL : ‖D.contractLp hF h0 x‖ ≤ ‖D.toLp x‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [D.coe_contractLp hF h0 x] with ω hω
    rw [hω]
    have h := hF.dist_le_mul (D.toLp x ω) 0
    simpa [h0, Real.dist_eq] using h
  have h1 := D.norm_sq_eq (D.contract hF h0 x)
  have h2 := D.norm_sq_eq x
  have h3 : D.form.formToDomain (D.contract hF h0 x) = ⟨D.contractLp hF h0 x, hw⟩ := by
    simp [contract]
  rw [h3, toLp_contract] at h1
  have h4 : ‖D.contractLp hF h0 x‖ ^ 2 ≤ ‖D.toLp x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hL 2
  have h7 : ‖D.contract hF h0 x‖ ^ 2 ≤ ‖x‖ ^ 2 := by linarith
  nlinarith [norm_nonneg x, norm_nonneg (D.contract hF h0 x)]

end Contraction

/-- Absolute value in 𝔻. -/
def absS (x : D.Space) : D.Space := D.contract ErrorStructure.lipschitz_abs (by simp) x

/-- The absolute value in the form space maps to the absolute value of its L² class. -/
theorem toLp_absS (x : D.Space) : D.toLp (D.absS x) = |D.toLp x| :=
  Lp.ext ((D.coe_contractLp ErrorStructure.lipschitz_abs (by simp) x).trans (Lp.coeFn_abs _).symm)

/-- Taking absolute values does not increase the form norm. -/
theorem norm_absS_le (x : D.Space) : ‖D.absS x‖ ≤ ‖x‖ := D.norm_contract_le _ _ x

/-- Supremum and infimum in 𝔻: u ∨ v = ½ (u + v + |u - v|), u ∧ v = ½ (u + v - |u - v|). -/
def supS (x y : D.Space) : D.Space := (2⁻¹ : ℝ) • (x + y + D.absS (y - x))
/-- The pointwise minimum of two form elements, defined by one half of x + y − |y − x|. -/
def infS (x y : D.Space) : D.Space := (2⁻¹ : ℝ) • (x + y - D.absS (y - x))

/-- The maximum in the form space maps to the lattice supremum in L². -/
theorem toLp_supS (x y : D.Space) : D.toLp (D.supS x y) = D.toLp x ⊔ D.toLp y := by
  rw [sup_eq_half_smul_add_add_abs_sub' ℝ, supS, map_smul, map_add, map_add, toLp_absS, map_sub]

/-- The minimum in the form space maps to the lattice infimum in L². -/
theorem toLp_infS (x y : D.Space) : D.toLp (D.infS x y) = D.toLp x ⊓ D.toLp y := by
  rw [inf_eq_half_smul_add_sub_abs_sub' ℝ, infS, map_smul, map_sub, map_add, toLp_absS, map_sub]

/--
BH 1991, ch. I § 8.1, Lemma 8.1.2.1 (statement p. 52, proof p. 53).

BH Lemma 8.1.2.1: ‖u ∨ v‖² + ‖u ∧ v‖² ≤ ‖u‖² + ‖v‖² in 𝔻.
-/
theorem bh_8_1_2_1 (x y : D.Space) :
    ‖D.supS x y‖ ^ 2 + ‖D.infS x y‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have hd : ‖D.absS (y - x)‖ ≤ ‖x - y‖ := by rw [norm_sub_rev]; exact D.norm_absS_le _
  have hd2 : ‖D.absS (y - x)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hp1 := parallelogram_law_with_norm ℝ (x + y) (D.absS (y - x))
  have hp2 := parallelogram_law_with_norm ℝ x y
  have hs : ‖D.supS x y‖ = 2⁻¹ * ‖x + y + D.absS (y - x)‖ := by
    rw [supS, norm_smul]; norm_num
  have hi : ‖D.infS x y‖ = 2⁻¹ * ‖x + y - D.absS (y - x)‖ := by
    rw [infS, norm_smul]; norm_num
  rw [hs, hi]
  nlinarith

/-- The squared form norm of the maximum is at most the sum of the squared input norms. -/
theorem norm_supS_sq_le (x y : D.Space) : ‖D.supS x y‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have h := D.bh_8_1_2_1 x y
  nlinarith [sq_nonneg ‖D.infS x y‖]

/-- The unit contraction t ↦ (0 ∨ t) ∧ 1. -/
def unitF : ℝ → ℝ := fun t => min (max t 0) 1

/-- Clipping a real number to [0, 1] is 1-Lipschitz. -/
theorem lipschitzWith_unitF : LipschitzWith 1 unitF :=
  (LipschitzWith.id.max_const 0).min_const 1

/-- The unit clipping function vanishes at zero. -/
theorem unitF_zero : unitF 0 = 0 := by simp [unitF]

/-- The unit clipping function equals one on [1, ∞). -/
theorem unitF_eq_one {t : ℝ} (ht : 1 ≤ t) : unitF t = 1 := by
  simp only [unitF]
  rw [max_eq_left (by linarith), min_eq_right ht]

/-- Every value of the unit clipping function lies in [0, 1]. -/
theorem unitF_mem (t : ℝ) : 0 ≤ unitF t ∧ unitF t ≤ 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

end DirichletForm
end ErrorCalculus.Capacity
