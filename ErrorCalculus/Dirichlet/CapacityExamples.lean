import ErrorCalculus.Dirichlet.Capacity
import ErrorCalculus.Dirichlet.ErrorStructure
import ErrorCalculus.Dirichlet.DirichletProperty
import ErrorCalculus.Dirichlet.Calculus
import ErrorCalculus.Dirichlet.WhiteNoiseHilbert
import Mathlib.Tactic

/-!
# error structures as Dirichlet forms; capacity controls

## Main results
Every library error structure (B19; μ a probability measure) is a form in this framework
(`ofErrorStructure`, normal contractions supplied by without an additional hypothesis; no
equivalence with the Markov property alone is claimed). Controls: the a.e. capacity of a μ-null set
is zero (hence BH's outer extension, def. 8.1.1, p. 52); for the zero structure, capAE(G) = μ(G)
(measurable G) and cap(G) = μ(G) (open G); c(Ω) = 1 for every error structure on a probability
space.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity
namespace DirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Variational
variable (D : DirichletForm μ)

/--
BH 1991, ch. I § 8.1, definition 8.1.1 (p. 52): reason for the outer extension to arbitrary sets.

Control: the a.e. capacity of a μ-null set is zero (0 is admissible on it); this is why BH defines
c(A), for arbitrary A, using the open sets containing it.
-/
theorem capAE_eq_zero_of_measure_zero {G : Set Ω} (hG : μ G = 0) : D.capAE G = 0 := by
  refine le_antisymm ?_ zero_le
  have h0 : (0 : D.Space) ∈ D.adm G := by
    show ∀ᵐ ω ∂μ, ω ∈ G → 1 ≤ D.toLp 0 ω
    exact (measure_eq_zero_iff_ae_notMem.1 hG).mono fun ω h hω => absurd hω h
  calc D.capAE G ≤ ENNReal.ofReal (‖(0 : D.Space)‖ ^ 2) := D.capAE_le h0
    _ = 0 := by simp

end Variational

/-! ### Error structures (ErrorCalculus) as Dirichlet forms -/

/--
adaptation: every error structure (B19) is a form in this framework; normal contractions follow from
`ErrorStructure.normal_contraction` (BH 1991, ch. I, prop. 3.3.1, p. 14). No equivalence with the
Markov property alone is claimed.

Every library error structure (B19; μ a probability measure) defines a Dirichlet form in this file's
sense (normal contractions: `ErrorStructure.normal_contraction`).
-/
def ofErrorStructure [IsProbabilityMeasure μ] (S : ErrorStructure Ω μ) : DirichletForm μ where
  form := S.energy
  closed := S.energy_closed
  contraction := fun hF _ u w hw => S.normal_contraction hF u w hw

/--
zero error structure, BH 1991, ch. I § 8.1, definition 8.1.1 (p. 52).

Control: for the zero error structure (ℰ = 0, 𝔻 = L²), capAE(G) = μ(G) for measurable G. The
indicator is used as a witness; its explicit identification with the equilibrium potential is not
stated here.
-/
theorem capAE_ofErrorStructure_zero [IsProbabilityMeasure μ] {G : Set Ω} (hG : MeasurableSet G) :
    (ofErrorStructure (ErrorStructure.zero (Ω := Ω) (μ := μ))).capAE G = μ G := by
  set D := ofErrorStructure (ErrorStructure.zero (Ω := Ω) (μ := μ)) with hD
  refine le_antisymm ?_ (D.measure_le_capAE hG)
  let w : Lp ℝ 2 μ := indicatorConstLp 2 hG (measure_ne_top μ G) (1 : ℝ)
  have hw : w ∈ D.form.dom := Submodule.mem_top
  let x : D.Space := D.form.formToDomain.symm ⟨w, hw⟩
  have hxw : D.toLp x = w := rfl
  have hx : x ∈ D.adm G := by
    show ∀ᵐ ω ∂μ, ω ∈ G → 1 ≤ D.toLp x ω
    rw [hxw]
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hG) (hμs := measure_ne_top μ G)
      (c := (1 : ℝ))] with ω h hω
    rw [h, Set.indicator_of_mem hω]
  have hn : ‖x‖ ^ 2 = μ.real G := by
    rw [D.norm_sq_eq, hxw]
    have hE : D.form.E (D.form.formToDomain x) (D.form.formToDomain x) = 0 :=
      ErrorStructure.zeroData_energy _ _
    rw [hE, add_zero, norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top]
    simp only [norm_one, one_mul, ENNReal.toReal_ofNat]
    rw [← Real.rpow_natCast, ← Real.rpow_mul measureReal_nonneg]
    norm_num
  calc D.capAE G ≤ ENNReal.ofReal (‖x‖ ^ 2) := D.capAE_le hx
    _ = μ G := by rw [hn, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ G)]

variable [TopologicalSpace Ω]

/-- zero error structure, BH 1991, ch. I § 8.1, definition 8.1.1 (p. 52), on open sets. -/
theorem cap_ofErrorStructure_zero_of_isOpen [IsProbabilityMeasure μ] [OpensMeasurableSpace Ω]
    {G : Set Ω} (hG : IsOpen G) :
    (ofErrorStructure (ErrorStructure.zero (Ω := Ω) (μ := μ))).cap G = μ G := by
  rw [cap_eq_capAE _ hG, capAE_ofErrorStructure_zero hG.measurableSet]

/--
BH 1991, ch. I § 8.1, definition 8.1.1 and proposition 8.1.3 a) (pp. 52–53): c(Ω) = 1 for every
error structure.

Control: for every error structure on a probability space, c(Ω) = 1. The constant 1, with zero
energy, gives the upper bound.
-/
theorem cap_univ_ofErrorStructure [IsProbabilityMeasure μ] [OpensMeasurableSpace Ω]
    (S : ErrorStructure Ω μ) : (ofErrorStructure S).cap Set.univ = 1 := by
  set D := ofErrorStructure S with hD
  refine le_antisymm ?_ ?_
  · let x : D.Space := D.form.formToDomain.symm (S.const 1)
    have hxw : D.toLp x = Lp.const 2 μ (1 : ℝ) := rfl
    have hx : x ∈ D.adm Set.univ := by
      show ∀ᵐ ω ∂μ, ω ∈ Set.univ → 1 ≤ D.toLp x ω
      rw [hxw]
      filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with ω h _
      rw [h, Function.const_apply]
    have hn : ‖x‖ ^ 2 = 1 := by
      rw [D.norm_sq_eq, hxw]
      have hE : D.form.E (D.form.formToDomain x) (D.form.formToDomain x) = 0 :=
        S.energy_const 1
      rw [hE, add_zero, ← ErrorCalculus.l2_integral_norm_sq,
        integral_congr_ae ((Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))).mono
          fun ω h => by rw [h])]
      simp
    calc D.cap Set.univ = D.capAE Set.univ := D.cap_eq_capAE isOpen_univ
      _ ≤ ENNReal.ofReal (‖x‖ ^ 2) := D.capAE_le hx
      _ = 1 := by rw [hn, ENNReal.ofReal_one]
  · calc (1 : ℝ≥0∞) = μ Set.univ := measure_univ.symm
      _ ≤ D.cap Set.univ := D.bh_8_1_3_a Set.univ

end DirichletForm
end ErrorCalculus.Capacity
