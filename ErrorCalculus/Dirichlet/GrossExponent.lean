import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Gross Exponent

## Main results
The Gross exponent for the convention E = ½∫Γ.
-/
noncomputable section
open Filter Topology
namespace ErrorCalculus

def grossExponent (c p t : ℝ) : ℝ := 1 + (p-1) * Real.exp (4*t/c)

@[simp] theorem grossExponent_zero (c p : ℝ) : grossExponent c p 0 = p := by
  simp [grossExponent]

theorem grossExponent_one_lt {c p : ℝ} (hp : 1 < p) (t : ℝ) :
    1 < grossExponent c p t := by
  have := mul_pos (sub_pos.mpr hp) (Real.exp_pos (4*t/c))
  dsimp [grossExponent]
  linarith

theorem hasDerivAt_grossExponent (c p t : ℝ) :
    HasDerivAt (grossExponent c p) (4*(grossExponent c p t-1)/c) t := by
  convert! (((((hasDerivAt_id t).const_mul 4).div_const c).exp).const_mul (p-1)).const_add 1 using 1
  simp only [grossExponent, id_eq]
  ring

theorem continuous_grossExponent (c p : ℝ) : Continuous (grossExponent c p) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_grossExponent c p t).continuousAt

@[simp] theorem grossExponent_four (p t : ℝ) :
    grossExponent 4 p t = 1 + (p-1)*Real.exp t := by
  simp [grossExponent]

@[simp] theorem grossExponent_four_two (t : ℝ) :
    grossExponent 4 2 t = 1 + Real.exp t := by norm_num

end ErrorCalculus
