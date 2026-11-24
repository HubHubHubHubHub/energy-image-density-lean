import ErrorCalculus.Dirichlet.FormConvergence
import DprBridge.BH1991NormalContractions.Basic
import DprBridge.BH1991Printed.Basic
import ErrorCalculus.Dirichlet.EIDConditionalGeneral
import ErrorCalculus.Dirichlet.EntropyDecay.Basic
import ErrorCalculus.Dirichlet.ResolventMarkov.Basic
import ErrorCalculus.Dirichlet.SemigroupResolvent
import GeometricMeasure.Current.Mass.Basic
import GeometricMeasure.VectorMeasure.Compactness.Basic
import GeometricMeasure.VectorMeasure.PolarFreezing
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Positivity, locality and the BH energy identity

This file contains the definitions and results of the development of `DprBridge.BH1991GammaLocality`
that the main statements of the library (the head theorems listed in the README of the repository)
use. `DprBridge.BH1991GammaLocality` imports it and continues the development.

## Main definitions

* `BH1991.DirichletForm.softThreshold`: The scalar residual is t minus its symmetric min/max
  truncation at level c.
* `BH1991.DirichletForm.residual`: The residual cutoff at level 1/(n+1) is obtained by contraction
  in the original form space.
* `BH1991.DirichletForm.residualPlateau`: The domain plateau is the unit truncation of (n+1) times
  the domain absolute value.

## Main statements

* `BH1991.DirichletForm.gammaMatrix_posSemidef`: The finite Gamma matrix is positive semidefinite on
  a single full-measure set.
* `BH1991.DirichletForm.gammaMatrix_integrable`: Each coordinate of the finite Gamma matrix is
  integrable.
* `BH1991.DirichletForm.gamma_eq_zero_of_tests`: An L1 class is zero if its integral pairing with
  every bounded domain test vanishes on the original measure.
* `BH1991.DirichletForm.bounded_memLp_top`: A bounded domain element has an L-infinity
  representative on an arbitrary measure.
* `BH1991.DirichletForm.tendsto_boundedMul`: A fixed essentially bounded multiplier preserves L1
  convergence on an arbitrary measure.
* `BH1991.DirichletForm.energy_eq_integral`: Conditional on BH locality, the original bilinear
  energy equals one half of the integral of Gamma on the original BH domain.

## References

References: Bouleau–Hirsch (1991), ch. I, I.4.1.3, I.5.1.3 and I.6.1.1; ch. V, p. 185; Notes, p.
302. Eriksson-Bique–Murugan, arXiv:2510.13659v1, §4.2, supplies the normal-current method.
-/
noncomputable section
open MeasureTheory Filter Topology ErrorCalculus
open scoped NNReal ENNReal
universe u

namespace DprBridge.BH1991.DirichletForm
variable {X : Type u} [MeasurableSpace X] {m : Measure X} (D : DirichletForm m)

/-- Finite linear combinations commute with the continuous BH bilinear operator. -/
theorem gamma_sum_smul (G : D.CarreDuChamp) {n : ℕ}
    (v : Fin n → D.form.FormSpace) (a b : Fin n → ℝ) :
    G.Γ (∑ i, a i • v i) (∑ j, b j • v j) =
      ∑ i, ∑ j, (a i * b j) • G.Γ (v i) (v j) := by
  simp only [map_sum, map_smul, sum_apply,
    smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- The finite bilinear expansion holds almost everywhere for the selected L1 representatives. -/
theorem coe_gamma_sum_smul (G : D.CarreDuChamp) {n : ℕ}
    (v : Fin n → D.form.FormSpace) (a b : Fin n → ℝ) :
    ⇑(G.Γ (∑ i, a i • v i) (∑ j, b j • v j)) =ᵐ[m]
      fun x => ∑ i, ∑ j, a i * b j * G.Γ (v i) (v j) x := by
  classical
  rw [D.gamma_sum_smul]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => ∑ j, (a i * b j) • G.Γ (v i) (v j)),
    ae_all_iff.mpr (fun i => Lp.coeFn_fun_finsetSum Finset.univ
      (fun j => (a i * b j) • G.Γ (v i) (v j))),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
      Lp.coeFn_smul (a i * b j) (G.Γ (v i) (v j))))] with x h1 h2 h3
  simp only [h1, h2, h3, Pi.smul_apply, smul_eq_mul]

/--
The finite Gamma matrix is positive semidefinite on a single full-measure set. Consequence
of BH 1991, ch. I, I.4.1.3; EID context: ch. V, p. 185, Notes p. 302, and EBM §4.2.
-/
theorem gammaMatrix_posSemidef (G : D.CarreDuChamp)
    {n : ℕ} (f : Fin n → D.form.dom) :
    ∀ᵐ x ∂m, (D.gammaMatrix G f x).PosSemidef := by
  classical
  let v : Fin n → D.form.FormSpace := fun i => D.form.formToDomain.symm (f i)
  have hq : ∀ q : Fin n → ℚ, ∀ᵐ x ∂m,
      0 ≤ ∑ i, ∑ j, (q i : ℝ) * (q j : ℝ) * G.Γ (v i) (v j) x := by
    intro q
    filter_upwards [G.nonneg (∑ i, (q i : ℝ) • v i),
      D.coe_gamma_sum_smul G v (fun i => (q i : ℝ)) (fun i => (q i : ℝ))]
      with x hp he
    simpa only [he, Pi.zero_apply] using hp
  filter_upwards [ae_all_iff.mpr hq] with x hx
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact congrArg (fun z : Lp ℝ 1 m => z x) (G.symm (v j) (v i))
  · intro a
    have hd : DenseRange (fun q : Fin n → ℚ => fun i => (q i : ℝ)) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    have hr : 0 ≤ ∑ i, ∑ j, a i * a j * G.Γ (v i) (v j) x :=
      hd.induction_on a (isClosed_le continuous_const (by fun_prop)) hx
    simpa [gammaMatrix, v, dotProduct, Matrix.mulVec, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm] using hr

/-- Each coordinate of the finite Gamma matrix is integrable. Consequence of the L1-valued
operator in BH 1991, ch. I, I.4.1.3; EBM §4.2. -/
theorem gammaMatrix_integrable (G : D.CarreDuChamp)
    {n : ℕ} (f : Fin n → D.form.dom) (i j : Fin n) :
    Integrable (fun x => D.gammaMatrix G f x i j) m :=
  L1.integrable_coeFn _

/--
Conditional on BH locality, the shifted zero-product energy identity holds on the form- preserving
capacity adapter. Using BH 1991, ch. I, I.5.1.3.
-/
theorem local_toCapacity (hL : D.Local) (f g : D.toCapacity.Space) (a : ℝ)
    (h : ∀ᵐ x ∂m, (D.toCapacity.toLp f x + a) * D.toCapacity.toLp g x = 0) :
    D.toCapacity.ener f g = 0 := by
  rw [D.toCapacity.ener_apply]
  exact hL (D.form.formToDomain f) (D.form.formToDomain g) a h

/--
An L1 class is zero if its integral pairing with every bounded domain test vanishes on the original
measure.
-/
theorem gamma_eq_zero_of_tests (b : Lp ℝ 1 m)
    (h : ∀ z ∈ D.toCapacity.bddSpace,
      ∫ x, D.toCapacity.toLp z x * b x ∂m = 0) : b = 0 := by
  apply D.toCapacity.eq_of_pair_eq D.denseRange_toCapacity
  intro z hz
  change (∫ x, D.toCapacity.toLp z x * b x ∂m) =
    ∫ x, D.toCapacity.toLp z x * (0 : Lp ℝ 1 m) x ∂m
  rw [h z hz]
  symm
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_zero ℝ 1 m] with x hx
  change (0 : Lp ℝ 1 m) x = 0 at hx
  change D.toCapacity.toLp z x * (0 : Lp ℝ 1 m) x = 0
  rw [hx, mul_zero]

/-- A bounded domain element has an L-infinity representative on an arbitrary measure. -/
theorem bounded_memLp_top (h : D.toCapacity.Space) (hh : h ∈ D.toCapacity.bddSpace) :
    MemLp (D.toCapacity.toLp h) ∞ m := by
  obtain ⟨C, hC⟩ := hh
  exact memLp_top_of_bound (Lp.aestronglyMeasurable _) C
    (hC.mono fun _ hx => by simpa only [Real.norm_eq_abs] using hx)

/-- A fixed essentially bounded multiplier preserves L1 convergence on an arbitrary measure. -/
theorem tendsto_boundedMul {c : X → ℝ} (hc : MemLp c ∞ m) {C : ℝ}
    (hC : ∀ᵐ x ∂m, |c x| ≤ C) {a : ℕ → Lp ℝ 1 m} {b : Lp ℝ 1 m}
    (ht : Tendsto a atTop (𝓝 b)) :
    Tendsto (fun n => boundedMul c hc (a n)) atTop (𝓝 (boundedMul c hc b)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim := (tendsto_iff_norm_sub_tendsto_zero.mp ht).const_mul C
  rw [mul_zero] at hlim
  apply squeeze_zero (fun n => norm_nonneg _) _ hlim
  intro n
  rw [← boundedMul_sub c hc (a n) b]
  exact norm_boundedMul_le c hc (a n - b) hC

/-- The diagonal Gamma has total integral at most twice the energy. Consequence of BH 1991, ch.
I, I.4.1.3. -/
theorem integral_gamma_self_le (G : D.CarreDuChamp) (f : D.toCapacity.Space) :
    ∫ x, G.Γ f f x ∂m ≤ 2 * D.toCapacity.ener f f := by
  have he : ‖G.Γ f f‖ = ∫ x, G.Γ f f x ∂m := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [G.nonneg f] with x hx
    exact Real.norm_of_nonneg hx
  rw [← he]
  exact D.toCapacity.isCarreDuChamp_norm_le D.denseRange_toCapacity
    (D.carreDuChamp_toCapacity G) f

/--
Conditional on BH locality, a bounded domain function v satisfies the diagonal energy identity if a
bounded domain plateau h obeys h <= 1 and h v = v almost everywhere.
-/
theorem integral_gamma_self_of_plateau (hL : D.Local) (G : D.CarreDuChamp)
    (v h : D.toCapacity.Space) (hv : v ∈ D.toCapacity.bddSpace)
    (hh : h ∈ D.toCapacity.bddSpace)
    (hupper : ∀ᵐ x ∂m, D.toCapacity.toLp h x ≤ 1)
    (hplateau : ∀ᵐ x ∂m, D.toCapacity.toLp h x * D.toCapacity.toLp v x =
      D.toCapacity.toLp v x) :
    ∫ x, G.Γ v v x ∂m = 2 * D.toCapacity.ener v v := by
  have hvh : D.toCapacity.mulS v h = v := by
    apply D.toCapacity.eq_of_ae
    filter_upwards [D.toCapacity.coeFn_toLp_mulS hv hh, hplateau] with x he hp
    rw [he, mul_comm]
    exact hp
  have hEr : D.toCapacity.ener h (D.toCapacity.mulS v v) = 0 := by
    apply D.local_toCapacity hL _ _ (-1)
    filter_upwards [D.toCapacity.coeFn_toLp_mulS hv hv, hplateau] with x he hp
    rw [he]
    linear_combination D.toCapacity.toLp v x * hp
  have hi := D.carreDuChamp_toCapacity G v hv v hv h hh
  rw [hvh, hEr] at hi
  have hle : (∫ x, D.toCapacity.toLp h x * G.Γ v v x ∂m) ≤ ∫ x, G.Γ v v x ∂m := by
    apply integral_mono_ae (D.toCapacity.integrable_pair hh _) (L1.integrable_coeFn _)
    filter_upwards [hupper, G.nonneg v] with x hx hp
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hx hp
  have hb := D.integral_gamma_self_le G v
  linarith

/-- The scalar residual is t minus its symmetric min/max truncation at level c. -/
def softThreshold (c t : ℝ) : ℝ := t - max (min t c) (-c)

/-- The scalar residual fixes zero for every nonnegative level. -/
theorem softThreshold_zero {c : ℝ} (hc : 0 ≤ c) : softThreshold c 0 = 0 := by
  simp [softThreshold, min_eq_left hc, max_eq_left (neg_nonpos.mpr hc)]

/-- The scalar residual is 1-Lipschitz at every nonnegative level. -/
theorem lipschitzWith_softThreshold {c : ℝ} (_hc : 0 ≤ c) :
    LipschitzWith 1 (softThreshold c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  have hab1 := le_abs_self (x - y)
  have hab2 := neg_le_abs (x - y)
  apply abs_le.mpr
  simp only [softThreshold, min_def, max_def]
  split_ifs <;> constructor <;> linarith

/-- At a nonnegative level, the scalar residual is dominated in absolute value by its input. -/
theorem abs_softThreshold_le {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    |softThreshold c t| ≤ |t| := by
  have h := (lipschitzWith_softThreshold hc).dist_le_mul t 0
  simpa only [softThreshold_zero hc, Real.dist_eq, sub_zero, NNReal.coe_one,
    one_mul] using h

/-- The scalar residual at level 1/(n+1) tends pointwise to its input. -/
theorem tendsto_softThreshold (t : ℝ) :
    Tendsto (fun n : ℕ => softThreshold ((n : ℝ) + 1)⁻¹ t) atTop (𝓝 t) := by
  have hc : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
  have ht : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
  simpa [softThreshold] using ht.sub ((ht.min hc).max hc.neg)

/-- The residual cutoff at level 1/(n+1) is obtained by contraction in the original form space. -/
def residual (n : ℕ) (f : D.toCapacity.Space) : D.toCapacity.Space :=
  D.toCapacity.contract (lipschitzWith_softThreshold (by positivity :
    (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹)) (softThreshold_zero (by positivity)) f

/-- The residual cutoff is represented almost everywhere by the scalar residual at level 1/(n+1). -/
theorem coe_residual (n : ℕ) (f : D.toCapacity.Space) :
    ⇑(D.toCapacity.toLp (D.residual n f)) =ᵐ[m]
      fun x => softThreshold ((n : ℝ) + 1)⁻¹ (D.toCapacity.toLp f x) :=
  D.toCapacity.coe_contractLp (lipschitzWith_softThreshold (by positivity :
    (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹)) (softThreshold_zero (by positivity)) f

/-- Residual cutoffs retain essential boundedness. -/
theorem residual_bounded (n : ℕ) (f : D.toCapacity.Space)
    (hf : f ∈ D.toCapacity.bddSpace) : D.residual n f ∈ D.toCapacity.bddSpace := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  filter_upwards [hC, D.coe_residual n f] with x hx he
  rw [he]
  exact (abs_softThreshold_le (by positivity) _).trans hx

/-- Residual cutoffs have no greater energy than their input. -/
theorem energy_residual_le (n : ℕ) (f : D.toCapacity.Space) :
    D.toCapacity.ener (D.residual n f) (D.residual n f) ≤ D.toCapacity.ener f f := by
  have h := D.normal_contraction (lipschitzWith_softThreshold (by positivity :
      (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹)) (softThreshold_zero (by positivity))
    (D.form.formToDomain f) (D.toCapacity.toLp (D.residual n f)) (D.coe_residual n f)
  obtain ⟨hw, he⟩ := h
  simp only [D.toCapacity.ener_apply]
  exact he

/--
Residual cutoffs converge to their input in the form norm, by dominated L2 convergence and the
closed-form energy bound.
-/
theorem tendsto_residual (f : D.toCapacity.Space) :
    Tendsto (fun n => D.residual n f) atTop (𝓝 f) := by
  have ht : Tendsto (fun n => D.toCapacity.toLp (D.residual n f)) atTop
      (𝓝 (D.toCapacity.toLp f)) := by
    have h := Foundations.tendsto_toLp_dominated m
      (fun n => Lp.memLp (D.toCapacity.toLp (D.residual n f)))
      (Lp.memLp (D.toCapacity.toLp f)) (Lp.memLp (D.toCapacity.toLp f)).norm
      (fun n => ?_) ?_
    · have he : ∀ z : Lp ℝ 2 m, (Lp.memLp z).toLp _ = z :=
        fun z => Lp.ext (Lp.memLp z).coeFn_toLp
      simpa only [he] using h
    · filter_upwards [D.coe_residual n f] with x hx
      simpa only [hx, Real.norm_eq_abs] using abs_softThreshold_le
        (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹) (D.toCapacity.toLp f x)
    · filter_upwards [ae_all_iff.mpr (fun n => D.coe_residual n f)] with x hx
      simpa only [hx] using tendsto_softThreshold (D.toCapacity.toLp f x)
  have hs := D.closed.tendsto_formSpace_of_energy_le
    (u := fun n => D.form.formToDomain (D.residual n f))
    (v := D.form.formToDomain f) ht (fun n => by
      simpa only [D.toCapacity.ener_apply] using D.energy_residual_le n f)
  simpa only [LinearEquiv.symm_apply_apply] using hs

/-- The domain plateau is the unit truncation of (n+1) times the domain absolute value. -/
def residualPlateau (n : ℕ) (f : D.toCapacity.Space) : D.toCapacity.Space :=
  D.toCapacity.contract Capacity.DirichletForm.lipschitzWith_unitF
    Capacity.DirichletForm.unitF_zero (((n : ℝ) + 1) • D.toCapacity.absS f)

/--
The plateau is represented almost everywhere by the unit truncation of (n+1) times the absolute
value of the input representative.
-/
theorem coe_residualPlateau (n : ℕ) (f : D.toCapacity.Space) :
    ⇑(D.toCapacity.toLp (D.residualPlateau n f)) =ᵐ[m] fun x =>
      Capacity.DirichletForm.unitF (((n : ℝ) + 1) * |D.toCapacity.toLp f x|) := by
  have hc := D.toCapacity.coe_contractLp Capacity.DirichletForm.lipschitzWith_unitF
    Capacity.DirichletForm.unitF_zero (((n : ℝ) + 1) • D.toCapacity.absS f)
  have he : D.toCapacity.toLp (((n : ℝ) + 1) • D.toCapacity.absS f) =
      ((n : ℝ) + 1) • |D.toCapacity.toLp f| := by
    rw [map_smul, D.toCapacity.toLp_absS]
  change ⇑(D.toCapacity.toLp (D.residualPlateau n f)) =ᵐ[m] _ at hc
  rw [he] at hc
  filter_upwards [hc, Lp.coeFn_smul ((n : ℝ) + 1) |D.toCapacity.toLp f|,
    Lp.coeFn_abs (D.toCapacity.toLp f)] with x h1 h2 h3
  simpa only [h2, h3, Pi.smul_apply, smul_eq_mul] using h1

/-- The domain plateau takes values in the unit interval almost everywhere. -/
theorem residualPlateau_unit (n : ℕ) (f : D.toCapacity.Space) :
    ∀ᵐ x ∂m, 0 ≤ D.toCapacity.toLp (D.residualPlateau n f) x ∧
      D.toCapacity.toLp (D.residualPlateau n f) x ≤ 1 := by
  filter_upwards [D.coe_residualPlateau n f] with x hx
  rw [hx]
  exact Capacity.DirichletForm.unitF_mem _

/-- The domain plateau belongs to the bounded form algebra. -/
theorem residualPlateau_bounded (n : ℕ) (f : D.toCapacity.Space) :
    D.residualPlateau n f ∈ D.toCapacity.bddSpace := by
  refine ⟨1, ?_⟩
  filter_upwards [D.residualPlateau_unit n f] with x hx
  simpa only [abs_of_nonneg hx.1] using hx.2

/--
For positive b, the unit truncation of b times the input modulus fixes the scalar residual at level
1/b by multiplication.
-/
theorem unitF_mul_softThreshold {b : ℝ} (hb : 0 < b) (t : ℝ) :
    Capacity.DirichletForm.unitF (b * |t|) * softThreshold b⁻¹ t =
      softThreshold b⁻¹ t := by
  by_cases ht : |t| ≤ b⁻¹
  · have ht' := abs_le.mp ht
    have hz : softThreshold b⁻¹ t = 0 := by
      simp only [softThreshold, min_eq_left ht'.2, max_eq_left ht'.1, sub_self]
    simp only [hz, mul_zero]
  · have hbt : 1 ≤ b * |t| := by
      have h := mul_le_mul_of_nonneg_left (le_of_not_ge ht) hb.le
      rwa [mul_inv_cancel₀ hb.ne'] at h
    rw [Capacity.DirichletForm.unitF_eq_one hbt, one_mul]

/-- Multiplication by the domain plateau fixes the residual cutoff almost everywhere. -/
theorem residualPlateau_mul_residual (n : ℕ) (f : D.toCapacity.Space) :
    ∀ᵐ x ∂m, D.toCapacity.toLp (D.residualPlateau n f) x *
      D.toCapacity.toLp (D.residual n f) x = D.toCapacity.toLp (D.residual n f) x := by
  filter_upwards [D.coe_residualPlateau n f, D.coe_residual n f] with x hh hv
  rw [hh, hv]
  exact unitF_mul_softThreshold (by positivity) _

/--
Conditional on BH locality, every residual cutoff of a bounded domain element satisfies the diagonal
energy identity.
-/
theorem integral_gamma_residual (hL : D.Local) (G : D.CarreDuChamp)
    (f : D.toCapacity.Space) (hf : f ∈ D.toCapacity.bddSpace) (n : ℕ) :
    ∫ x, G.Γ (D.residual n f) (D.residual n f) x ∂m =
      2 * D.toCapacity.ener (D.residual n f) (D.residual n f) :=
  D.integral_gamma_self_of_plateau hL G _ _ (D.residual_bounded n f hf)
    (D.residualPlateau_bounded n f) ((D.residualPlateau_unit n f).mono fun _ hx => hx.2)
    (D.residualPlateau_mul_residual n f)

/--
Conditional on BH locality, every bounded domain element satisfies the diagonal energy identity.
Proving BH 1991, ch. I, I.6.1.1 in this case.
-/
theorem integral_gamma_self_bounded (hL : D.Local) (G : D.CarreDuChamp)
    (f : D.toCapacity.Space) (hf : f ∈ D.toCapacity.bddSpace) :
    ∫ x, G.Γ f f x ∂m = 2 * D.toCapacity.ener f f := by
  have ht := (D.tendsto_residual f).prodMk_nhds (D.tendsto_residual f)
  have hg := continuous_integral.tendsto (G.Γ f f) |>.comp
    ((G.Γ.continuous₂.tendsto (f, f)).comp ht)
  have he := ((D.toCapacity.ener.continuous₂.tendsto (f, f)).comp ht).const_mul 2
  exact tendsto_nhds_unique hg (he.congr fun n => (D.integral_gamma_residual hL G f hf n).symm)

/-- Conditional on BH locality, the integral of diagonal Gamma equals twice the energy on an
arbitrary measure. BH 1991, ch. I, I.6.1.1. -/
theorem integral_gamma_self (hL : D.Local) (G : D.CarreDuChamp)
    (f : D.toCapacity.Space) :
    ∫ x, G.Γ f f x ∂m = 2 * D.toCapacity.ener f f := by
  have hc : IsClosed {v : D.toCapacity.Space |
      ∫ x, G.Γ v v x ∂m = 2 * D.toCapacity.ener v v} :=
    isClosed_eq (continuous_integral.comp (G.Γ.continuous.clm_apply continuous_id))
      (continuous_const.mul (D.toCapacity.ener.continuous.clm_apply continuous_id))
  exact hc.closure_subset_iff.mpr (D.integral_gamma_self_bounded hL G)
    (D.toCapacity.dense_bddSpace f)

/-- Conditional on BH locality, the integral of Gamma(f,g) equals twice the bilinear energy on
the capacity adapter. BH 1991, ch. I, I.6.1.1, polarized. -/
theorem integral_gamma (hL : D.Local) (G : D.CarreDuChamp)
    (f g : D.toCapacity.Space) :
    ∫ x, G.Γ f g x ∂m = 2 * D.toCapacity.ener f g := by
  have h := D.integral_gamma_self hL G (f + g)
  have hff := D.integral_gamma_self hL G f
  have hgg := D.integral_gamma_self hL G g
  have he : G.Γ (f + g) (f + g) = (G.Γ f f + G.Γ f g) + (G.Γ f g + G.Γ g g) := by
    simp only [map_add, add_apply, G.symm g f]
  have hi : (∫ x, G.Γ (f + g) (f + g) x ∂m) =
      (∫ x, G.Γ f f x ∂m) + (∫ x, G.Γ f g x ∂m) +
        ((∫ x, G.Γ f g x ∂m) + (∫ x, G.Γ g g x ∂m)) := by
    rw [he]
    have hadd (a b : Lp ℝ 1 m) :
        (∫ x, (a + b) x ∂m) = (∫ x, a x ∂m) + ∫ x, b x ∂m := by
      calc
        _ = ∫ x, a x + b x ∂m := integral_congr_ae (Lp.coeFn_add a b)
        _ = _ := integral_add (L1.integrable_coeFn a) (L1.integrable_coeFn b)
    rw [hadd, hadd, hadd]
  have hsym : D.toCapacity.ener g f = D.toCapacity.ener f g := D.toCapacity.ener_symm _ _
  rw [hi] at h
  simp only [map_add, add_apply, hsym] at h
  linarith

/--
Conditional on BH locality, the original bilinear energy equals one half of the integral of
Gamma on the original BH domain. BH 1991, ch. I, I.6.1.1; EID context: ch. V, p. 185, Notes p. 302;
EBM §4.2 uses gamma = Gamma/2.
-/
theorem energy_eq_integral (hL : D.Local) (G : D.CarreDuChamp)
    (f g : D.form.dom) :
    D.form.E f g = (1 / 2 : ℝ) *
      ∫ x, G.Γ (D.form.formToDomain.symm f)
        (D.form.formToDomain.symm g) x ∂m := by
  have h := D.integral_gamma hL G (D.form.formToDomain.symm f) (D.form.formToDomain.symm g)
  rw [D.toCapacity.ener_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply] at h
  linarith

end DprBridge.BH1991.DirichletForm
