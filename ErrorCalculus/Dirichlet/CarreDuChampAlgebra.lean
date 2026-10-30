import ErrorCalculus.Dirichlet.CapacityForm
import ErrorCalculus.Dirichlet.FiniteEnergyDual
import ErrorCalculus.Dirichlet.ResolventEquation

/-!
# Carre du champ (BH 1991, ch. I § 4.1), part 1: the algebra 𝔻 ∩ L^∞, BH form, βR_β

## Main results
Framework: `DirichletForm μ`, a closed form on L²(μ), for arbitrary μ, with normal contractions; 𝔻 =
`D.Space`. No semigroup: the form resolvent (`QuadForm.resolvent`) replaces BH proposition 2.3.3.

* A. 𝔻 ∩ L^∞ (`bddSpace`), products (BH corollary 3.3.2), the form (f, g) ↦ ℰ(fh, g) + ℰ(gh, f) −
ℰ(h, fg).
* B. The sub-Markov property of βR_β (BH prop. 3.2.1, part 3).
* C. A pointwise Kadison-type inequality for βR_β (an ingredient of prop. 4.1.1).

The continuation (approximating forms, prop. 4.1.1) is in
`ErrorCalculus.Dirichlet.CarreDuChampApprox`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity
namespace DirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## A. 𝔻 ∩ L^∞, products, the BH trilinear form -/

section Products

/--
Product of two L² classes, taken in L² when it belongs there (0 otherwise, a value never used under
the boundedness assumptions).
-/
def mulBdd (f g : Lp ℝ 2 μ) : Lp ℝ 2 μ := by
  classical
  exact if h : MemLp (fun ω => f ω * g ω) 2 μ then h.toLp _ else 0

/-- An L² pointwise product represents the class `mulBdd` almost everywhere. -/
theorem coeFn_mulBdd {f g : Lp ℝ 2 μ} (h : MemLp (fun ω => f ω * g ω) 2 μ) :
    ⇑(mulBdd f g) =ᵐ[μ] fun ω => f ω * g ω := by
  classical
  have he : mulBdd f g = h.toLp _ := by simp only [mulBdd, dif_pos h]
  rw [he]
  exact h.coeFn_toLp

/-- The product of an essentially bounded class and an L² class lies in L². -/
theorem memLp_mul_of_bdd {f : Lp ℝ 2 μ} {C : ℝ} (hf : ∀ᵐ ω ∂μ, |f ω| ≤ C) (g : Lp ℝ 2 μ) :
    MemLp (fun ω => f ω * g ω) 2 μ := by
  have hft : MemLp (fun ω => f ω) ∞ μ :=
    memLp_top_of_bound (Lp.aestronglyMeasurable f) C
      (hf.mono fun ω h => by rwa [Real.norm_eq_abs])
  exact (Lp.memLp g).mul' hft

/-- The product of an L² function and an essentially bounded L² function belongs to L². -/
theorem memLp_mul_of_bdd' (f : Lp ℝ 2 μ) {g : Lp ℝ 2 μ} {C : ℝ} (hg : ∀ᵐ ω ∂μ, |g ω| ≤ C) :
    MemLp (fun ω => f ω * g ω) 2 μ := by
  have h := memLp_mul_of_bdd hg f
  refine h.congr_norm (Lp.aestronglyMeasurable f |>.mul (Lp.aestronglyMeasurable g)) ?_
  exact ae_of_all _ fun ω => by rw [mul_comm]

/-- Linear combination of four classes, pointwise representative. -/
theorem coeFn_comb4 (a b c d : Lp ℝ 2 μ) (r s : ℝ) :
    ⇑(a - r • b - c + s • d) =ᵐ[μ] fun ω => a ω - r * b ω - c ω + s * d ω := by
  filter_upwards [Lp.coeFn_add (a - r • b - c) (s • d), Lp.coeFn_sub (a - r • b) c,
    Lp.coeFn_sub a (r • b), Lp.coeFn_smul r b, Lp.coeFn_smul s d] with ω h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, Pi.sub_apply, h3, Pi.sub_apply, h4, h5]
  rfl

end Products

variable (D : DirichletForm μ)

section Bounded

/-- The form ℰ as a continuous bilinear form on 𝔻 (the form `formBilin` at parameter 0). -/
def ener : D.Space →L[ℝ] D.Space →L[ℝ] ℝ := D.form.formBilin 0

/-- The continuous energy form evaluates to the original form under the domain equivalence. -/
theorem ener_apply (x y : D.Space) :
    D.ener x y = D.form.E (D.form.formToDomain x) (D.form.formToDomain y) := by
  rw [ener, QuadForm.formBilin_apply, zero_mul, add_zero]

/-- The energy is bounded above by the squared form norm. -/
theorem ener_self_le (x : D.Space) : D.ener x x ≤ ‖x‖ ^ 2 := by
  rw [D.ener_apply, D.norm_sq_eq]
  nlinarith [sq_nonneg ‖D.toLp x‖]

/-- The diagonal energy is nonnegative. -/
theorem ener_self_nonneg (x : D.Space) : 0 ≤ D.ener x x := by
  rw [D.ener_apply]; exact D.form.nonneg _

/-- The continuous energy form is symmetric. -/
theorem ener_symm (x y : D.Space) : D.ener x y = D.ener y x := by
  rw [D.ener_apply, D.ener_apply, D.form.symm]

/--
BH 1991, ch. I § 4.1 (p. 17): the space 𝔻 ∩ L^∞ on which BH states definition 4.1.2.

𝔻 ∩ L^∞: the essentially bounded elements of 𝔻, a subspace of 𝔻.
-/
def bddSpace : Submodule ℝ D.Space where
  carrier := {x | ∃ C : ℝ, ∀ᵐ ω ∂μ, |D.toLp x ω| ≤ C}
  add_mem' := by
    rintro x y ⟨C, hC⟩ ⟨C', hC'⟩
    refine ⟨C + C', ?_⟩
    filter_upwards [hC, hC', Lp.coeFn_add (D.toLp x) (D.toLp y)] with ω h1 h2 h3
    rw [map_add, h3, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  zero_mem' := ⟨0, by
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with ω h
    rw [map_zero, h]
    simp⟩
  smul_mem' := by
    rintro c x ⟨C, hC⟩
    refine ⟨|c| * C, ?_⟩
    filter_upwards [hC, Lp.coeFn_smul c (D.toLp x)] with ω h1 h2
    rw [map_smul, h2, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)

/-- Membership in the bounded form subspace is equivalent to an a.e. bound on the representative. -/
theorem mem_bddSpace {x : D.Space} : x ∈ D.bddSpace ↔ ∃ C : ℝ, ∀ᵐ ω ∂μ, |D.toLp x ω| ≤ C :=
  Iff.rfl

/-- The function t ↦ (clamp_M t)² / (2M), a normal contraction for M > 0. -/
def sqF (M : ℝ) : ℝ → ℝ := fun t => (max (min t M) (-M)) ^ 2 / (2 * M)

/-- For M > 0, the clipped quadratic profile `sqF M` is 1-Lipschitz. -/
theorem lipschitz_sqF {M : ℝ} (hM : 0 < M) : LipschitzWith 1 (sqF M) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [sqF, Real.dist_eq, NNReal.coe_one, one_mul]
  have hc : ∀ r : ℝ, |max (min r M) (-M)| ≤ M := fun r =>
    abs_le.2 ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩
  have hab : |max (min s M) (-M) - max (min t M) (-M)| ≤ |s - t| := by
    have h := ((LipschitzWith.id.min_const M).max_const (-M)).dist_le_mul s t
    simpa [Real.dist_eq] using h
  have h2M : (0 : ℝ) < 2 * M := by linarith
  rw [div_sub_div_same, abs_div, abs_of_pos h2M, div_le_iff₀ h2M]
  have hsq : max (min s M) (-M) ^ 2 - max (min t M) (-M) ^ 2 =
      (max (min s M) (-M) - max (min t M) (-M)) * (max (min s M) (-M) + max (min t M) (-M)) := by
    ring
  rw [hsq, abs_mul]
  have hsum : |max (min s M) (-M) + max (min t M) (-M)| ≤ 2 * M := by
    have := abs_add_le (max (min s M) (-M)) (max (min t M) (-M))
    linarith [hc s, hc t]
  calc |max (min s M) (-M) - max (min t M) (-M)| * |max (min s M) (-M) + max (min t M) (-M)|
      ≤ |s - t| * (2 * M) := mul_le_mul hab hsum (abs_nonneg _) (abs_nonneg _)

/-- For M > 0, the clipped quadratic profile vanishes at zero. -/
theorem sqF_zero {M : ℝ} (hM : 0 < M) : sqF M 0 = 0 := by
  simp [sqF, min_eq_left hM.le, max_eq_left (show -M ≤ 0 by linarith)]

/-- On |t| ≤ M, the clipped quadratic profile equals t²/(2M). -/
theorem sqF_of_abs_le {M t : ℝ} (ht : |t| ≤ M) : sqF M t = t ^ 2 / (2 * M) := by
  have h := abs_le.1 ht
  simp only [sqF, min_eq_left h.2, max_eq_left h.1]

/-- The square of an element of 𝔻 ∩ L^∞ lies in 𝔻 (the normal contraction t ↦ (clamp t)²/(2M)). -/
theorem mulBdd_self_mem {x : D.Space} (hx : x ∈ D.bddSpace) :
    mulBdd (D.toLp x) (D.toLp x) ∈ D.form.dom := by
  obtain ⟨C, hC⟩ := hx
  set M : ℝ := max C 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCM : ∀ᵐ ω ∂μ, |D.toLp x ω| ≤ M := hC.mono fun ω h => h.trans (le_max_left _ _)
  have hm := memLp_mul_of_bdd hC (D.toLp x)
  set w : Lp ℝ 2 μ := (2 * M)⁻¹ • mulBdd (D.toLp x) (D.toLp x) with hw
  have hwe : ⇑w =ᵐ[μ] fun ω => sqF M ((D.form.formToDomain x : Lp ℝ 2 μ) ω) := by
    filter_upwards [Lp.coeFn_smul (2 * M)⁻¹ (mulBdd (D.toLp x) (D.toLp x)), coeFn_mulBdd hm, hCM]
      with ω h1 h2 h3
    rw [hw, h1, Pi.smul_apply, h2, smul_eq_mul, ← D.toLp_apply, sqF_of_abs_le h3]
    field_simp
  obtain ⟨hwd, -⟩ := D.contraction (lipschitz_sqF hM) (sqF_zero hM) (D.form.formToDomain x) w hwe
  have he : mulBdd (D.toLp x) (D.toLp x) = (2 * M) • w := by
    rw [hw, smul_smul, mul_inv_cancel₀ (by linarith), one_smul]
  rw [he]
  exact D.form.dom.smul_mem _ hwd

/-- The pointwise product of two bounded form-space representatives is essentially bounded. -/
theorem bdd_mul {x y : D.Space} (hx : x ∈ D.bddSpace) (hy : y ∈ D.bddSpace) :
    ∃ C : ℝ, ∀ᵐ ω ∂μ, |D.toLp x ω * D.toLp y ω| ≤ C := by
  obtain ⟨C, hC⟩ := hx
  obtain ⟨C', hC'⟩ := hy
  refine ⟨|C| * |C'|, ?_⟩
  filter_upwards [hC, hC'] with ω h1 h2
  rw [abs_mul]
  exact mul_le_mul (h1.trans (le_abs_self C)) (h2.trans (le_abs_self C')) (abs_nonneg _)
    (abs_nonneg _)

/-- The product of two elements of 𝔻 ∩ L^∞ lies in 𝔻 (polarization). -/
theorem mulBdd_mem {x y : D.Space} (hx : x ∈ D.bddSpace) (hy : y ∈ D.bddSpace) :
    mulBdd (D.toLp x) (D.toLp y) ∈ D.form.dom := by
  have hxy := D.bddSpace.add_mem hx hy
  have hxy' := D.bddSpace.sub_mem hx hy
  obtain ⟨C, hC⟩ := hx
  obtain ⟨C₁, hC₁⟩ := hxy
  obtain ⟨C₂, hC₂⟩ := hxy'
  have he : mulBdd (D.toLp x) (D.toLp y) = (4⁻¹ : ℝ) • (mulBdd (D.toLp (x + y)) (D.toLp (x + y)) -
      mulBdd (D.toLp (x - y)) (D.toLp (x - y))) := by
    apply Lp.ext
    filter_upwards [coeFn_mulBdd (memLp_mul_of_bdd hC (D.toLp y)),
      coeFn_mulBdd (memLp_mul_of_bdd hC₁ (D.toLp (x + y))),
      coeFn_mulBdd (memLp_mul_of_bdd hC₂ (D.toLp (x - y))),
      Lp.coeFn_smul (4⁻¹ : ℝ) (mulBdd (D.toLp (x + y)) (D.toLp (x + y)) -
        mulBdd (D.toLp (x - y)) (D.toLp (x - y))),
      Lp.coeFn_sub (mulBdd (D.toLp (x + y)) (D.toLp (x + y)))
        (mulBdd (D.toLp (x - y)) (D.toLp (x - y))),
      Lp.coeFn_add (D.toLp x) (D.toLp y), Lp.coeFn_sub (D.toLp x) (D.toLp y)]
      with ω h1 h2 h3 h4 h5 h6 h7
    rw [h1, h4, Pi.smul_apply, h5, Pi.sub_apply, h2, h3, map_add, map_sub, h6, h7, Pi.add_apply,
      Pi.sub_apply, smul_eq_mul]
    ring
  rw [he]
  exact D.form.dom.smul_mem _ (D.form.dom.sub_mem (D.mulBdd_self_mem (⟨C₁, hC₁⟩))
    (D.mulBdd_self_mem ⟨C₂, hC₂⟩))

/-- The product fg in 𝔻 (0 outside 𝔻 ∩ L^∞, a value never used). -/
def mulS (x y : D.Space) : D.Space := by
  classical
  exact if h : mulBdd (D.toLp x) (D.toLp y) ∈ D.form.dom then
    D.form.formToDomain.symm ⟨mulBdd (D.toLp x) (D.toLp y), h⟩ else 0

/-- For bounded form elements, the form-space product maps to the L² product class. -/
theorem toLp_mulS {x y : D.Space} (hx : x ∈ D.bddSpace) (hy : y ∈ D.bddSpace) :
    D.toLp (D.mulS x y) = mulBdd (D.toLp x) (D.toLp y) := by
  classical
  have hm := D.mulBdd_mem hx hy
  have h1 : D.mulS x y = D.form.formToDomain.symm ⟨mulBdd (D.toLp x) (D.toLp y), hm⟩ := by
    unfold mulS
    simp only [dif_pos hm]
  rw [h1]
  simp only [toLp_apply, LinearEquiv.apply_symm_apply]

/-- For bounded form elements, the product representative equals the pointwise product a.e. -/
theorem coeFn_toLp_mulS {x y : D.Space} (hx : x ∈ D.bddSpace) (hy : y ∈ D.bddSpace) :
    ⇑(D.toLp (D.mulS x y)) =ᵐ[μ] fun ω => D.toLp x ω * D.toLp y ω := by
  rw [D.toLp_mulS hx hy]
  obtain ⟨C, hC⟩ := hx
  exact coeFn_mulBdd (memLp_mul_of_bdd hC (D.toLp y))

/--
BH 1991, ch. I § 3.3, corollary 3.3.2 (p. 14): 𝔻 ∩ L^∞ is an algebra.

The product of two elements of 𝔻 ∩ L^∞ lies in 𝔻 ∩ L^∞ and represents the pointwise product.
-/
theorem mulS_mem {x y : D.Space} (hx : x ∈ D.bddSpace) (hy : y ∈ D.bddSpace) :
    D.mulS x y ∈ D.bddSpace := by
  obtain ⟨C, hC⟩ := D.bdd_mul hx hy
  refine ⟨C, ?_⟩
  filter_upwards [D.coeFn_toLp_mulS hx hy, hC] with ω h1 h2
  rw [h1]; exact h2

/-- Equality in 𝔻 from a.e. equality of representatives. -/
theorem eq_of_ae {x y : D.Space} (h : ⇑(D.toLp x) =ᵐ[μ] ⇑(D.toLp y)) : x = y :=
  D.toLp_injective (Lp.ext h)

/-- The form-space product is commutative on bounded elements. -/
theorem mulS_comm {x y : D.Space} (hx : x ∈ D.bddSpace) (hy : y ∈ D.bddSpace) :
    D.mulS x y = D.mulS y x := by
  apply D.eq_of_ae
  filter_upwards [D.coeFn_toLp_mulS hx hy, D.coeFn_toLp_mulS hy hx] with ω h1 h2
  rw [h1, h2, mul_comm]

/-- The form-space product distributes over addition in its first bounded argument. -/
theorem mulS_add_left {x x' y : D.Space} (hx : x ∈ D.bddSpace) (hx' : x' ∈ D.bddSpace)
    (hy : y ∈ D.bddSpace) : D.mulS (x + x') y = D.mulS x y + D.mulS x' y := by
  apply D.eq_of_ae
  filter_upwards [D.coeFn_toLp_mulS (D.bddSpace.add_mem hx hx') hy, D.coeFn_toLp_mulS hx hy,
    D.coeFn_toLp_mulS hx' hy, Lp.coeFn_add (D.toLp (D.mulS x y)) (D.toLp (D.mulS x' y)),
    Lp.coeFn_add (D.toLp x) (D.toLp x')] with ω h1 h2 h3 h4 h5
  rw [h1, map_add D.toLp (D.mulS x y) (D.mulS x' y), h4, Pi.add_apply, h2, h3,
    map_add D.toLp x x', h5, Pi.add_apply]
  ring

/-- The form-space product commutes with real scalar multiplication on bounded elements. -/
theorem mulS_smul_left (c : ℝ) {x y : D.Space} (hx : x ∈ D.bddSpace) (hy : y ∈ D.bddSpace) :
    D.mulS (c • x) y = c • D.mulS x y := by
  apply D.eq_of_ae
  filter_upwards [D.coeFn_toLp_mulS (D.bddSpace.smul_mem c hx) hy, D.coeFn_toLp_mulS hx hy,
    Lp.coeFn_smul c (D.toLp (D.mulS x y)), Lp.coeFn_smul c (D.toLp x)] with ω h1 h2 h3 h4
  rw [h1, map_smul D.toLp c (D.mulS x y), h3, Pi.smul_apply, h2, map_smul D.toLp c x, h4,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- The product as a bilinear map on 𝔻 ∩ L^∞. -/
def mulB : D.bddSpace →ₗ[ℝ] D.bddSpace →ₗ[ℝ] D.bddSpace :=
  LinearMap.mk₂ ℝ (fun x y => ⟨D.mulS x y, D.mulS_mem x.2 y.2⟩)
    (fun x x' y => Subtype.ext (D.mulS_add_left x.2 x'.2 y.2))
    (fun c x y => Subtype.ext (D.mulS_smul_left c x.2 y.2))
    (fun x y y' => Subtype.ext (by
      change D.mulS x (y + y') = D.mulS x y + D.mulS x y'
      rw [D.mulS_comm x.2 (D.bddSpace.add_mem y.2 y'.2), D.mulS_add_left y.2 y'.2 x.2,
        D.mulS_comm y.2 x.2, D.mulS_comm y'.2 x.2]))
    (fun c x y => Subtype.ext (by
      change D.mulS x (c • y) = c • D.mulS x y
      rw [D.mulS_comm x.2 (D.bddSpace.smul_mem c y.2), D.mulS_smul_left c y.2 x.2,
        D.mulS_comm y.2 x.2]))

/-- The bounded-subspace product coerces to the form-space product. -/
@[simp] theorem coe_mulB (x y : D.bddSpace) : ((D.mulB x y : D.bddSpace) : D.Space) = D.mulS x y :=
  rfl

/--
The BH bilinear form (f, g) ↦ ℰ(fh, g) + ℰ(gh, f) − ℰ(h, fg) (prop. 4.1.3, p. 17), with h fixed in 𝔻
∩ L^∞.
-/
def bhForm (z : D.bddSpace) : D.bddSpace →ₗ[ℝ] D.bddSpace →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun x y => D.ener (D.mulB x z) y + D.ener (D.mulB y z) x - D.ener z (D.mulB x y))
    (fun x x' y => by simp only [map_add, Submodule.coe_add, FunLike.coe_add, Pi.add_apply,
      LinearMap.add_apply]; ring)
    (fun c x y => by simp only [map_smul, Submodule.coe_smul, FunLike.coe_smul, Pi.smul_apply,
      LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [map_add, Submodule.coe_add, FunLike.coe_add, Pi.add_apply,
      LinearMap.add_apply]; ring)
    (fun c x y => by simp only [map_smul, Submodule.coe_smul, FunLike.coe_smul, Pi.smul_apply,
      LinearMap.smul_apply, smul_eq_mul]; ring)

/-- The BH form at (z, x, y) is ℰ(xz, y) + ℰ(yz, x) − ℰ(z, xy). -/
theorem bhForm_apply (z x y : D.bddSpace) :
    D.bhForm z x y = D.ener (D.mulS x z) y + D.ener (D.mulS y z) x - D.ener z (D.mulS x y) :=
  rfl

/-- The BH form is symmetric in its two energy arguments. -/
theorem bhForm_symm (z x y : D.bddSpace) : D.bhForm z x y = D.bhForm z y x := by
  rw [D.bhForm_apply, D.bhForm_apply, D.mulS_comm x.2 y.2]
  ring

/-- Linearity in h. -/
theorem bhForm_add (z z' x y : D.bddSpace) :
    D.bhForm (z + z') x y = D.bhForm z x y + D.bhForm z' x y := by
  simp only [D.bhForm_apply, Submodule.coe_add]
  rw [D.mulS_comm x.2 (D.bddSpace.add_mem z.2 z'.2), D.mulS_comm y.2 (D.bddSpace.add_mem z.2 z'.2),
    D.mulS_add_left z.2 z'.2 x.2, D.mulS_add_left z.2 z'.2 y.2, D.mulS_comm z.2 x.2,
    D.mulS_comm z'.2 x.2, D.mulS_comm z.2 y.2, D.mulS_comm z'.2 y.2]
  simp only [map_add, FunLike.coe_add, Pi.add_apply]
  ring

/-- Scaling the test argument scales the BH form by the same real scalar. -/
theorem bhForm_smul (c : ℝ) (z x y : D.bddSpace) :
    D.bhForm (c • z) x y = c * D.bhForm z x y := by
  simp only [D.bhForm_apply, Submodule.coe_smul]
  rw [D.mulS_comm x.2 (D.bddSpace.smul_mem c z.2), D.mulS_comm y.2 (D.bddSpace.smul_mem c z.2),
    D.mulS_smul_left c z.2 x.2, D.mulS_smul_left c z.2 y.2, D.mulS_comm z.2 x.2,
    D.mulS_comm z.2 y.2]
  simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- A normal contraction of an element of 𝔻 ∩ L^∞ remains in 𝔻 ∩ L^∞. -/
theorem contract_mem_bddSpace {F : ℝ → ℝ} (hF : LipschitzWith 1 F) (h0 : F 0 = 0) {x : D.Space}
    (hx : x ∈ D.bddSpace) : D.contract hF h0 x ∈ D.bddSpace := by
  obtain ⟨C, hC⟩ := hx
  refine ⟨C, ?_⟩
  filter_upwards [D.coe_contractLp hF h0 x, hC] with ω h1 h2
  rw [toLp_contract, h1]
  have h := hF.dist_le_mul (D.toLp x ω) 0
  simp only [h0, Real.dist_eq, sub_zero, NNReal.coe_one, one_mul] at h
  exact h.trans h2

end Bounded

/-! ## B. The sub-Markov property of βR_β (BH prop. 3.2.1, part 3) -/

section Markov

/-- The normalized form resolvent βR_β, an operator on L². -/
def sres (β : ℝ) (hβ : 0 < β) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := β • D.form.resolvent D.closed β hβ

/-- At β > 0, the normalized resolvent is the L² class of the domain resolvent βR_β. -/
theorem sres_apply (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 μ) :
    D.sres β hβ f = (D.form.betaResolventDom D.closed β hβ f : Lp ℝ 2 μ) := by
  rw [QuadForm.coe_betaResolventDom]; rfl

/-- Symmetry of βR_β. -/
theorem inner_sres (β : ℝ) (hβ : 0 < β) (f g : Lp ℝ 2 μ) :
    ⟪D.sres β hβ f, g⟫_ℝ = ⟪f, D.sres β hβ g⟫_ℝ := by
  simp only [sres, FunLike.coe_smul, Pi.smul_apply, real_inner_smul_left, real_inner_smul_right,
    QuadForm.resolvent_symm]

/-- A normal contraction fixing the datum fixes βR_β (the minimization argument, with F(0) = 0). -/
theorem sres_fixed (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 μ) {F : ℝ → ℝ} (hF : LipschitzWith 1 F)
    (h0 : F 0 = 0) (hf : ∀ᵐ ω ∂μ, F (f ω) = f ω) (w : Lp ℝ 2 μ)
    (hw : ⇑w =ᵐ[μ] fun ω => F (D.sres β hβ f ω)) : w = D.sres β hβ f := by
  set u := D.form.betaResolventDom D.closed β hβ f with hu
  have hu' : (u : Lp ℝ 2 μ) = D.sres β hβ f := (D.sres_apply β hβ f).symm
  have hw' : ⇑w =ᵐ[μ] fun ω => F ((u : Lp ℝ 2 μ) ω) := by rw [hu']; exact hw
  obtain ⟨hd, hE⟩ := D.contraction hF h0 u w hw'
  have hn : ‖w - f‖ ≤ ‖(u : Lp ℝ 2 μ) - f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hw', hf, Lp.coeFn_sub w f, Lp.coeFn_sub (u : Lp ℝ 2 μ) f] with ω h1 h2 h3 h4
    have hl := hF.dist_le_mul ((u : Lp ℝ 2 μ) ω) (f ω)
    simpa only [h3, h4, Pi.sub_apply, h1, h2, NNReal.coe_one, one_mul, Real.dist_eq,
      Real.norm_eq_abs] using hl
  have he := D.form.eq_resolvent_of_le D.closed β hβ f ⟨w, hd⟩ (by
    change D.form.E ⟨w, hd⟩ ⟨w, hd⟩ + β * ‖w - f‖ ^ 2 ≤
      D.form.E u u + β * ‖(u : Lp ℝ 2 μ) - f‖ ^ 2
    exact add_le_add hE (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hβ.le))
  have h2 := congrArg (fun v : D.form.dom => (v : Lp ℝ 2 μ)) he
  simp only at h2
  rw [h2, hu']

/--
BH 1991, ch. I § 3.2, proposition 3.2.1, part 3) of the proof (p. 13): βR_β is sub-Markov; here in
lower-bound form, for a Dirichlet form in this framework (normal contractions), without a semigroup.

If f ≥ −c a.e. (c ≥ 0), then βR_β f ≥ −c a.e.
-/
theorem sres_ge (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 μ) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ᵐ ω ∂μ, -c ≤ f ω) : ∀ᵐ ω ∂μ, -c ≤ D.sres β hβ f ω := by
  have hF : LipschitzWith 1 (fun t : ℝ => max t (-c)) := LipschitzWith.id.max_const (-c)
  have h0 : (fun t : ℝ => max t (-c)) 0 = 0 := max_eq_left (by linarith)
  have hm : MemLp (fun ω => max (D.sres β hβ f ω) (-c)) 2 μ :=
    hF.comp_memLp h0 (Lp.memLp (D.sres β hβ f))
  have hw : ⇑(hm.toLp _) =ᵐ[μ] fun ω => max (D.sres β hβ f ω) (-c) := hm.coeFn_toLp
  have he := D.sres_fixed β hβ f hF h0 (hf.mono fun ω h => max_eq_left h) (hm.toLp _) hw
  rw [he] at hw
  filter_upwards [hw] with ω h
  rw [h]
  exact le_max_right _ _

/-- Positivity of βR_β. -/
theorem sres_nonneg (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 μ) (hf : ∀ᵐ ω ∂μ, 0 ≤ f ω) :
    ∀ᵐ ω ∂μ, 0 ≤ D.sres β hβ f ω := by
  have h := D.sres_ge β hβ f le_rfl (hf.mono fun ω h => by linarith)
  exact h.mono fun ω h => by linarith

/-- Upper bound: f ≤ c a.e. (c ≥ 0) ⇒ βR_β f ≤ c a.e. -/
theorem sres_le (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 μ) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ᵐ ω ∂μ, f ω ≤ c) : ∀ᵐ ω ∂μ, D.sres β hβ f ω ≤ c := by
  have hneg : ∀ᵐ ω ∂μ, -c ≤ (-f) ω := by
    filter_upwards [hf, Lp.coeFn_neg f] with ω h1 h2
    rw [h2, Pi.neg_apply]; linarith
  have h := D.sres_ge β hβ (-f) hc hneg
  filter_upwards [h, Lp.coeFn_neg (D.sres β hβ f)] with ω h1 h2
  rw [map_neg, h2, Pi.neg_apply] at h1
  linarith

end Markov

/-! ## C. The key pointwise inequality -/

section Kadison

/--
The approximate carre du champ ψ_β(f) = f² − 2 f·βR_β f + βR_β(f²), an L² class (f essentially
bounded).
-/
def psiL2 (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  mulBdd f f - (2 : ℝ) • mulBdd f (D.sres β hβ f) + D.sres β hβ (mulBdd f f)

/-- For bounded f, the L² remainder is represented a.e. by βR_β(f²) − 2f βR_β(f) + f². -/
theorem coeFn_psiL2 (β : ℝ) (hβ : 0 < β) {f : Lp ℝ 2 μ} {C : ℝ} (hf : ∀ᵐ ω ∂μ, |f ω| ≤ C) :
    ⇑(D.psiL2 β hβ f) =ᵐ[μ] fun ω =>
      D.sres β hβ (mulBdd f f) ω - 2 * f ω * D.sres β hβ f ω + f ω ^ 2 := by
  filter_upwards [Lp.coeFn_add (mulBdd f f - (2 : ℝ) • mulBdd f (D.sres β hβ f))
      (D.sres β hβ (mulBdd f f)), Lp.coeFn_sub (mulBdd f f) ((2 : ℝ) • mulBdd f (D.sres β hβ f)),
    Lp.coeFn_smul (2 : ℝ) (mulBdd f (D.sres β hβ f)), coeFn_mulBdd (memLp_mul_of_bdd hf f),
    coeFn_mulBdd (memLp_mul_of_bdd hf (D.sres β hβ f))] with ω h1 h2 h3 h4 h5
  rw [psiL2, h1, Pi.add_apply, h2, Pi.sub_apply, h3, Pi.smul_apply, h4, h5, smul_eq_mul]
  ring

/--
an ingredient of the proof of BH 1991, ch. I, prop. 4.1.1 (p. 17), which refers to prop. 2.3.3
(semigroup): a pointwise Kadison-type inequality for the symmetric sub-Markov operator βR_β,
established using only the sub-Markov lower bound and a rational argument (no kernel,
no constants in L²).

If g = F ∘ f with F a normal contraction and f, g essentially bounded, then a.e. βR_β(g²) − 2 g βR_β
g + g² ≤ βR_β(f²) − 2 f βR_β f + f².
-/
theorem psi_le (β : ℝ) (hβ : 0 < β) {f g : Lp ℝ 2 μ} {C C' : ℝ} (hf : ∀ᵐ ω ∂μ, |f ω| ≤ C)
    (hg : ∀ᵐ ω ∂μ, |g ω| ≤ C') {F : ℝ → ℝ} (hF : LipschitzWith 1 F) (h0 : F 0 = 0)
    (hgf : ∀ᵐ ω ∂μ, g ω = F (f ω)) :
    ∀ᵐ ω ∂μ, D.sres β hβ (mulBdd g g) ω - 2 * g ω * D.sres β hβ g ω + g ω ^ 2 ≤
      D.sres β hβ (mulBdd f f) ω - 2 * f ω * D.sres β hβ f ω + f ω ^ 2 := by
  set K := D.sres β hβ with hK
  have hff := coeFn_mulBdd (memLp_mul_of_bdd hf f)
  have hgg := coeFn_mulBdd (memLp_mul_of_bdd hg g)
  have key : ∀ t : ℚ, ∀ᵐ ω ∂μ, 0 ≤ K (mulBdd f f) ω - 2 * (t : ℝ) * K f ω - K (mulBdd g g) ω +
      2 * F t * K g ω + ((t : ℝ) ^ 2 - F t ^ 2) := by
    intro t
    have hFt : |F t| ≤ |(t : ℝ)| := by
      have h := hF.dist_le_mul (t : ℝ) 0
      simp only [h0, Real.dist_eq, sub_zero, NNReal.coe_one, one_mul] at h
      exact h
    have hc : 0 ≤ (t : ℝ) ^ 2 - F t ^ 2 := by
      have := sq_le_sq' (abs_le.1 hFt).1 (abs_le.1 hFt).2
      nlinarith [sq_abs (t : ℝ), abs_nonneg (t : ℝ)]
    set φ : Lp ℝ 2 μ := mulBdd f f - (2 * (t : ℝ)) • f - mulBdd g g + (2 * F t) • g with hφ
    have hφb : ∀ᵐ ω ∂μ, -((t : ℝ) ^ 2 - F t ^ 2) ≤ φ ω := by
      filter_upwards [coeFn_comb4 (mulBdd f f) f (mulBdd g g) g (2 * (t : ℝ)) (2 * F t), hff, hgg,
        hgf] with ω h1 h2 h3 h4
      rw [hφ, h1, h2, h3, h4]
      have hl : |F (f ω) - F t| ≤ |f ω - t| := by
        have h := hF.dist_le_mul (f ω) t
        simpa [Real.dist_eq] using h
      have hsq : (F (f ω) - F t) ^ 2 ≤ (f ω - t) ^ 2 := by
        have := sq_le_sq' (abs_le.1 hl).1 (abs_le.1 hl).2
        nlinarith [sq_abs (f ω - (t : ℝ)), sq_abs (F (f ω) - F t)]
      nlinarith
    have hKφ := D.sres_ge β hβ φ hc hφb
    have hKe : K φ = K (mulBdd f f) - (2 * (t : ℝ)) • K f - K (mulBdd g g) + (2 * F t) • K g := by
      rw [hφ, map_add, map_sub, map_sub, map_smul, map_smul]
    filter_upwards [hKφ, coeFn_comb4 (K (mulBdd f f)) (K f) (K (mulBdd g g)) (K g) (2 * (t : ℝ))
      (2 * F t)] with ω h1 h2
    rw [hKe, h2] at h1
    linarith
  have hall := ae_all_iff.2 key
  filter_upwards [hall, hgf] with ω hω hgω
  have hFc : Continuous F := hF.continuous
  have hr : ∀ t : ℝ, 0 ≤ K (mulBdd f f) ω - 2 * t * K f ω - K (mulBdd g g) ω +
      2 * F t * K g ω + (t ^ 2 - F t ^ 2) := by
    intro t
    exact Rat.denseRange_cast.induction_on t (isClosed_le continuous_const (by fun_prop)) hω
  have h := hr (f ω)
  rw [← hgω] at h
  nlinarith

/-- Positivity of ψ_β(f) (the case F = 0). -/
theorem psi_nonneg (β : ℝ) (hβ : 0 < β) {f : Lp ℝ 2 μ} {C : ℝ} (hf : ∀ᵐ ω ∂μ, |f ω| ≤ C) :
    ∀ᵐ ω ∂μ, 0 ≤ D.sres β hβ (mulBdd f f) ω - 2 * f ω * D.sres β hβ f ω + f ω ^ 2 := by
  have h0 : ∀ᵐ ω ∂μ, |(0 : Lp ℝ 2 μ) ω| ≤ 0 := by
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with ω h; rw [h]; simp
  have hz : ∀ᵐ ω ∂μ, (0 : Lp ℝ 2 μ) ω = (fun _ : ℝ => (0 : ℝ)) (f ω) := by
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with ω h; rw [h]; rfl
  have h := D.psi_le β hβ hf h0 ((LipschitzWith.const (0 : ℝ)).weaken zero_le_one) rfl hz
  have hm : mulBdd (0 : Lp ℝ 2 μ) 0 = 0 := by
    apply Lp.ext
    filter_upwards [coeFn_mulBdd (memLp_mul_of_bdd h0 0), Lp.coeFn_zero ℝ 2 μ] with ω h1 h2
    rw [h1, h2]; simp
  filter_upwards [h, Lp.coeFn_zero ℝ 2 μ] with ω h1 h2
  rw [hm, map_zero, h2] at h1
  simpa using h1

end Kadison

end DirichletForm
end ErrorCalculus.Capacity
