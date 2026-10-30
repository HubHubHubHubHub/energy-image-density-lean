import ErrorCalculus.Dirichlet.CarreDuChampAlgebra
import ErrorCalculus.Dirichlet.ApproximatingForm

/-!
# Carre du champ (BH 1991, ch. I § 4.1), part 1: approximating forms and proposition 4.1.1

## Main results
Continuation of `ErrorCalculus.Dirichlet.CarreDuChampAlgebra`.

* D. βR_β is an L¹ contraction on nonnegative functions (without sigma-finiteness), approximating
forms ℰ_β, the integral identity 2ℰ_β(fh, f) − ℰ_β(h, f²) = β ⟪h, ψ_β(f)⟫.
* E. BH proposition 4.1.1: for 0 ≤ h ≤ M, h ∈ 𝔻 ∩ L^∞, f ∈ 𝔻 ∩ L^∞, F a normal contraction, g = F ∘
f: 0 ≤ ℰ(gh, g) − ½ ℰ(h, g²) ≤ ℰ(fh, f) − ½ ℰ(h, f²) ≤ M ℰ(f) (bound in the L^∞ norm of h).
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity
namespace DirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## D. Approximating forms, integral identity, integrability -/

section Integrals

/--
A measurable function whose lower integrals on finite-measure sets are bounded by C has integral
bounded by C, provided its level sets {φ ≥ 1/(n+1)} have finite measure (monotone convergence; no
sigma-finiteness).
-/
theorem lintegral_le_of_setLIntegral_le {φ : Ω → ℝ} (hφ : Measurable φ)
    (hfin : ∀ n : ℕ, μ {ω | 1 / ((n : ℝ) + 1) ≤ φ ω} ≠ ∞) {C : ℝ≥0∞}
    (hA : ∀ A, MeasurableSet A → μ A ≠ ∞ → ∫⁻ ω in A, ENNReal.ofReal (φ ω) ∂μ ≤ C) :
    ∫⁻ ω, ENNReal.ofReal (φ ω) ∂μ ≤ C := by
  set A : ℕ → Set Ω := fun n => {ω | 1 / ((n : ℝ) + 1) ≤ φ ω} with hAdef
  have hAm : ∀ n, MeasurableSet (A n) := fun n => measurableSet_le measurable_const hφ
  set g : ℕ → Ω → ℝ≥0∞ := fun n => (A n).indicator (fun ω => ENNReal.ofReal (φ ω)) with hg
  have hgm : ∀ n, Measurable (g n) := fun n =>
    (ENNReal.measurable_ofReal.comp hφ).indicator (hAm n)
  have hmono : Monotone g := by
    intro m n hmn
    apply Set.indicator_le_indicator_of_subset _ (fun _ => zero_le)
    intro ω' hω'
    simp only [hAdef, Set.mem_setOf_eq] at hω' ⊢
    refine le_trans ?_ hω'
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hle : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    exact one_div_le_one_div_of_le hm hle
  have hsup : ∀ ω, ⨆ n, g n ω = ENNReal.ofReal (φ ω) := by
    intro ω
    apply le_antisymm
    · exact iSup_le fun n => Set.indicator_le_self (A n) _ ω
    · by_cases hp : 0 < φ ω
      · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hp
        refine le_iSup_of_le n (le_of_eq ?_)
        simp only [hg]
        rw [Set.indicator_of_mem (show ω ∈ A n from hn.le)]
      · rw [ENNReal.ofReal_of_nonpos (not_lt.1 hp)]
        exact zero_le
  calc ∫⁻ ω, ENNReal.ofReal (φ ω) ∂μ = ∫⁻ ω, ⨆ n, g n ω ∂μ := by simp_rw [hsup]
    _ = ⨆ n, ∫⁻ ω, g n ω ∂μ := lintegral_iSup hgm hmono
    _ ≤ C := iSup_le fun n => by
        simp only [hg]
        rw [lintegral_indicator (hAm n)]
        exact hA _ (hAm n) (hfin n)

/-- Level sets of an Lᵖ function (0 < p < ∞) have finite measure. -/
theorem measure_level_ne_top {φ : Ω → ℝ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hφ : MemLp φ p μ) (n : ℕ) : μ {ω | 1 / ((n : ℝ) + 1) ≤ φ ω} ≠ ∞ := by
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hε : Real.toNNReal (1 / ((n : ℝ) + 1)) ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hpos
  refine (lt_of_le_of_lt (measure_mono ?_) (hφ.meas_ge_lt_top hp0 hpt hε)).ne
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hpos.le, coe_nnnorm, Real.norm_eq_abs]
  exact hω.trans (le_abs_self _)

/-- Real-valued version: integrability and an upper bound for the integral. -/
theorem integrable_of_setIntegral_le {φ : Ω → ℝ} (hφm : Measurable φ) (hφ0 : 0 ≤ᵐ[μ] φ)
    (hfin : ∀ n : ℕ, μ {ω | 1 / ((n : ℝ) + 1) ≤ φ ω} ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ A, MeasurableSet A → μ A ≠ ∞ → IntegrableOn φ A μ ∧ ∫ ω in A, φ ω ∂μ ≤ C) :
    Integrable φ μ ∧ ∫ ω, φ ω ∂μ ≤ C := by
  have hl : ∫⁻ ω, ENNReal.ofReal (φ ω) ∂μ ≤ ENNReal.ofReal C := by
    apply lintegral_le_of_setLIntegral_le hφm hfin
    intro A hAm hA'
    obtain ⟨hi, hle⟩ := hA A hAm hA'
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_restrict_of_ae hφ0)]
    exact ENNReal.ofReal_le_ofReal hle
  have hint : Integrable φ μ :=
    ⟨hφm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hφ0).2 (lt_of_le_of_lt hl ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hφ0 hφm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hC hl

/-- Product and L² inner product: ⟪a·b, c⟫ = ⟪b, a·c⟫ (a bounded). -/
theorem inner_mulBdd {a : Lp ℝ 2 μ} {C : ℝ} (ha : ∀ᵐ ω ∂μ, |a ω| ≤ C) (b c : Lp ℝ 2 μ) :
    ⟪mulBdd a b, c⟫_ℝ = ⟪b, mulBdd a c⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulBdd (memLp_mul_of_bdd ha b), coeFn_mulBdd (memLp_mul_of_bdd ha c)]
    with ω h1 h2
  simp only [h1, h2, RCLike.inner_apply, conj_trivial]
  ring

/-- The L² inner product as the integral of the product. -/
theorem inner_eq_integral (a b : Lp ℝ 2 μ) : ⟪a, b⟫_ℝ = ∫ ω, a ω * b ω ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  ring

end Integrals

variable (D : DirichletForm μ)

section Approx

/-- The normalized resolvent is β times the form resolvent, for β > 0. -/
theorem sres_eq (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 μ) :
    D.sres β hβ f = β • D.form.resolvent D.closed β hβ f := rfl

/--
βR_β is an L¹ contraction on nonnegative functions: βR_β g is integrable and ∫ βR_β g ≤ ∫ g
(symmetry and βR_β 1_A ≤ 1).
-/
theorem integrable_sres (β : ℝ) (hβ : 0 < β) {g : Lp ℝ 2 μ} (hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hgi : Integrable g μ) :
    Integrable (D.sres β hβ g) μ ∧ ∫ ω, D.sres β hβ g ω ∂μ ≤ ∫ ω, g ω ∂μ := by
  have hK0 := D.sres_nonneg β hβ g hg0
  refine integrable_of_setIntegral_le (Lp.stronglyMeasurable _).measurable hK0
    (measure_level_ne_top two_ne_zero ENNReal.ofNat_ne_top (Lp.memLp _))
    (integral_nonneg_of_ae hg0) (fun A hA hμA => ?_)
  haveI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hμA
  refine ⟨((Lp.memLp (D.sres β hβ g)).restrict A).integrable one_le_two, ?_⟩
  set e : Lp ℝ 2 μ := indicatorConstLp 2 hA hμA (1 : ℝ) with he
  have hei := indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA) (c := (1 : ℝ))
  have he0 : ∀ᵐ ω ∂μ, 0 ≤ e ω := by
    filter_upwards [hei] with ω h
    rw [h]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have he1 : ∀ᵐ ω ∂μ, e ω ≤ 1 := by
    filter_upwards [hei] with ω h
    rw [h]
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem hω]; exact zero_le_one
  have hKe0 := D.sres_nonneg β hβ e he0
  have hKe1 := D.sres_le β hβ e zero_le_one he1
  rw [← L2.inner_indicatorConstLp_one hA hμA, ← he, ← D.inner_sres, inner_eq_integral]
  refine integral_mono_ae ((Lp.memLp _).integrable_mul (Lp.memLp g)) hgi ?_
  filter_upwards [hKe0, hKe1, hg0] with ω h1 h2 h3
  nlinarith

/--
Integral identity: 2ℰ_β(fh, f) − ℰ_β(h, f²) = β ⟪h, ψ_β(f)⟫, where ℰ_β(u, v) = β ⟪u − βR_β u, v⟫ is
the approximating form.
-/
theorem approx_identity (β : ℝ) (hβ : 0 < β) {x z : D.Space} (hx : x ∈ D.bddSpace)
    (hz : z ∈ D.bddSpace) :
    2 * D.form.approxForm D.closed β hβ (D.toLp (D.mulS x z)) (D.toLp x) -
      D.form.approxForm D.closed β hβ (D.toLp z) (D.toLp (D.mulS x x)) =
    β * ⟪D.toLp z, D.psiL2 β hβ (D.toLp x)⟫_ℝ := by
  obtain ⟨C, hC⟩ := hx
  rw [QuadForm.approxForm_apply, QuadForm.approxForm_apply, ← D.sres_eq, ← D.sres_eq,
    D.toLp_mulS ⟨C, hC⟩ hz, D.toLp_mulS ⟨C, hC⟩ ⟨C, hC⟩]
  have t1 := inner_mulBdd hC (D.toLp z) (D.toLp x)
  have t2 := inner_mulBdd hC (D.toLp z) (D.sres β hβ (D.toLp x))
  have t3 := D.inner_sres β hβ (mulBdd (D.toLp x) (D.toLp z)) (D.toLp x)
  have t4 := D.inner_sres β hβ (D.toLp z) (mulBdd (D.toLp x) (D.toLp x))
  simp only [psiL2, inner_sub_left, inner_add_right, inner_sub_right, real_inner_smul_right]
  rw [t3, t1, t2, t4]
  ring

/-- Upper bound: for 0 ≤ h ≤ M, β ⟪h, ψ_β(f)⟫ ≤ 2M ℰ_β(f, f). -/
theorem inner_psi_le (β : ℝ) (hβ : 0 < β) {x z : D.Space} (hx : x ∈ D.bddSpace) {M : ℝ}
    (hM : 0 ≤ M) (hz0 : ∀ᵐ ω ∂μ, 0 ≤ D.toLp z ω) (hzM : ∀ᵐ ω ∂μ, D.toLp z ω ≤ M) :
    β * ⟪D.toLp z, D.psiL2 β hβ (D.toLp x)⟫_ℝ ≤
      2 * M * D.form.approxForm D.closed β hβ (D.toLp x) (D.toLp x) := by
  obtain ⟨C, hC⟩ := hx
  set f := D.toLp x with hfdef
  set K := D.sres β hβ with hKdef
  have hff : ⇑(mulBdd f f) =ᵐ[μ] fun ω => f ω * f ω := coeFn_mulBdd (memLp_mul_of_bdd hC f)
  have iff : Integrable (fun ω => f ω * f ω) μ := (Lp.memLp f).integrable_mul (Lp.memLp f)
  have hK := D.integrable_sres β hβ (g := mulBdd f f)
    (hff.mono fun ω h => by rw [h]; exact mul_self_nonneg _) (iff.congr hff.symm)
  have ifK : Integrable (fun ω => f ω * K f ω) μ := (Lp.memLp f).integrable_mul (Lp.memLp (K f))
  have hψ := D.coeFn_psiL2 β hβ hC
  have hψ0 := D.psi_nonneg β hβ hC
  have iψ : Integrable (fun ω => K (mulBdd f f) ω - 2 * f ω * K f ω + f ω ^ 2) μ := by
    have h := (hK.1.sub (ifK.const_mul 2)).add iff
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have s1 : ⟪D.toLp z, D.psiL2 β hβ f⟫_ℝ ≤
      M * ∫ ω, (K (mulBdd f f) ω - 2 * f ω * K f ω + f ω ^ 2) ∂μ := by
    rw [inner_eq_integral, ← integral_const_mul]
    refine integral_mono_ae ((Lp.memLp _).integrable_mul (Lp.memLp _)) (iψ.const_mul M) ?_
    filter_upwards [hψ, hψ0, hz0, hzM] with ω a b c d
    rw [a]
    nlinarith
  have s2 : ∫ ω, (K (mulBdd f f) ω - 2 * f ω * K f ω + f ω ^ 2) ∂μ =
      ∫ ω, K (mulBdd f f) ω ∂μ - 2 * ∫ ω, f ω * K f ω ∂μ + ∫ ω, f ω * f ω ∂μ := by
    have e : (fun ω => K (mulBdd f f) ω - 2 * f ω * K f ω + f ω ^ 2) =
        fun ω => (K (mulBdd f f) ω - 2 * (f ω * K f ω)) + f ω * f ω := by
      ext ω; ring
    have i0 : Integrable (fun ω => K (mulBdd f f) ω) μ := hK.1
    have i2 : Integrable (fun ω => 2 * (f ω * K f ω)) μ := ifK.const_mul 2
    have i1 : Integrable (fun ω => K (mulBdd f f) ω - 2 * (f ω * K f ω)) μ := i0.sub i2
    rw [e, integral_add i1 iff, integral_sub i0 i2, integral_const_mul]
  have s3 : ∫ ω, K (mulBdd f f) ω ∂μ ≤ ∫ ω, f ω * f ω ∂μ :=
    hK.2.trans (le_of_eq (integral_congr_ae hff))
  have s4 : D.form.approxForm D.closed β hβ f f =
      β * (∫ ω, f ω * f ω ∂μ - ∫ ω, f ω * K f ω ∂μ) := by
    rw [QuadForm.approxForm_apply, ← D.sres_eq, inner_sub_left, inner_eq_integral,
      inner_eq_integral]
    congr 2
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    ring
  rw [s4]
  rw [s2] at s1
  have hb := mul_le_mul_of_nonneg_left s1 hβ.le
  nlinarith [mul_le_mul_of_nonneg_left s3 (mul_nonneg hβ.le hM)]

/-- Polarization of a symmetric continuous bilinear form. -/
theorem polar_of_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ a b, B a b = B b a) (a b : E) :
    (4⁻¹ : ℝ) * (B (a + b) (a + b) - B (a - b) (a - b)) = B a b := by
  simp only [map_add, map_sub, FunLike.coe_add, FunLike.coe_sub, Pi.add_apply, Pi.sub_apply]
  rw [hB b a]
  ring

/--
Convergence of the approximating forms to ℰ, in bilinear form, along β = n + 1
(`tendsto_approxForm`, by polarization).
-/
theorem tendsto_approxForm_ener (x y : D.Space) :
    Tendsto (fun n : ℕ => D.form.approxForm D.closed (QuadForm.resolventParameter n)
      (QuadForm.resolventParameter_pos n) (D.toLp x) (D.toLp y)) atTop (𝓝 (D.ener x y)) := by
  have hdiag : ∀ w : D.Space, Tendsto (fun n : ℕ => D.form.approxForm D.closed
      (QuadForm.resolventParameter n) (QuadForm.resolventParameter_pos n) (D.toLp w) (D.toLp w))
      atTop (𝓝 (D.ener w w)) := by
    intro w
    rw [D.ener_apply]
    exact D.form.tendsto_approxForm D.closed (D.form.formToDomain w)
  have h := ((hdiag (x + y)).sub (hdiag (x - y))).const_mul (4⁻¹ : ℝ)
  rw [polar_of_symm D.ener D.ener_symm x y] at h
  refine h.congr fun n => ?_
  rw [map_add, map_sub]
  exact polar_of_symm _ (QuadForm.approxForm_symm _ _ _ _) _ _

end Approx

/-! ## E. BH proposition 4.1.1 -/

section Prop411

/-- Approximating forms: the chain of inequalities in 4.1.1 at parameter β. -/
theorem approx_chain (β : ℝ) (hβ : 0 < β) {x y z : D.Space} (hx : x ∈ D.bddSpace)
    (hy : y ∈ D.bddSpace) (hz : z ∈ D.bddSpace) {F : ℝ → ℝ} (hF : LipschitzWith 1 F)
    (h0 : F 0 = 0) (hyx : ∀ᵐ ω ∂μ, D.toLp y ω = F (D.toLp x ω)) {M : ℝ} (hM : 0 ≤ M)
    (hz0 : ∀ᵐ ω ∂μ, 0 ≤ D.toLp z ω) (hzM : ∀ᵐ ω ∂μ, D.toLp z ω ≤ M) :
    0 ≤ 2 * D.form.approxForm D.closed β hβ (D.toLp (D.mulS y z)) (D.toLp y) -
        D.form.approxForm D.closed β hβ (D.toLp z) (D.toLp (D.mulS y y)) ∧
    2 * D.form.approxForm D.closed β hβ (D.toLp (D.mulS y z)) (D.toLp y) -
        D.form.approxForm D.closed β hβ (D.toLp z) (D.toLp (D.mulS y y)) ≤
      2 * D.form.approxForm D.closed β hβ (D.toLp (D.mulS x z)) (D.toLp x) -
        D.form.approxForm D.closed β hβ (D.toLp z) (D.toLp (D.mulS x x)) ∧
    2 * D.form.approxForm D.closed β hβ (D.toLp (D.mulS x z)) (D.toLp x) -
        D.form.approxForm D.closed β hβ (D.toLp z) (D.toLp (D.mulS x x)) ≤
      2 * M * D.form.approxForm D.closed β hβ (D.toLp x) (D.toLp x) := by
  rw [D.approx_identity β hβ hx hz, D.approx_identity β hβ hy hz]
  obtain ⟨C, hC⟩ := hx
  obtain ⟨C', hC'⟩ := hy
  have hz0' : 0 ≤ D.toLp z := (Lp.coeFn_nonneg _).1 hz0
  refine ⟨?_, ?_, D.inner_psi_le β hβ ⟨C, hC⟩ hM hz0 hzM⟩
  · have hp : 0 ≤ D.psiL2 β hβ (D.toLp y) := by
      refine (Lp.coeFn_nonneg _).1 ?_
      filter_upwards [D.coeFn_psiL2 β hβ hC', D.psi_nonneg β hβ hC'] with ω h1 h2
      rw [Pi.zero_apply, h1]; exact h2
    exact mul_nonneg hβ.le (lp_inner_nonneg hz0' hp)
  · have hp : 0 ≤ D.psiL2 β hβ (D.toLp x) - D.psiL2 β hβ (D.toLp y) := by
      refine (Lp.coeFn_nonneg _).1 ?_
      filter_upwards [Lp.coeFn_sub (D.psiL2 β hβ (D.toLp x)) (D.psiL2 β hβ (D.toLp y)),
        D.coeFn_psiL2 β hβ hC, D.coeFn_psiL2 β hβ hC', D.psi_le β hβ hC hC' hF h0 hyx]
        with ω h1 h2 h3 h4
      rw [Pi.zero_apply, h1, Pi.sub_apply, h2, h3]
      linarith
    have h := lp_inner_nonneg hz0' hp
    rw [inner_sub_right] at h
    nlinarith

/--
BH 1991, ch. I § 4.1, proposition 4.1.1 (p. 17). BH gives it as a direct consequence of proposition
2.3.3 (semigroup); the proof here uses the approximating resolvent forms, for every form in this
framework (arbitrary μ, domain not assumed dense). The norm ‖h‖_{L^∞} is represented by a bound M ≥
0 for h.

Let h ∈ 𝔻 ∩ L^∞ with 0 ≤ h ≤ M a.e., f ∈ 𝔻 ∩ L^∞, F a normal contraction and g = F ∘ f. Then 0 ≤
ℰ(gh, g) − ½ ℰ(h, g²) ≤ ℰ(fh, f) − ½ ℰ(h, f²) ≤ M ℰ(f).
-/
theorem bh_4_1_1 {x y z : D.Space} (hx : x ∈ D.bddSpace) (hz : z ∈ D.bddSpace) {M : ℝ}
    (hM : 0 ≤ M) (hz0 : ∀ᵐ ω ∂μ, 0 ≤ D.toLp z ω) (hzM : ∀ᵐ ω ∂μ, D.toLp z ω ≤ M)
    {F : ℝ → ℝ} (hF : LipschitzWith 1 F) (h0 : F 0 = 0)
    (hyx : ∀ᵐ ω ∂μ, D.toLp y ω = F (D.toLp x ω)) :
    0 ≤ D.ener (D.mulS y z) y - 2⁻¹ * D.ener z (D.mulS y y) ∧
    D.ener (D.mulS y z) y - 2⁻¹ * D.ener z (D.mulS y y) ≤
      D.ener (D.mulS x z) x - 2⁻¹ * D.ener z (D.mulS x x) ∧
    D.ener (D.mulS x z) x - 2⁻¹ * D.ener z (D.mulS x x) ≤ M * D.ener x x := by
  have hy : y ∈ D.bddSpace := by
    obtain ⟨C, hC⟩ := hx
    refine ⟨C, ?_⟩
    filter_upwards [hyx, hC] with ω h1 h2
    rw [h1]
    have h := hF.dist_le_mul (D.toLp x ω) 0
    simp only [h0, Real.dist_eq, sub_zero, NNReal.coe_one, one_mul] at h
    exact h.trans h2
  set b := QuadForm.resolventParameter with hb
  have hbp := QuadForm.resolventParameter_pos
  have L : ∀ u v w : D.Space, Tendsto (fun n : ℕ =>
      2 * D.form.approxForm D.closed (b n) (hbp n) (D.toLp u) (D.toLp v) -
        D.form.approxForm D.closed (b n) (hbp n) (D.toLp w) (D.toLp (D.mulS v v)))
      atTop (𝓝 (2 * D.ener u v - D.ener w (D.mulS v v))) := fun u v w =>
    ((D.tendsto_approxForm_ener u v).const_mul 2).sub (D.tendsto_approxForm_ener w (D.mulS v v))
  have Ly := L (D.mulS y z) y z
  have Lx := L (D.mulS x z) x z
  have Lxx := (D.tendsto_approxForm_ener x x).const_mul (2 * M)
  have c := fun n : ℕ => D.approx_chain (b n) (hbp n) hx hy hz hF h0 hyx hM hz0 hzM
  have i1 : 0 ≤ 2 * D.ener (D.mulS y z) y - D.ener z (D.mulS y y) :=
    ge_of_tendsto Ly (Eventually.of_forall fun n => (c n).1)
  have i2 : 2 * D.ener (D.mulS y z) y - D.ener z (D.mulS y y) ≤
      2 * D.ener (D.mulS x z) x - D.ener z (D.mulS x x) :=
    le_of_tendsto_of_tendsto' Ly Lx fun n => (c n).2.1
  have i3 : 2 * D.ener (D.mulS x z) x - D.ener z (D.mulS x x) ≤ 2 * M * D.ener x x :=
    le_of_tendsto_of_tendsto' Lx Lxx fun n => (c n).2.2
  refine ⟨by linarith, by linarith, by linarith⟩

end Prop411

end DirichletForm
end ErrorCalculus.Capacity
