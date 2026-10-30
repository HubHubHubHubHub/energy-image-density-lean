import ErrorCalculus.Dirichlet.FiniteEnergyMeasure
import ErrorCalculus.Dirichlet.CapacityExamples
import ErrorCalculus.Dirichlet.GeneratorComposition
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-!
# bounded density, generator connection, Lipschitz (O), the zero error structure (BH 1991, ch. I §
9.1–9.2)

## Main results
Measures with bounded density with respect to μ: finite energy (definition 9.2.2, p. 63) and
distribution ι(ρ), ι : L² → 𝔻' (consistency of propositions 9.1.2 and 9.2.1); connection of (I −
A) in the form sense (proposition 9.1.3 a), p. 62) to the generator of library error structures, in
one
direction; hypothesis (O) on a metric space whenever Lipschitz functions taking values in [0, 1]
belong to 𝔻 (in the spirit) of the proof of 9.2.3, p. 64); non-vacuity of bounded (E₂) and (O) for
the zero error structure (a degenerate instance; the nondegenerate instance is in
`FiniteEnergyControls`).
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000

namespace ErrorCalculus.Capacity
namespace DirichletForm

/-! ## D. Controls: measures with bounded density, hypothesis (O) from Lipschitz functions -/

section Density
variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
  {μ : Measure Ω} (D : DirichletForm μ)

omit [OpensMeasurableSpace Ω] in
/-- ∫ φ d(ρ·μ) = (r, x)_{L²} if r represents ρ and φ represents x. -/
theorem integral_withDensity_eq_inner {ρ : Ω → ℝ≥0} (hρ : Measurable ρ) {r : Lp ℝ 2 μ}
    (hr : ⇑r =ᵐ[μ] fun ω => (ρ ω : ℝ)) {x : D.Space} {φ : Ω → ℝ} (h : D.BddContRep x φ) :
    ∫ ω, φ ω ∂(μ.withDensity fun ω => (ρ ω : ℝ≥0∞)) = ⟪r, D.toLp x⟫_ℝ := by
  rw [integral_withDensity_eq_integral_smul hρ, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hr, h.2.2] with ω h1 h2
  rw [h1, h2, NNReal.smul_def, smul_eq_mul]
  simp [RCLike.inner_apply, mul_comm]

omit [OpensMeasurableSpace Ω] in
/--
An example for BH 1991, ch. I § 9.2, definition 9.2.2 (p. 63): a measure with bounded density with
respect to μ (finite μ) has finite energy.

If μ is finite and ρ is measurable and bounded, then ρ·μ is a positive finite-energy measure.
-/
theorem isFiniteEnergy_withDensity [IsFiniteMeasure μ] {ρ : Ω → ℝ≥0} (hρ : Measurable ρ)
    {M : ℝ≥0} (hM : ∀ ω, ρ ω ≤ M) :
    D.IsFiniteEnergy (μ.withDensity fun ω => (ρ ω : ℝ≥0∞)) := by
  have hmem : MemLp (fun ω => (ρ ω : ℝ)) 2 μ :=
    MemLp.of_bound hρ.coe_nnreal_real.aestronglyMeasurable M
      (ae_of_all _ fun ω => by simpa using hM ω)
  refine ⟨isFiniteMeasure_withDensity ?_, ‖hmem.toLp _‖, fun x φ h => ?_⟩
  · refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun ω => ENNReal.coe_le_coe.2 (hM ω)) ?_)
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ _)
  · rw [D.integral_withDensity_eq_inner hρ (MemLp.coeFn_toLp hmem) h]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (D.norm_toLp_le x) (norm_nonneg _))

/--
consistency check between BH 1991, ch. I § 9.1, proposition 9.1.2 (p. 61) and § 9.2, proposition
9.2.1 (p. 63): the distribution of ρ·μ is the image of ρ ∈ L² in 𝔻'.

Under bounded (E₂), T_{ρ·μ} = ι(ρ), ι : L² → 𝔻'.
-/
theorem toDist_withDensity [IsFiniteMeasure μ] (hd : D.BddContDense) {ρ : Ω → ℝ≥0}
    (hρ : Measurable ρ) {M : ℝ≥0} (hM : ∀ ω, ρ ω ≤ M) {r : Lp ℝ 2 μ}
    (hr : ⇑r =ᵐ[μ] fun ω => (ρ ω : ℝ)) :
    D.toDist (μ.withDensity fun ω => (ρ ω : ℝ≥0∞)) = D.ofLp r :=
  (D.toDist_unique hd (D.isFiniteEnergy_withDensity hρ hM) fun x φ h => by
    rw [ofLp_apply, D.integral_withDensity_eq_inner hρ hr h]).symm

end Density

section Raccord
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The inner product of 𝔻: (x, y)_𝔻 = (x, y)_{L²} + ℰ(x, y). -/
theorem inner_space_eq (D : DirichletForm μ) (x y : D.Space) :
    ⟪x, y⟫_ℝ = ⟪D.toLp x, D.toLp y⟫_ℝ + D.form.E (D.form.formToDomain x) (D.form.formToDomain y) :=
  rfl

/--
connection of BH 1991, ch. I § 9.1, proposition 9.1.3 a) (p. 62) to the generator of library error
structures (`ErrorStructure.generator`, the "energy identity" statement): (I − A)x = h in the form
sense means x ∈ D(A) and Ax = x − h.

For an error structure, if x ∈ D(A) and (I − A)x = h in the form sense, then x lies in the library
generator's domain and A x = x − h.
-/
theorem isResolvent_ofErrorStructure (S : ErrorStructure Ω μ) {x : (ofErrorStructure S).Space}
    {h : Lp ℝ 2 μ} (hx : (ofErrorStructure S).IsResolvent x h) :
    ∃ hw : (ofErrorStructure S).toLp x ∈ S.generatorDom,
      S.generator ⟨_, hw⟩ = (ofErrorStructure S).toLp x - h := by
  have he : ∀ z : S.dom, S.energy.E ((ofErrorStructure S).form.formToDomain x) z =
      -⟪(ofErrorStructure S).toLp x - h, (z : Lp ℝ 2 μ)⟫_ℝ := by
    intro z
    have h1 := hx ((ofErrorStructure S).form.formToDomain.symm z)
    rw [inner_space_eq, LinearEquiv.apply_symm_apply] at h1
    have h2 : (ofErrorStructure S).toLp ((ofErrorStructure S).form.formToDomain.symm z) =
        (z : Lp ℝ 2 μ) := by
      rw [toLp_apply, LinearEquiv.apply_symm_apply]
    rw [h2] at h1
    rw [inner_sub_left]
    change ⟪(ofErrorStructure S).toLp x, (z : Lp ℝ 2 μ)⟫_ℝ +
      S.energy.E ((ofErrorStructure S).form.formToDomain x) z = ⟪h, (z : Lp ℝ 2 μ)⟫_ℝ at h1
    linarith
  exact ⟨S.mem_generatorDom_of_energy_identity _ _ he, S.generator_of_energy_identity _ _ he _⟩

end Raccord

section Lipschitz
variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] {ν : Measure X}
  (E : DirichletForm ν)

omit [MeasurableSpace X] in
/-- The function min(p · dist(·, s), 1) is p-Lipschitz for a natural number p. -/
theorem lipschitzWith_mul_infDist (s : Set X) (p : ℕ) :
    LipschitzWith (p : ℝ≥0) fun ω => min ((p : ℝ) * Metric.infDist ω s) 1 := by
  refine LipschitzWith.min_const (LipschitzWith.of_dist_le_mul fun a b => ?_) 1
  have h := (Metric.lipschitz_infDist_pt s).dist_le_mul a b
  rw [Real.dist_eq] at h ⊢
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg p)]
  simp only [NNReal.coe_natCast, NNReal.coe_one, one_mul] at h ⊢
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg p)

/--
sufficient condition for hypothesis (O) on a metric space — in the spirit of the proof of BH 9.2.3,)
(p. 64: "since Ω is a metric space, there exists an increasing sequence (kₚ) …").

If every Lipschitz function taking values in [0, 1] has its class in 𝔻, then (O) holds.
-/
theorem openApprox_of_lipschitz
    (hlip : ∀ (φ : X → ℝ) (K : ℝ≥0), LipschitzWith K φ → (∀ ω, 0 ≤ φ ω ∧ φ ω ≤ 1) →
      ∃ x : E.Space, ⇑(E.toLp x) =ᵐ[ν] φ) :
    E.OpenApprox := by
  intro G hG
  by_cases hc : (Gᶜ).Nonempty
  · set k : ℕ → X → ℝ := fun p ω => min ((p : ℝ) * Metric.infDist ω Gᶜ) 1 with hkdef
    have hk01 : ∀ p ω, 0 ≤ k p ω ∧ k p ω ≤ 1 := fun p ω =>
      ⟨le_min (mul_nonneg (Nat.cast_nonneg p) Metric.infDist_nonneg) zero_le_one,
        min_le_right _ _⟩
    have hx : ∀ p, ∃ x : E.Space, ⇑(E.toLp x) =ᵐ[ν] k p := fun p =>
      hlip (k p) p (lipschitzWith_mul_infDist Gᶜ p) (hk01 p)
    choose x hx using hx
    refine ⟨x, k, fun p => ⟨(lipschitzWith_mul_infDist Gᶜ p).continuous, ⟨1, fun ω => ?_⟩, hx p⟩,
      fun p ω => (hk01 p ω).1, fun p ω => (hk01 p ω).2, fun p ω hω => ?_, fun ω hω => ?_⟩
    · rw [abs_of_nonneg (hk01 p ω).1]
      exact (hk01 p ω).2
    · have h0 : Metric.infDist ω Gᶜ = 0 := Metric.infDist_zero_of_mem hω
      simp [hkdef, h0]
    · have hpos : 0 < Metric.infDist ω Gᶜ :=
        (IsClosed.notMem_iff_infDist_pos hG.isClosed_compl hc).1 (fun h => h hω)
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / Metric.infDist ω Gᶜ)
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun p hp => ?_⟩)
      have h1 : 1 ≤ (p : ℝ) * Metric.infDist ω Gᶜ := by
        have hNp : (N : ℝ) ≤ p := by exact_mod_cast hp
        have h2 : 1 / Metric.infDist ω Gᶜ < p := lt_of_lt_of_le hN hNp
        rw [div_lt_iff₀ hpos] at h2
        linarith
      show (1 : ℝ) = min ((p : ℝ) * Metric.infDist ω Gᶜ) 1
      rw [min_eq_right h1]
  · have hG' : G = Set.univ := by
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hc
      exact hc
    obtain ⟨x1, hx1⟩ := hlip (fun _ => 1) 0 (LipschitzWith.const 1) fun _ => ⟨zero_le_one, le_rfl⟩
    refine ⟨fun _ => x1, fun _ _ => 1, fun _ => ⟨continuous_const, ⟨1, fun _ => by simp⟩, hx1⟩,
      fun _ _ => zero_le_one, fun _ _ => le_rfl, fun p ω hω => ?_, fun ω _ => tendsto_const_nhds⟩
    exact absurd (hG' ▸ Set.mem_univ ω) hω

end Lipschitz

end DirichletForm
end ErrorCalculus.Capacity

namespace ErrorCalculus.Capacity
namespace DirichletForm

/-! ## E. Non-vacuity control: the zero error structure on a metric space -/

section ZeroStructure
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {ν : Measure X}
  [IsProbabilityMeasure ν]

omit [MetricSpace X] [BorelSpace X] in
/-- For the zero structure, ‖x‖_𝔻 = ‖x‖_{L²}. -/
theorem norm_ofErrorStructure_zero
    (x : (ofErrorStructure (ErrorStructure.zero (Ω := X) (μ := ν))).Space) :
    ‖x‖ = ‖(ofErrorStructure (ErrorStructure.zero (Ω := X) (μ := ν))).toLp x‖ := by
  have h := DirichletForm.norm_sq_eq _ x
  have hE : (ofErrorStructure (ErrorStructure.zero (Ω := X) (μ := ν))).form.E
      ((ofErrorStructure (ErrorStructure.zero (Ω := X) (μ := ν))).form.formToDomain x)
      ((ofErrorStructure (ErrorStructure.zero (Ω := X) (μ := ν))).form.formToDomain x) = 0 :=
    ErrorStructure.zeroData_energy _ _
  rw [hE, add_zero] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/--
non-vacuity control for the hypotheses of 9.2.3–9.2.4 (BH 1991, ch. I § 9.2, (E₂), p. 63): for the
zero error structure on a Borel metric probability space, bounded (E₂) and (O) hold.

Zero structure (𝔻 = L²(ν)) on a metric space: 𝒞_b ∩ 𝔻 is dense in 𝔻 and (O) holds.
-/
theorem hypotheses_ofErrorStructure_zero :
    (ofErrorStructure (ErrorStructure.zero (Ω := X) (μ := ν))).BddContDense ∧
      (ofErrorStructure (ErrorStructure.zero (Ω := X) (μ := ν))).OpenApprox := by
  set D := ofErrorStructure (ErrorStructure.zero (Ω := X) (μ := ν))
  constructor
  · rw [BddContDense, Metric.dense_iff]
    intro x r hr
    have hL := Lp.boundedContinuousFunction_dense ℝ ν (p := 2) ENNReal.ofNat_ne_top
    obtain ⟨g, hgball, hgS⟩ := Metric.dense_iff.1 hL (D.toLp x) r hr
    have hgdom : g ∈ D.form.dom := Submodule.mem_top
    refine ⟨D.form.formToDomain.symm ⟨g, hgdom⟩, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, norm_ofErrorStructure_zero, map_sub]
      have hg : D.toLp (D.form.formToDomain.symm ⟨g, hgdom⟩) = g := rfl
      rw [hg, ← dist_eq_norm]
      exact hgball
    · obtain ⟨f₀, hf₀⟩ := Lp.mem_boundedContinuousFunction_iff.1 hgS
      have hrep : ⇑g =ᵐ[ν] ⇑f₀ := by
        have h := ContinuousMap.coeFn_toAEEqFun ν f₀.toContinuousMap
        rw [hf₀] at h
        exact h
      exact ⟨f₀, f₀.continuous, ⟨‖f₀‖, fun ω => by
        rw [← Real.norm_eq_abs]; exact f₀.norm_coe_le_norm ω⟩, hrep⟩
  · refine openApprox_of_lipschitz D fun φ K hφ h01 => ?_
    have hmem : MemLp φ 2 ν :=
      MemLp.of_bound hφ.continuous.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h01 ω).1]
        exact (h01 ω).2)
    have hdom : hmem.toLp φ ∈ D.form.dom := Submodule.mem_top
    exact ⟨D.form.formToDomain.symm ⟨hmem.toLp φ, hdom⟩, MemLp.coeFn_toLp hmem⟩

end ZeroStructure

end DirichletForm
end ErrorCalculus.Capacity
