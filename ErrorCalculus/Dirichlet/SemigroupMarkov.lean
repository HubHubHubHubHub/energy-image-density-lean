import ErrorCalculus.Dirichlet.SemigroupGenerator
import ErrorCalculus.Dirichlet.ResolventMarkov
import ErrorCalculus.Dirichlet.Calculus
import Mathlib.Topology.Algebra.InfiniteSum.Order

noncomputable section
open Filter Topology MeasureTheory
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Scalar order on L², proved on representatives. -/
theorem smul_le_smul_Lp {c : ℝ} (hc : 0 ≤ c) {f g : Lp ℝ 2 μ} (h : f ≤ g) :
    c • f ≤ c • g := by
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [Lp.coeFn_smul c f, Lp.coeFn_smul c g, (Lp.coeFn_le f g).mpr h]
    with ω hf hg hω
  simpa only [hf, hg, Pi.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left hω hc

theorem smul_nonneg_Lp {c : ℝ} (hc : 0 ≤ c) {f : Lp ℝ 2 μ} (hf : 0 ≤ f) :
    0 ≤ c • f := by
  simpa only [smul_zero] using smul_le_smul_Lp hc hf

/-- The order interval is closed in L². Mathlib's instance uses an a.e. subsequence. -/
theorem isClosed_Lp_unitInterval [IsFiniteMeasure μ] :
    IsClosed (Set.Icc (0 : Lp ℝ 2 μ) (Lp.const 2 μ 1)) := isClosed_Icc

/-- The exponential series evaluated at a vector, with scalar nonnegative weights. -/
theorem hasSum_exp_apply_Lp (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (a : ℝ) (f : Lp ℝ 2 μ) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ * a^n) • ((T^n) f))
      (NormedSpace.exp (a • T) f) := by
  have hh := (ContinuousLinearMap.apply ℝ (Lp ℝ 2 μ) f).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (a • T))
  simpa only [ContinuousLinearMap.apply_apply, smul_pow, smul_apply, smul_smul] using hh

/-- A positive operator has a positive exponential at nonnegative times. -/
theorem exp_apply_nonneg_Lp (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f, 0 ≤ f → 0 ≤ T f) {a : ℝ} (ha : 0 ≤ a) {f : Lp ℝ 2 μ} (hf : 0 ≤ f) :
    0 ≤ NormedSpace.exp (a • T) f := by
  have hp (n : ℕ) : 0 ≤ (T^n) f := by
    induction n with
    | zero => simpa using hf
    | succ n ih => simpa only [pow_succ', mul_apply_eq_comp] using hT _ ih
  apply hasSum_le (g := fun n : ℕ => ((n.factorial : ℝ)⁻¹ * a^n) • ((T^n) f))
    (fun n => smul_nonneg_Lp (by positivity) (hp n)) hasSum_zero
    (hasSum_exp_apply_Lp T a f)

/-- Iterated Markov bounds pass through the exponential series using closed order. -/
theorem exp_apply_le_Lp (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (c : Lp ℝ 2 μ)
    (hT : ∀ f, 0 ≤ f → f ≤ c → 0 ≤ T f ∧ T f ≤ c)
    {a : ℝ} (ha : 0 ≤ a) {f : Lp ℝ 2 μ} (hf : 0 ≤ f) (hf' : f ≤ c) :
    0 ≤ NormedSpace.exp (a • T) f ∧ NormedSpace.exp (a • T) f ≤ Real.exp a • c := by
  have hp (n : ℕ) : 0 ≤ (T^n) f ∧ (T^n) f ≤ c := by
    induction n with
    | zero => simpa using And.intro hf hf'
    | succ n ih => simpa only [pow_succ', mul_apply_eq_comp] using hT _ ih.1 ih.2
  have hs := hasSum_exp_apply_Lp T a f
  have hr : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * a^n) (Real.exp a) := by
    simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a
  constructor
  · exact hasSum_le (fun n => smul_nonneg_Lp (by positivity) (hp n).1) hasSum_zero hs
  · exact hasSum_le (fun n => smul_le_smul_Lp (by positivity) (hp n).2) hs (hr.smul_const c)

namespace ErrorStructure
variable [IsProbabilityMeasure μ] (S : ErrorStructure Ω μ)

/-- Each bounded Yosida semigroup preserves the unit order interval. -/
theorem semigroupApprox_markov_order {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t)
    (f : Lp ℝ 2 μ) (h₀ : 0 ≤ f) (h₁ : f ≤ Lp.const 2 μ 1) :
    0 ≤ (S.energy.formResolvent S.energy_closed S.dense).semigroupApprox b t f ∧
      (S.energy.formResolvent S.energy_closed S.dense).semigroupApprox b t f ≤ Lp.const 2 μ 1 := by
  rw [Foundations.ContractionResolvent.semigroupApprox_factor,
    S.energy.formResolvent_G S.energy_closed S.dense hb, smul_apply]
  have hh := exp_apply_le_Lp (b • S.resolvent b hb) (Lp.const 2 μ 1)
    (fun f h₀ h₁ => S.resolvent_markov_order b hb f h₀ h₁) (mul_nonneg ht hb.le) h₀ h₁
  refine ⟨smul_nonneg_Lp (Real.exp_pos _).le hh.1, ?_⟩
  have hu := smul_le_smul_Lp (Real.exp_pos (-(t*b))).le hh.2
  simpa only [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul, resolvent] using hu

/-- Closedness of the L² order interval transfers the Markov bounds to the limiting semigroup. -/
theorem semigroup_markov_order {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 μ)
    (h₀ : 0 ≤ f) (h₁ : f ≤ Lp.const 2 μ 1) :
    0 ≤ S.semigroup t f ∧ S.semigroup t f ≤ Lp.const 2 μ 1 := by
  apply (isClosed_Lp_unitInterval (μ := μ)).mem_of_tendsto
    ((S.energy.formResolvent S.energy_closed S.dense).tendsto_semigroupApprox_apply ht f)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  exact S.semigroupApprox_markov_order hb ht f h₀ h₁

/-- The semigroup is Markov on almost-everywhere representatives. -/
theorem semigroup_markov {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ ω ∂μ, 0 ≤ f ω ∧ f ω ≤ 1) :
    ∀ᵐ ω ∂μ, 0 ≤ (S.semigroup t f) ω ∧ (S.semigroup t f) ω ≤ 1 := by
  have h₀ := (Lp.coeFn_nonneg f).mp (hf.mono fun _ h => h.1)
  have h₁ : f ≤ Lp.const 2 μ 1 := by
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [hf, Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with ω h hc
    simpa only [hc, Function.const_apply] using h.2
  have hh := S.semigroup_markov_order ht f h₀ h₁
  filter_upwards [(Lp.coeFn_nonneg _).mpr hh.1, (Lp.coeFn_le _ _).mpr hh.2,
    Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with ω h₀ h₁ hc
  exact ⟨h₀, by simpa only [hc, Function.const_apply] using h₁⟩

/-- positivity also holds for unbounded nonnegative L² data. -/
theorem semigroup_nonneg {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ ω ∂μ, 0 ≤ f ω) : ∀ᵐ ω ∂μ, 0 ≤ (S.semigroup t f) ω := by
  apply (Lp.coeFn_nonneg _).mpr
  apply ge_of_tendsto ((S.energy.formResolvent S.energy_closed S.dense).tendsto_semigroupApprox_apply ht f)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  rw [Foundations.ContractionResolvent.semigroupApprox_factor,
    S.energy.formResolvent_G S.energy_closed S.dense hb, smul_apply]
  apply smul_nonneg_Lp (Real.exp_pos _).le
  apply exp_apply_nonneg_Lp (b • S.resolvent b hb) _ (mul_nonneg ht hb.le)
    ((Lp.coeFn_nonneg f).mp hf)
  intro g hg
  exact smul_nonneg_Lp hb.le ((Lp.coeFn_nonneg _).mp
    (S.resolvent_nonneg b hb g ((Lp.coeFn_nonneg g).mpr hg)))

/-- The unit is fixed by the resolvent at parameter one. -/
theorem resolvent_const_one : S.resolvent 1 zero_lt_one (Lp.const 2 μ 1) = Lp.const 2 μ 1 := by
  have he := S.energy.resolvent_unique S.energy_closed 1 zero_lt_one (Lp.const 2 μ 1)
    (S.const 1) (by
      intro v
      have hz : S.energy.E (S.const 1) v = 0 := by
        rw [ErrorData.energy_apply, S.gamma_const]
        rw [integral_congr_ae (Lp.coeFn_zero ℝ 1 μ)]
        simp
      rw [hz]
      simp only [zero_add, one_mul]
      rfl)
  exact (congrArg (fun v : S.dom => (v : Lp ℝ 2 μ)) he).symm

/-- Constants are conservative for an error structure. -/
theorem semigroup_const_one {t : ℝ} (ht : 0 ≤ t) :
    S.semigroup t (Lp.const 2 μ 1) = Lp.const 2 μ 1 := by
  let R := S.energy.formResolvent S.energy_closed S.dense
  have he : R.G 1 (Lp.const 2 μ 1) = Lp.const 2 μ 1 := by
    simpa only [R, S.energy.formResolvent_G S.energy_closed S.dense zero_lt_one, resolvent] using
      S.resolvent_const_one
  let u : R.dom := ⟨R.G 1 (Lp.const 2 μ 1), R.mem_dom_G zero_lt_one _⟩
  have hA : R.generator u = 0 := by
    rw [R.generator_G_one, he, sub_self]
  have hi := R.semigroup_sub_eq_integral ht u
  simp only [hA, map_zero, intervalIntegral.integral_zero] at hi
  exact sub_eq_zero.mp (by simpa only [u, he, semigroup, QuadForm.semigroup, R] using hi)

end ErrorStructure
end ErrorCalculus
