import ErrorCalculus.Dirichlet.ApproximatingForm
import ErrorCalculus.Dirichlet.DirichletProperty

noncomputable section
open MeasureTheory
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- The resolvent of the closed energy form of an error structure. -/
def resolvent (β : ℝ) (hβ : 0 < β) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  S.energy.resolvent S.energy_closed β hβ

/--
a normal contraction fixing the datum fixes the scaled resolvent. The norm comparison is
pointwise, while uniqueness is in the form domain.
-/
theorem resolvent_fixed_of_normal_contraction (β : ℝ) (hβ : 0 < β)
    (f : Lp ℝ 2 μ) {F : ℝ → ℝ} (hF : LipschitzWith 1 F)
    (hf : ∀ᵐ ω ∂μ, F (f ω) = f ω) (w : Lp ℝ 2 μ)
    (hw : ⇑w =ᵐ[μ] fun ω => F ((β • S.resolvent β hβ f) ω)) :
    w = β • S.resolvent β hβ f := by
  let u := S.energy.betaResolventDom S.energy_closed β hβ f
  have hw' : ⇑w =ᵐ[μ] fun ω => F ((u : Lp ℝ 2 μ) ω) := hw
  obtain ⟨hd, hE⟩ := S.normal_contraction hF u w hw'
  have hn : ‖w-f‖ ≤ ‖(u : Lp ℝ 2 μ)-f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hw', hf, Lp.coeFn_sub w f, Lp.coeFn_sub (u : Lp ℝ 2 μ) f] with ω hw hf hs ht
    have hl := hF.dist_le_mul ((u : Lp ℝ 2 μ) ω) (f ω)
    simpa only [hs, ht, Pi.sub_apply, hw, hf, NNReal.coe_one, one_mul,
      Real.dist_eq, Real.norm_eq_abs] using hl
  have he := S.energy.eq_resolvent_of_le S.energy_closed β hβ f ⟨w, hd⟩ (by
    change S.energy.E ⟨w, hd⟩ ⟨w, hd⟩ + β * ‖w-f‖ ^ 2 ≤
      S.energy.E u u + β * ‖(u : Lp ℝ 2 μ)-f‖ ^ 2
    exact add_le_add hE (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hβ.le))
  exact congrArg (fun v : S.energy.dom => (v : Lp ℝ 2 μ)) he

/-- The scaled resolvent preserves the almost-sure unit interval. -/
theorem resolvent_markov (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ ω ∂μ, 0 ≤ f ω ∧ f ω ≤ 1) :
    ∀ᵐ ω ∂μ, 0 ≤ (β • S.resolvent β hβ f) ω ∧ (β • S.resolvent β hβ f) ω ≤ 1 := by
  let u := β • S.resolvent β hβ f
  let w := (0 ⊔ u) ⊓ Lp.const 2 μ 1
  have hw : ⇑w =ᵐ[μ] fun ω => min (max 0 (u ω)) 1 := by
    filter_upwards [Lp.coeFn_inf (0 ⊔ u) (Lp.const 2 μ 1),
      Lp.coeFn_sup (0 : Lp ℝ 2 μ) u, Lp.coeFn_zero ℝ 2 μ,
      Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with ω hi hs hz hc
    simp [w, hi, hs]
  have he : w = u := S.resolvent_fixed_of_normal_contraction β hβ f
    ((LipschitzWith.id.const_max 0).min_const 1)
    (hf.mono fun ω h => by
      change min (max 0 (f ω)) 1 = f ω
      rw [max_eq_right h.1, min_eq_left h.2]) w hw
  rw [he] at hw
  filter_upwards [hw] with ω hω
  change 0 ≤ u ω ∧ u ω ≤ 1
  rw [hω]
  exact ⟨le_min (le_max_left _ _) zero_le_one, min_le_right _ _⟩

/-- The equivalent lattice-order version. -/
theorem resolvent_markov_order (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 μ)
    (h₀ : 0 ≤ f) (h₁ : f ≤ Lp.const 2 μ 1) :
    0 ≤ β • S.resolvent β hβ f ∧ β • S.resolvent β hβ f ≤ Lp.const 2 μ 1 := by
  have hf : ∀ᵐ ω ∂μ, 0 ≤ f ω ∧ f ω ≤ 1 := by
    filter_upwards [(Lp.coeFn_nonneg f).mpr h₀, (Lp.coeFn_le f _).mpr h₁,
      Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with ω ha hb hc
    exact ⟨ha, by simpa using hb⟩
  have hh := S.resolvent_markov β hβ f hf
  constructor
  · exact (Lp.coeFn_nonneg _).mp (hh.mono fun _ h => h.1)
  · apply (Lp.coeFn_le _ _).mp
    filter_upwards [hh, Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with ω h hc
    simpa using h.2

/-- positivity of the unscaled resolvent for nonnegative data. -/
theorem resolvent_nonneg (β : ℝ) (hβ : 0 < β) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ ω ∂μ, 0 ≤ f ω) : ∀ᵐ ω ∂μ, 0 ≤ (S.resolvent β hβ f) ω := by
  let u := β • S.resolvent β hβ f
  have hw : ⇑(Lp.posPart u) =ᵐ[μ] fun ω => max (u ω) 0 := Lp.coeFn_posPart u
  have he : Lp.posPart u = u := S.resolvent_fixed_of_normal_contraction β hβ f
    (LipschitzWith.id.max_const 0) (hf.mono fun ω h => max_eq_left h) _ hw
  rw [he] at hw
  filter_upwards [hw, Lp.coeFn_smul β (S.resolvent β hβ f)] with ω hω hs
  have hn : 0 ≤ u ω := by rw [hω]; exact le_max_right _ _
  change (β • S.resolvent β hβ f) ω = _ at hs
  rw [hs] at hn
  change 0 ≤ β * (S.resolvent β hβ f) ω at hn
  exact nonneg_of_mul_nonneg_right hn hβ

end ErrorCalculus.ErrorStructure
