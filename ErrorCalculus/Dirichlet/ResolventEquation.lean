import ErrorCalculus.Dirichlet.ResolventBasic
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter Topology
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (Q : QuadForm H) (hQ : Q.IsClosed)

/-- The resolvent identity on each vector. -/
theorem resolvent_eq_apply (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (f : H) :
    Q.resolvent hQ α hα f - Q.resolvent hQ β hβ f =
      (β-α) • Q.resolvent hQ α hα (Q.resolvent hQ β hβ f) := by
  have hu := Q.resolvent_unique hQ α hα f
    (Q.resolventDom hQ β hβ f + (β-α) •
      Q.resolventDom hQ α hα (Q.resolvent hQ β hβ f)) (by
        intro v
        have hb := Q.resolvent_spec hQ β hβ f v
        have ha := Q.resolvent_spec hQ α hα (Q.resolvent hQ β hβ f) v
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, Submodule.coe_add, Submodule.coe_smul, coe_resolventDom,
          inner_add_left, real_inner_smul_left]
        nlinarith)
  have hh := congrArg (fun x : Q.dom => (x : H)) hu
  simp only [Submodule.coe_add, Submodule.coe_smul, coe_resolventDom] at hh
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hh.symm)

/-- equality of continuous operators. -/
theorem resolvent_eq (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    Q.resolvent hQ α hα - Q.resolvent hQ β hβ =
      (β-α) • (Q.resolvent hQ α hα).comp (Q.resolvent hQ β hβ) := by
  ext f
  exact Q.resolvent_eq_apply hQ α β hα hβ f

/-- resolvents commute, including coincident parameters. -/
theorem resolvent_comm (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (Q.resolvent hQ α hα).comp (Q.resolvent hQ β hβ) =
      (Q.resolvent hQ β hβ).comp (Q.resolvent hQ α hα) := by
  by_cases he : α = β
  · subst β; rfl
  ext f
  apply smul_right_injective H (sub_ne_zero.mpr (Ne.symm he))
  change (β-α) • Q.resolvent hQ α hα (Q.resolvent hQ β hβ f) =
    (β-α) • Q.resolvent hQ β hβ (Q.resolvent hQ α hα f)
  rw [← Q.resolvent_eq_apply hQ α β hα hβ f]
  have hh := Q.resolvent_eq_apply hQ β α hβ hα f
  calc
    _ = -(Q.resolvent hQ β hβ f - Q.resolvent hQ α hα f) := (neg_sub _ _).symm
    _ = -((α-β) • Q.resolvent hQ β hβ (Q.resolvent hQ α hα f)) := congrArg Neg.neg hh
    _ = _ := by rw [← neg_smul, neg_sub]

/-- The scaled solution as a domain element. -/
def betaResolventDom (β : ℝ) (hβ : 0 < β) (f : H) : Q.dom :=
  β • Q.resolventDom hQ β hβ f

@[simp] theorem coe_betaResolventDom (β : ℝ) (hβ : 0 < β) (f : H) :
    (Q.betaResolventDom hQ β hβ f : H) = β • Q.resolvent hQ β hβ f := rfl

/-- scaled variational identity. -/
theorem beta_resolvent_spec (β : ℝ) (hβ : 0 < β) (f : H) (v : Q.dom) :
    Q.E (Q.betaResolventDom hQ β hβ f) v +
      β * inner ℝ (Q.betaResolventDom hQ β hβ f : H) (v : H) = β * inner ℝ f (v : H) := by
  have hh := Q.resolvent_spec hQ β hβ f v
  simp only [betaResolventDom, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Submodule.coe_smul, coe_resolventDom, real_inner_smul_left]
  nlinarith

/-- The strictly convex minimization functional. -/
def resolventFunctional (β : ℝ) (f : H) (v : Q.dom) : ℝ :=
  Q.E v v + β * ‖(v : H) - f‖ ^ 2

/-- Exact completion of the square, also used in R.4 and A.1. -/
theorem resolventFunctional_identity (β : ℝ) (hβ : 0 < β) (f : H) (v : Q.dom) :
    Q.resolventFunctional β f v =
      Q.resolventFunctional β f (Q.betaResolventDom hQ β hβ f) +
      Q.E (v - Q.betaResolventDom hQ β hβ f) (v - Q.betaResolventDom hQ β hβ f) +
      β * ‖((v - Q.betaResolventDom hQ β hβ f : Q.dom) : H)‖ ^ 2 := by
  let u := Q.betaResolventDom hQ β hβ f
  have hv := Q.beta_resolvent_spec hQ β hβ f v
  have hu := Q.beta_resolvent_spec hQ β hβ f u
  change Q.E u v + β * inner ℝ (u : H) (v : H) = _ at hv
  change Q.E u u + β * inner ℝ (u : H) (u : H) = _ at hu
  change Q.resolventFunctional β f v = Q.resolventFunctional β f u +
    Q.E (v-u) (v-u) + β * ‖((v-u : Q.dom) : H)‖ ^ 2
  simp only [resolventFunctional, map_sub, LinearMap.sub_apply, Submodule.coe_sub,
    ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right]
  rw [Q.symm v u]
  have h₁ : inner ℝ (v : H) (u : H) = inner ℝ (u : H) (v : H) := real_inner_comm _ _
  have h₂ : inner ℝ (v : H) f = inner ℝ f (v : H) := real_inner_comm _ _
  have h₃ : inner ℝ (u : H) f = inner ℝ f (u : H) := real_inner_comm _ _
  rw [h₁, h₂, h₃]
  nlinarith

/-- The scaled resolvent minimizes energy plus squared distance. -/
theorem resolvent_minimizes (β : ℝ) (hβ : 0 < β) (f : H) (v : Q.dom) :
    Q.resolventFunctional β f (Q.betaResolventDom hQ β hβ f) ≤ Q.resolventFunctional β f v := by
  rw [Q.resolventFunctional_identity hQ β hβ f v]
  have hp := Q.nonneg (v-Q.betaResolventDom hQ β hβ f)
  have hn := mul_nonneg hβ.le (sq_nonneg ‖((v-Q.betaResolventDom hQ β hβ f : Q.dom) : H)‖)
  linarith

/-- uniqueness, in the form needed for truncation arguments. -/
theorem eq_resolvent_of_le (β : ℝ) (hβ : 0 < β) (f : H) (v : Q.dom)
    (hv : Q.resolventFunctional β f v ≤ Q.resolventFunctional β f (Q.betaResolventDom hQ β hβ f)) :
    v = Q.betaResolventDom hQ β hβ f := by
  rw [Q.resolventFunctional_identity hQ β hβ f v] at hv
  have hp := Q.nonneg (v-Q.betaResolventDom hQ β hβ f)
  have hz : ‖((v-Q.betaResolventDom hQ β hβ f : Q.dom) : H)‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖((v-Q.betaResolventDom hQ β hβ f : Q.dom) : H)‖]
  apply sub_eq_zero.mp
  exact Subtype.ext (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- The quantitative strong approximation on the domain. -/
theorem beta_norm_sq_beta_resolvent_sub_le (β : ℝ) (hβ : 0 < β) (u : Q.dom) :
    β * ‖β • Q.resolvent hQ β hβ (u : H) - (u : H)‖ ^ 2 ≤ Q.E u u := by
  have hh := Q.resolvent_minimizes hQ β hβ (u : H) u
  simpa only [resolventFunctional, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero, coe_betaResolventDom] using
    (le_add_of_nonneg_left (Q.nonneg (Q.betaResolventDom hQ β hβ (u : H)))).trans hh

/-- strong convergence on the domain along any positive parameters tending to infinity. -/
theorem tendsto_beta_resolvent_dom {ι : Type*} {l : Filter ι} (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) (ht : Tendsto b l atTop) (u : Q.dom) :
    Tendsto (fun i => b i • Q.resolvent hQ (b i) (hb i) (u : H)) l (𝓝 (u : H)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [ht.eventually (eventually_gt_atTop (Q.E u u / ε^2))] with i hi
  rw [dist_eq_norm]
  have hh := Q.beta_norm_sq_beta_resolvent_sub_le hQ (b i) (hb i) u
  have he : Q.E u u < b i * ε^2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hi
  have hn : ‖b i • Q.resolvent hQ (b i) (hb i) (u : H) - (u : H)‖ ^ 2 < ε^2 := by
    nlinarith [hb i]
  nlinarith [norm_nonneg (b i • Q.resolvent hQ (b i) (hb i) (u : H) - (u : H))]

/-- density extends strong convergence to every ambient vector. -/
theorem tendsto_beta_resolvent (hd : Dense (Q.dom : Set H))
    {ι : Type*} {l : Filter ι} (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (ht : Tendsto b l atTop) (f : H) :
    Tendsto (fun i => b i • Q.resolvent hQ (b i) (hb i) f) l (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨u, hu, hfu⟩ := hd.exists_dist_lt f (show 0 < ε/3 by positivity)
  have hh := Metric.tendsto_nhds.mp (Q.tendsto_beta_resolvent_dom hQ b hb ht ⟨u, hu⟩) (ε/3) (by positivity)
  filter_upwards [hh] with i hi
  have hc := Q.norm_beta_resolvent_le hQ (b i) (hb i) (f-u)
  rw [map_sub, smul_sub] at hc
  have htri := norm_add_le (b i • Q.resolvent hQ (b i) (hb i) f - b i • Q.resolvent hQ (b i) (hb i) u)
    (b i • Q.resolvent hQ (b i) (hb i) u - u)
  have htri' := norm_add_le (b i • Q.resolvent hQ (b i) (hb i) f - u) (u-f)
  simp only [sub_add_sub_cancel] at htri htri'
  rw [dist_eq_norm] at hfu hi ⊢
  rw [norm_sub_rev u f] at htri'
  change ‖b i • Q.resolvent hQ (b i) (hb i) u - u‖ < ε/3 at hi
  linarith

/-- The positive integer parameters used in the lower semicontinuity argument. -/
def resolventParameter (n : ℕ) : ℝ := (n : ℝ) + 1

theorem resolventParameter_pos (n : ℕ) : 0 < resolventParameter n := by
  unfold resolventParameter; positivity

theorem tendsto_resolventParameter : Tendsto resolventParameter atTop atTop :=
  tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

end ErrorCalculus.QuadForm
