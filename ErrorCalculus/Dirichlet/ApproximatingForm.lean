import ErrorCalculus.Dirichlet.ResolventEquation
import ErrorCalculus.Dirichlet.LowerSemicontinuous

noncomputable section
open Filter Topology
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (Q : QuadForm H) (hQ : Q.IsClosed)

/-- bounded bilinear approximating form on the entire ambient space. -/
def approxForm (β : ℝ) (hβ : 0 < β) : H →L[ℝ] H →L[ℝ] ℝ :=
  β • (innerSL ℝ).comp (ContinuousLinearMap.id ℝ H - β • Q.resolvent hQ β hβ)

@[simp] theorem approxForm_apply (β : ℝ) (hβ : 0 < β) (f g : H) :
    Q.approxForm hQ β hβ f g = β * inner ℝ (f - β • Q.resolvent hQ β hβ f) g := rfl

/-- symmetry of the approximating form. -/
theorem approxForm_symm (β : ℝ) (hβ : 0 < β) (f g : H) :
    Q.approxForm hQ β hβ f g = Q.approxForm hQ β hβ g f := by
  simp only [approxForm_apply, inner_sub_left, real_inner_smul_left]
  have h₁ := Q.resolvent_symm hQ β hβ f g
  have h₂ : inner ℝ f (Q.resolvent hQ β hβ g) = inner ℝ (Q.resolvent hQ β hβ g) f := real_inner_comm _ _
  have h₃ : inner ℝ f g = inner ℝ g f := real_inner_comm _ _
  rw [h₁, h₂, h₃]

/-- The approximating energy is the minimum of the penalized energy. -/
theorem approxForm_eq_minimum (β : ℝ) (hβ : 0 < β) (f : H) :
    Q.approxForm hQ β hβ f f =
      Q.resolventFunctional β f (Q.betaResolventDom hQ β hβ f) := by
  let u := Q.betaResolventDom hQ β hβ f
  have hh := Q.beta_resolvent_spec hQ β hβ f u
  change Q.E u u + β * inner ℝ (u : H) (u : H) = β * inner ℝ f (u : H) at hh
  change β * inner ℝ (f - (u : H)) f = Q.E u u + β * ‖(u : H)-f‖ ^ 2
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right]
  have hi : inner ℝ (u : H) f = inner ℝ f (u : H) := real_inner_comm _ _
  rw [hi]
  nlinarith

/-- positivity from the nonnegative minimum functional. -/
theorem approxForm_nonneg (β : ℝ) (hβ : 0 < β) (f : H) :
    0 ≤ Q.approxForm hQ β hβ f f := by
  rw [Q.approxForm_eq_minimum hQ β hβ f, resolventFunctional]
  exact add_nonneg (Q.nonneg _) (mul_nonneg hβ.le (sq_nonneg _))

/-- The solution energy is bounded by the approximating energy. -/
theorem energy_beta_resolvent_le_approxForm (β : ℝ) (hβ : 0 < β) (f : H) :
    Q.E (Q.betaResolventDom hQ β hβ f) (Q.betaResolventDom hQ β hβ f) ≤
      Q.approxForm hQ β hβ f f := by
  rw [Q.approxForm_eq_minimum hQ β hβ f, resolventFunctional]
  exact le_add_of_nonneg_right (mul_nonneg hβ.le (sq_nonneg _))

/-- On the domain the approximating form is bounded by the original energy. -/
theorem approxForm_le_energy (β : ℝ) (hβ : 0 < β) (u : Q.dom) :
    Q.approxForm hQ β hβ (u : H) (u : H) ≤ Q.E u u := by
  rw [Q.approxForm_eq_minimum hQ β hβ (u : H)]
  simpa only [resolventFunctional, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero] using Q.resolvent_minimizes hQ β hβ (u : H) u

/-- monotonicity follows by comparison of the two minimum functionals. -/
theorem approxForm_mono (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hab : α ≤ β) (f : H) :
    Q.approxForm hQ α hα f f ≤ Q.approxForm hQ β hβ f f := by
  rw [Q.approxForm_eq_minimum hQ α hα f, Q.approxForm_eq_minimum hQ β hβ f]
  apply (Q.resolvent_minimizes hQ α hα f (Q.betaResolventDom hQ β hβ f)).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hab (sq_nonneg _))

/-- bounded approximating energies on n+1 identify domain membership and energy. -/
theorem mem_dom_energy_le_of_approxForm_bounded (hd : Dense (Q.dom : Set H))
    (f : H) (C : ℝ)
    (hb : ∀ n : ℕ, Q.approxForm hQ (resolventParameter n) (resolventParameter_pos n) f f ≤ C) :
    ∃ hf : f ∈ Q.dom, Q.E ⟨f, hf⟩ ⟨f, hf⟩ ≤ C := by
  apply hQ.mem_dom_of_tendsto_of_energy_le
    (x := fun n => Q.betaResolventDom hQ (resolventParameter n) (resolventParameter_pos n) f)
  · exact Q.tendsto_beta_resolvent hQ hd resolventParameter resolventParameter_pos tendsto_resolventParameter f
  · intro n
    exact (Q.energy_beta_resolvent_le_approxForm hQ _ _ f).trans (hb n)

/-- boundedness for all positive real parameters characterizes the domain. -/
theorem mem_dom_iff_approxForm_bounded (hd : Dense (Q.dom : Set H)) (f : H) :
    f ∈ Q.dom ↔ ∃ C : ℝ, ∀ (β : ℝ) (hβ : 0 < β), Q.approxForm hQ β hβ f f ≤ C := by
  constructor
  · intro hf
    exact ⟨Q.E ⟨f, hf⟩ ⟨f, hf⟩, fun β hβ => Q.approxForm_le_energy hQ β hβ ⟨f, hf⟩⟩
  · rintro ⟨C, hC⟩
    exact (Q.mem_dom_energy_le_of_approxForm_bounded hQ hd f C (fun n => hC _ _)).choose

/-- The solution energies converge to the original energy, by lower semicontinuity. -/
theorem tendsto_energy_beta_resolvent (u : Q.dom) :
    Tendsto (fun n => Q.E
      (Q.betaResolventDom hQ (resolventParameter n) (resolventParameter_pos n) (u : H))
      (Q.betaResolventDom hQ (resolventParameter n) (resolventParameter_pos n) (u : H)))
      atTop (𝓝 (Q.E u u)) := by
  let x := fun n => Q.betaResolventDom hQ (resolventParameter n) (resolventParameter_pos n) (u : H)
  have ht : Tendsto (fun n => (x n : H)) atTop (𝓝 (u : H)) :=
    Q.tendsto_beta_resolvent_dom hQ resolventParameter resolventParameter_pos tendsto_resolventParameter u
  have hu : ∀ n, Q.E (x n) (x n) ≤ Q.E u u := fun n =>
    (Q.energy_beta_resolvent_le_approxForm hQ _ _ (u : H)).trans (Q.approxForm_le_energy hQ _ _ u)
  have hupper : IsBoundedUnder (· ≤ ·) atTop (fun n => Q.E (x n) (x n)) :=
    isBoundedUnder_of ⟨Q.E u u, hu⟩
  have hlower : IsBoundedUnder (· ≥ ·) atTop (fun n => Q.E (x n) (x n)) :=
    isBoundedUnder_of ⟨0, fun n => Q.nonneg (x n)⟩
  have hl := hQ.energy_le_liminf ht ⟨Q.E u u, (Eventually.of_forall hu).frequently⟩ u.property
  apply tendsto_of_le_liminf_of_limsup_le hl _ hupper hlower
  exact limsup_le_of_le hlower.isCoboundedUnder_le (Eventually.of_forall hu)

/-- convergence of approximating energies, on the cofinal sequence n+1. -/
theorem tendsto_approxForm (u : Q.dom) :
    Tendsto (fun n => Q.approxForm hQ (resolventParameter n) (resolventParameter_pos n) (u : H) (u : H))
      atTop (𝓝 (Q.E u u)) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (Q.tendsto_energy_beta_resolvent hQ u)
    tendsto_const_nhds (fun n => Q.energy_beta_resolvent_le_approxForm hQ _ _ (u : H))
    (fun n => Q.approxForm_le_energy hQ _ _ u)

/-- The original energy is the least upper bound over all positive real parameters. -/
theorem energy_isLUB_approxForm (u : Q.dom) :
    IsLUB {a : ℝ | ∃ (β : ℝ) (hβ : 0 < β), a = Q.approxForm hQ β hβ (u : H) (u : H)} (Q.E u u) := by
  constructor
  · rintro a ⟨β, hβ, rfl⟩
    exact Q.approxForm_le_energy hQ β hβ u
  · intro C hC
    apply le_of_tendsto (Q.tendsto_approxForm hQ u)
    exact Eventually.of_forall (fun n => hC ⟨resolventParameter n, resolventParameter_pos n, rfl⟩)

end ErrorCalculus.QuadForm
