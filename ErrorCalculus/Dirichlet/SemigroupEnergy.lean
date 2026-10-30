import ErrorCalculus.Dirichlet.SemigroupGenerator

noncomputable section
open Filter Topology
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (Q : QuadForm H) (hQ : Q.IsClosed) (hd : Dense (Q.dom : Set H))

/-- The limiting semigroup commutes with each positive resolvent. -/
theorem semigroup_commute_resolvent {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    Commute (Q.semigroup hQ hd t) (Q.resolvent hQ b hb) := by
  let R := Q.formResolvent hQ hd
  change Q.semigroup hQ hd t * Q.resolvent hQ b hb =
    Q.resolvent hQ b hb * Q.semigroup hQ hd t
  ext f
  have h₁ := R.tendsto_semigroupApprox_apply ht (R.G b f)
  have h₂ := (R.G b).continuous.tendsto (R.semigroup t f) |>.comp
    (R.tendsto_semigroupApprox_apply ht f)
  have he : R.semigroup t (R.G b f) = R.G b (R.semigroup t f) := by
    apply tendsto_nhds_unique h₁
    apply h₂.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    exact (congrArg (fun T : H →L[ℝ] H => T f)
      (R.semigroupApprox_commute_G ha hb t).eq).symm
  simpa only [semigroup, R, Q.formResolvent_G hQ hd hb, mul_apply_eq_comp] using he

/-- The generator domain is invariant under the semigroup. -/
theorem semigroup_mem_dom {t : ℝ} (ht : 0 ≤ t) (u : (Q.formResolvent hQ hd).dom) :
    Q.semigroup hQ hd t u ∈ (Q.formResolvent hQ hd).dom := by
  have hu := (Q.formResolvent_dom hQ hd zero_lt_one).le u.property
  apply (Q.formResolvent_dom hQ hd zero_lt_one).ge
  obtain ⟨f, hf⟩ := hu
  change Q.resolvent hQ 1 zero_lt_one f = (u : H) at hf
  refine ⟨Q.semigroup hQ hd t f, ?_⟩
  change Q.resolvent hQ 1 zero_lt_one (Q.semigroup hQ hd t f) = _
  have he := congrArg (fun T : H →L[ℝ] H => T f)
    (Q.semigroup_commute_resolvent hQ hd zero_lt_one ht).eq
  simpa only [mul_apply_eq_comp, hf] using he.symm

/-- The positive quadratic pairing is the squared norm at half the time. -/
theorem inner_semigroup_self_eq_norm_sq {t : ℝ} (ht : 0 ≤ t) (u : H) :
    inner ℝ (Q.semigroup hQ hd t u) u = ‖Q.semigroup hQ hd (t/2) u‖^2 := by
  have ht2 : 0 ≤ t/2 := by positivity
  conv_lhs => rw [show t = t/2+t/2 by ring, Q.semigroup_add hQ hd ht2 ht2,
    mul_apply_eq_comp, Q.semigroup_symm hQ hd ht2]
  exact real_inner_self_eq_norm_sq _

/-- Correlations decrease along the semigroup, for every ambient vector. -/
theorem inner_semigroup_self_antitone (u : H) :
    AntitoneOn (fun t => inner ℝ (Q.semigroup hQ hd t u) u) (Set.Ici 0) := by
  intro s hs t ht hst
  change 0 ≤ s at hs
  change 0 ≤ t at ht
  change inner ℝ (Q.semigroup hQ hd t u) u ≤ inner ℝ (Q.semigroup hQ hd s u) u
  rw [Q.inner_semigroup_self_eq_norm_sq hQ hd hs u,
    Q.inner_semigroup_self_eq_norm_sq hQ hd ht u]
  have hdiff : 0 ≤ (t-s)/2 := div_nonneg (sub_nonneg.mpr hst) (by norm_num)
  have he : t/2 = (t-s)/2 + s/2 := by ring
  rw [he, Q.semigroup_add hQ hd hdiff (by positivity), mul_apply_eq_comp]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (Q.norm_semigroup_apply_le hQ hd hdiff (Q.semigroup hQ hd (s/2) u)) 2

end ErrorCalculus.QuadForm
