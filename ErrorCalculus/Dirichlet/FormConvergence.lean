import ErrorCalculus.Dirichlet.HilbertWeakStrong
import ErrorCalculus.Dirichlet.LowerSemicontinuous

noncomputable section
open Filter Topology
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Q : QuadForm H}

/-- Energy is continuous for the form topology in both arguments. -/
theorem continuous_energy_formSpace :
    Continuous (fun p : Q.FormSpace × Q.FormSpace =>
      Q.E (Q.formToDomain p.1) (Q.formToDomain p.2)) := by
  have h := (Q.formEnergy.continuous.comp continuous_fst).inner
    (𝕜 := ℝ) (Q.formEnergy.continuous.comp continuous_snd)
  change Continuous (fun p : Q.FormSpace × Q.FormSpace =>
    inner ℝ (Q.j (Q.formToDomain p.1)) (Q.j (Q.formToDomain p.2))) at h
  simpa only [Q.inner_j] using h

/-- The energy seminorm is bounded by the form norm. -/
theorem seminorm_le_formNorm (u : Q.dom) : Q.seminorm u ≤ Q.formNorm u := by
  rw [seminorm, Real.sqrt_le_iff]
  exact ⟨norm_nonneg _, by rw [Q.formNorm_sq]; nlinarith [sq_nonneg ‖(u : H)‖]⟩

variable [CompleteSpace H]

/--
ambient strong convergence and an upper energy limsup force convergence in the complete form Hilbert
space. The eventual energy bound is necessary when using the real-valued `Filter.limsup`.
-/
theorem IsClosed.tendsto_formSpace_of_limsup_energy_le (hQ : Q.IsClosed)
    {u : ℕ → Q.dom} {v : Q.dom}
    (ht : Tendsto (fun n => (u n : H)) atTop (𝓝 (v : H)))
    (hb : IsBoundedUnder (· ≤ ·) atTop (fun n => Q.E (u n) (u n)))
    (hs : limsup (fun n => Q.E (u n) (u n)) atTop ≤ Q.E v v) :
    Tendsto (fun n => Q.formToDomain.symm (u n)) atTop (𝓝 (Q.formToDomain.symm v)) := by
  letI := hQ.completeSpace_formSpace
  let g : ℕ → Q.FormSpace := fun n => Q.formToDomain.symm (u n)
  let x : Q.FormSpace := Q.formToDomain.symm v
  have hn : ∀ r > ‖x‖, ∀ᶠ n in atTop, ‖g n‖ < r := by
    intro r hr
    have hr0 : 0 < r := (norm_nonneg x).trans_lt hr
    have hd : 0 < r^2 - ‖x‖^2 := by nlinarith [norm_nonneg x]
    have he := eventually_lt_of_limsup_lt
      (hs.trans_lt (show Q.E v v < Q.E v v + (r^2 - ‖x‖^2)/2 by linarith)) hb
    have ha := (ht.norm.pow 2).eventually
      (gt_mem_nhds (show ‖(v : H)‖^2 < ‖(v : H)‖^2 + (r^2 - ‖x‖^2)/2 by linarith))
    filter_upwards [he, ha] with n he ha
    have hg := Q.formSpace_norm_sq (g n)
    have hx := Q.formSpace_norm_sq x
    change ‖g n‖^2 = ‖(u n : H)‖^2 + Q.E (u n) (u n) at hg
    change ‖x‖^2 = ‖(v : H)‖^2 + Q.E v v at hx
    nlinarith [norm_nonneg (g n)]
  have hb' : ∀ᶠ n in atTop, ‖g n‖ ≤ ‖x‖ + 1 :=
    (hn (‖x‖ + 1) (by linarith)).mono fun _ h => h.le
  apply tendsto_of_bounded_of_clusterPt_eq_of_limsup_norm_le hb'
  · intro A _ z hz
    have he : Q.formInclusion z = (v : H) :=
      formInclusion_eq_of_weak_cluster hz inf_le_left ht
    apply Q.formToDomain.injective
    exact Subtype.ext he
  · exact (limsup_le_iff
      (show IsBoundedUnder (· ≥ ·) atTop (fun n => ‖g n‖) from
        ⟨0, show ∀ᶠ n in atTop, 0 ≤ ‖g n‖ from
          Eventually.of_forall fun n => norm_nonneg (g n)⟩).isCobounded_flip
      (isBoundedUnder_of_eventually_le hb')).mpr hn

/-- Useful bounded-energy specialization of the limsup pivot. -/
theorem IsClosed.tendsto_formSpace_of_energy_le (hQ : Q.IsClosed)
    {u : ℕ → Q.dom} {v : Q.dom}
    (ht : Tendsto (fun n => (u n : H)) atTop (𝓝 (v : H)))
    (he : ∀ n, Q.E (u n) (u n) ≤ Q.E v v) :
    Tendsto (fun n => Q.formToDomain.symm (u n)) atTop (𝓝 (Q.formToDomain.symm v)) := by
  apply hQ.tendsto_formSpace_of_limsup_energy_le ht
    (isBoundedUnder_of_eventually_le (Eventually.of_forall he))
  exact limsup_le_of_le
    (show IsBoundedUnder (· ≥ ·) atTop (fun n => Q.E (u n) (u n)) from
      ⟨0, show ∀ᶠ n in atTop, 0 ≤ Q.E (u n) (u n) from
        Eventually.of_forall fun n => Q.nonneg (u n)⟩).isCobounded_flip
    (Eventually.of_forall he)

end ErrorCalculus.QuadForm
