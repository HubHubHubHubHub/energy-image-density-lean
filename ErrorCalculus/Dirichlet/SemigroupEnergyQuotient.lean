import ErrorCalculus.Dirichlet.SemigroupEnergyContraction
import ErrorCalculus.Dirichlet.ApproximatingForm

noncomputable section
open Filter Topology Set MeasureTheory
namespace ErrorCalculus

/--
averages from zero of a continuous decreasing real function decrease. The proof compares both
adjacent intervals with their common endpoint value.
-/
theorem antitone_average_of_antitone {g : ℝ → ℝ}
    (hc : ContinuousOn g (Ici 0)) (hg : AntitoneOn g (Ici 0)) :
    AntitoneOn (fun t => (∫ s in 0..t, g s) / t) (Ioi 0) := by
  intro s hs t ht hst
  change 0 < s at hs
  change 0 < t at ht
  have hi (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable g volume a b :=
    (hc.mono (fun _ hx => le_trans ha hx.1)).intervalIntegrable_of_Icc hab
  have hlow := intervalIntegral.integral_mono_on hs.le
    (intervalIntegrable_const (c := g s)) (hi 0 s le_rfl hs.le)
    (fun x hx => hg hx.1 hs.le hx.2)
  have hupp := intervalIntegral.integral_mono_on hst
    (hi s t hs.le hst) (intervalIntegrable_const (c := g s))
    (fun x hx => hg hs.le (hs.le.trans hx.1) hx.1)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hlow hupp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hi 0 s le_rfl hs.le) (hi s t hs.le hst)
  apply (div_le_div_iff₀ ht hs).mpr
  have h₁ := mul_le_mul_of_nonneg_left hupp hs.le
  have h₂ := mul_le_mul_of_nonneg_left hlow (sub_nonneg.mpr hst)
  nlinarith

namespace QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (Q : QuadForm H) (hQ : Q.IsClosed) (hd : Dense (Q.dom : Set H))

/-- The semigroup energy quotient, used at positive times. -/
def energyQuotient (u : H) (t : ℝ) : ℝ :=
  (1/t) * inner ℝ (u - Q.semigroup hQ hd t u) u

theorem continuous_energyQuotient (t : ℝ) :
    Continuous (fun u : H => Q.energyQuotient hQ hd u t) := by
  unfold energyQuotient
  fun_prop

theorem energyQuotient_nonneg (u : H) {t : ℝ} (ht : 0 < t) :
    0 ≤ Q.energyQuotient hQ hd u t := by
  unfold energyQuotient
  apply mul_nonneg (by positivity)
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  have hh := (real_inner_le_norm (Q.semigroup hQ hd t u) u).trans
    (mul_le_mul_of_nonneg_right (Q.norm_semigroup_apply_le hQ hd ht.le u) (norm_nonneg u))
  nlinarith

theorem continuousOn_semigroupEnergy (u : (Q.formResolvent hQ hd).dom) :
    ContinuousOn (Q.semigroupEnergy hQ hd u) (Ici 0) :=
  ((Q.continuous_semigroup_apply hQ hd _).inner
    (Q.continuous_semigroup_apply hQ hd _)).neg

theorem continuousOn_semigroupEnergy_half (u : (Q.formResolvent hQ hd).dom) :
    ContinuousOn (fun s => Q.semigroupEnergy hQ hd u (s/2)) (Ici 0) :=
  (Q.continuousOn_semigroupEnergy hQ hd u).comp
    (by fun_prop : Continuous (fun s : ℝ => s/2)).continuousOn
    (fun s hs => div_nonneg hs (by norm_num : (0:ℝ) ≤ 2))

/-- The correlation difference is the integral of diagonal energies. -/
theorem inner_sub_semigroup_eq_integral_energy {t : ℝ} (ht : 0 ≤ t)
    (u : (Q.formResolvent hQ hd).dom) :
    inner ℝ ((u : H) - Q.semigroup hQ hd t u) (u : H) =
      ∫ s in 0..t, Q.semigroupEnergy hQ hd u (s/2) := by
  have hi := ((Q.continuous_semigroup_apply hQ hd
    ((Q.formResolvent hQ hd).generator u)).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc (μ := volume) ht
  have hh := (innerSL ℝ (u : H)).intervalIntegral_comp_comm hi
  change (∫ s in 0..t, inner ℝ (u : H)
    (Q.semigroup hQ hd s ((Q.formResolvent hQ hd).generator u))) =
      inner ℝ (u : H) (∫ s in 0..t,
        Q.semigroup hQ hd s ((Q.formResolvent hQ hd).generator u)) at hh
  rw [← Q.semigroup_sub_eq_integral hQ hd ht u] at hh
  calc
    _ = -(∫ s in 0..t, inner ℝ (u : H)
        (Q.semigroup hQ hd s ((Q.formResolvent hQ hd).generator u))) := by
      rw [hh, inner_sub_right, inner_sub_left,
        real_inner_comm (u : H) (Q.semigroup hQ hd t u)]
      ring
    _ = ∫ s in 0..t, -inner ℝ (u : H)
        (Q.semigroup hQ hd s ((Q.formResolvent hQ hd).generator u)) :=
      intervalIntegral.integral_neg.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : 0 ≤ s := (show s ∈ Icc 0 t from (uIcc_of_le ht) ▸ hs).1
      dsimp only
      rw [Q.semigroupEnergy_double hQ hd (show 0 ≤ s/2 by positivity),
        show 2*(s/2) = s by ring, real_inner_comm]

theorem energyQuotient_eq_average {t : ℝ} (ht : 0 ≤ t)
    (u : (Q.formResolvent hQ hd).dom) :
    Q.energyQuotient hQ hd (u : H) t =
      (∫ s in 0..t, Q.semigroupEnergy hQ hd u (s/2)) / t := by
  rw [energyQuotient, Q.inner_sub_semigroup_eq_integral_energy hQ hd ht]
  ring

/-- The energy bound on the generator domain. -/
theorem energyQuotient_le_energy_generator {t : ℝ} (ht : 0 < t)
    (u : (Q.formResolvent hQ hd).dom) :
    Q.energyQuotient hQ hd (u : H) t ≤
      Q.E ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩
        ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩ := by
  rw [Q.energyQuotient_eq_average hQ hd ht.le]
  apply (div_le_iff₀ ht).mpr
  have hh := intervalIntegral.integral_mono_on ht.le
    ((Q.continuousOn_semigroupEnergy_half hQ hd u).mono Icc_subset_Ici_self
      |>.intervalIntegrable_of_Icc (μ := volume) ht.le)
    (intervalIntegrable_const (c := Q.semigroupEnergy hQ hd u 0))
    (fun s hs => by
      rw [Q.semigroupEnergy_zero]
      exact Q.energy_semigroup_le hQ hd (div_nonneg hs.1 (by norm_num)) u)
  simpa [mul_comm] using hh

/-- decreasing energy quotients on the generator domain. -/
theorem energyQuotient_antitone_generator (u : (Q.formResolvent hQ hd).dom) :
    AntitoneOn (Q.energyQuotient hQ hd (u : H)) (Ioi 0) := by
  have hg : AntitoneOn (fun s => Q.semigroupEnergy hQ hd u (s/2)) (Ici 0) := by
    intro s hs t ht hst
    exact Q.energy_semigroup_antitone hQ hd u
      (div_nonneg hs (by norm_num : (0:ℝ) ≤ 2)) (div_nonneg ht (by norm_num : (0:ℝ) ≤ 2)) (by linarith)
  intro s hs t ht hst
  rw [Q.energyQuotient_eq_average hQ hd hs.le, Q.energyQuotient_eq_average hQ hd ht.le]
  exact antitone_average_of_antitone (Q.continuousOn_semigroupEnergy_half hQ hd u) hg hs ht hst

/-- The approximants belong to the generator domain, not just the form domain. -/
theorem betaResolvent_mem_generatorDom (b : ℝ) (hb : 0 < b) (u : H) :
    (Q.betaResolventDom hQ b hb u : H) ∈ (Q.formResolvent hQ hd).dom := by
  rw [Q.formResolvent_dom hQ hd hb]
  exact ⟨b • u, by simp⟩

/-- extension of the energy bound by the resolvent approximants. -/
theorem energyQuotient_le_energy (u : Q.dom) {t : ℝ} (ht : 0 < t) :
    Q.energyQuotient hQ hd (u : H) t ≤ Q.E u u := by
  let x := fun n => Q.betaResolventDom hQ (resolventParameter n) (resolventParameter_pos n) (u : H)
  have hx : Tendsto (fun n => (x n : H)) atTop (𝓝 (u : H)) :=
    Q.tendsto_beta_resolvent_dom hQ resolventParameter resolventParameter_pos tendsto_resolventParameter u
  apply le_of_tendsto ((Q.continuous_energyQuotient hQ hd t).tendsto (u : H) |>.comp hx)
  apply Eventually.of_forall
  intro n
  have hh := Q.energyQuotient_le_energy_generator hQ hd ht
    ⟨x n, Q.betaResolvent_mem_generatorDom hQ hd _ _ (u : H)⟩
  exact hh.trans ((Q.energy_beta_resolvent_le_approxForm hQ _ _ (u : H)).trans
    (Q.approxForm_le_energy hQ _ _ u))

/-- pointwise limits preserve monotonicity on the entire form domain. -/
theorem energyQuotient_antitone (u : Q.dom) :
    AntitoneOn (Q.energyQuotient hQ hd (u : H)) (Ioi 0) := by
  let x := fun n => Q.betaResolventDom hQ (resolventParameter n) (resolventParameter_pos n) (u : H)
  have hx : Tendsto (fun n => (x n : H)) atTop (𝓝 (u : H)) :=
    Q.tendsto_beta_resolvent_dom hQ resolventParameter resolventParameter_pos tendsto_resolventParameter u
  intro s hs t ht hst
  apply le_of_tendsto_of_tendsto
    ((Q.continuous_energyQuotient hQ hd t).tendsto (u : H) |>.comp hx)
    ((Q.continuous_energyQuotient hQ hd s).tendsto (u : H) |>.comp hx)
  exact Eventually.of_forall fun n => Q.energyQuotient_antitone_generator hQ hd
    ⟨x n, Q.betaResolvent_mem_generatorDom hQ hd _ _ (u : H)⟩ hs ht hst

end QuadForm
end ErrorCalculus
