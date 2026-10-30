import ErrorCalculus.Dirichlet.SemigroupEnergyContraction
import ErrorCalculus.Dirichlet.SemigroupContraction
import ErrorCalculus.Dirichlet.GeneratorWeights

/-!
# Semigroup Orbit Deriv

## Main results
Differentiable generator-domain orbits, including the initial right derivative. The integral
representation from gives both sides at every positive time.
-/
noncomputable section
open MeasureTheory Filter Topology Set
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

theorem semigroup_mem_generatorDom {t : ℝ} (ht : 0 ≤ t) (u : S.generatorDom) :
    S.semigroup t u ∈ S.generatorDom :=
  S.energy.semigroup_mem_dom S.energy_closed S.dense ht u

def semigroupGeneratorDom {t : ℝ} (ht : 0 ≤ t) (u : S.generatorDom) : S.generatorDom :=
  ⟨S.semigroup t u, S.semigroup_mem_generatorDom ht u⟩

def semigroupFormDom {t : ℝ} (ht : 0 ≤ t) (u : S.generatorDom) : S.dom :=
  ⟨S.semigroup t u, S.energy.formResolvent_dom_le S.energy_closed S.dense
    (S.semigroup_mem_generatorDom ht u)⟩

theorem semigroup_generator_eq {t : ℝ} (ht : 0 ≤ t) (u : S.generatorDom) :
    S.semigroup t (S.generator u) = S.generator (S.semigroupGeneratorDom ht u) :=
  (S.energy.generator_semigroup S.energy_closed S.dense ht u).symm

/-- FTC applied to the integral representation proves the two-sided derivative. -/
theorem hasDerivAt_semigroup (u : S.generatorDom) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => S.semigroup s u) (S.semigroup t (S.generator u)) t := by
  have hc := S.energy.continuous_semigroup_apply S.energy_closed S.dense (S.generator u)
  have hi : IntervalIntegrable (fun s => S.semigroup s (S.generator u)) volume 0 t :=
    (hc.mono (by intro s hs; exact hs.1)).intervalIntegrable_of_Icc ht.le
  have hct : ContinuousAt (fun s => S.semigroup s (S.generator u)) t :=
    hc.continuousAt (Ici_mem_nhds ht)
  have hm : StronglyMeasurableAtFilter (fun s => S.semigroup s (S.generator u)) (𝓝 t) :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi (hc.mono Ioi_subset_Ici_self)
      t ht
  have hd := (intervalIntegral.integral_hasDerivAt_right hi hm hct).add_const (u : Lp ℝ 2 μ)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ici_mem_nhds ht] with s hs
  have he := S.energy.semigroup_sub_eq_integral S.energy_closed S.dense hs u
  change S.semigroup s u - (u : Lp ℝ 2 μ) = _ at he
  exact eq_add_of_sub_eq he

theorem hasDerivWithinAt_semigroup_Ici (u : S.generatorDom) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => S.semigroup s u) (S.semigroup t (S.generator u)) (Ici t) t := by
  rcases ht.eq_or_lt with he | hp
  · subst t
    simpa [semigroup] using
      S.energy.hasDerivWithinAt_semigroup_zero S.energy_closed S.dense u
  · exact (S.hasDerivAt_semigroup u hp).hasDerivWithinAt

theorem hasDerivWithinAt_semigroup_Iic (u : S.generatorDom) {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (fun s => S.semigroup s u) (S.semigroup t (S.generator u)) (Iic t) t :=
  (S.hasDerivAt_semigroup u ht).hasDerivWithinAt

theorem deriv_semigroup (u : S.generatorDom) {t : ℝ} (ht : 0 < t) :
    deriv (fun s => S.semigroup s u) t = S.semigroup t (S.generator u) :=
  (S.hasDerivAt_semigroup u ht).deriv

theorem integral_generator_eq_zero (u : S.generatorDom) :
    ∫ ω, S.generator u ω ∂μ = 0 := by
  have he := S.energy.energy_eq_neg_inner_generator S.energy_closed S.dense u (S.const 1)
  have hz : S.energy.E ⟨u, S.energy.formResolvent_dom_le S.energy_closed S.dense u.property⟩
      (S.const 1) = 0 := by
    rw [S.energy.symm, ErrorData.energy_apply, S.gamma_const]
    rw [integral_congr_ae (Lp.coeFn_zero ℝ 1 μ)]
    simp
  rw [hz, L2.inner_def] at he
  have hi : (∫ ω, inner ℝ (S.generator u ω) ((S.const 1 : Lp ℝ 2 μ) ω) ∂μ) =
      ∫ ω, S.generator u ω ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with ω hω
    change inner ℝ (S.generator u ω) (Lp.const 2 μ (1 : ℝ) ω) = _
    simp [RCLike.inner_apply]
  rw [hi] at he
  linarith

end ErrorCalculus.ErrorStructure
