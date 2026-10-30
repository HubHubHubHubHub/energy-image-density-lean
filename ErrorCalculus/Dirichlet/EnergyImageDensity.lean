import ErrorCalculus.Dirichlet.EnergyImageWeak
import ErrorCalculus.Dirichlet.EnergyImagePrimitive

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- The primitives converge in L² after composition. Domination is by 2|u|. -/
theorem tendsto_smoothPrimitive_comp_L2 {O : Set ℝ} (hO : MeasurableSet O) (u : S.dom) :
    Tendsto (fun k => (S.lipschitzComp (lipschitzWith_one_smoothPrimitive hO k) u : Lp ℝ 2 μ))
      atTop (𝓝 (S.lipschitzComp (lipschitzWith_one_primitiveIndicator hO) u : Lp ℝ 2 μ)) := by
  let q k := S.lipschitzComp (lipschitzWith_one_smoothPrimitive hO k) u
  let v := S.lipschitzComp (lipschitzWith_one_primitiveIndicator hO) u
  have hq k x : |smoothPrimitive O k x| ≤ |x| := by
    simpa [smoothPrimitive] using (lipschitzWith_one_smoothPrimitive hO k).dist_le_mul x 0
  have hv x : |primitiveIndicator O x| ≤ |x| := by
    simpa [primitiveIndicator] using (lipschitzWith_one_primitiveIndicator hO).dist_le_mul x 0
  apply tendsto_sub_nhds_zero_iff.mp
  apply lp_two_tendsto_zero_of_dominated _ ((2 : ℝ) • (u : Lp ℝ 2 μ))
  · intro k
    filter_upwards [Lp.coeFn_sub (q k : Lp ℝ 2 μ) (v : Lp ℝ 2 μ),
      S.coeFn_lipschitzComp (lipschitzWith_one_smoothPrimitive hO k) u,
      S.coeFn_lipschitzComp (lipschitzWith_one_primitiveIndicator hO) u,
      Lp.coeFn_smul (2 : ℝ) (u : Lp ℝ 2 μ)] with ω hs hq' hv' h2
    change |((q k : Lp ℝ 2 μ) - (v : Lp ℝ 2 μ)) ω| ≤ _
    simp only [hs, Pi.sub_apply, q, v, hq', hv', h2, Pi.smul_apply, smul_eq_mul,
      abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    exact (abs_sub _ _).trans (by linarith [hq k ((u : Lp ℝ 2 μ) ω), hv ((u : Lp ℝ 2 μ) ω)])
  · filter_upwards [ae_all_iff.mpr (fun k => Lp.coeFn_sub (q k : Lp ℝ 2 μ) (v : Lp ℝ 2 μ)),
      ae_all_iff.mpr (fun k => S.coeFn_lipschitzComp (lipschitzWith_one_smoothPrimitive hO k) u),
      S.coeFn_lipschitzComp (lipschitzWith_one_primitiveIndicator hO) u] with ω hs hq' hv'
    simpa only [hs, Pi.sub_apply, q, v, hq', hv', sub_self] using
      (tendsto_smoothPrimitive hO ((u : Lp ℝ 2 μ) ω)).sub_const (primitiveIndicator O ((u : Lp ℝ 2 μ) ω))

/-- The lower bound in Fatou's argument. Since the coefficients are bounded,
dominated convergence on the preimage of O gives the same inequality directly. -/
theorem integral_indicator_gamma_le_two_energy_mixed {O : Set ℝ} (hO : IsOpen O) (u : S.dom) :
    (∫ ω in (u : Lp ℝ 2 μ) ⁻¹' O, S.Γ u u ω ∂μ) ≤
      2 * S.energy.E (S.lipschitzComp (lipschitzWith_one_primitiveIndicator hO.measurableSet) u) u := by
  let F := smoothPrimitive O
  let hL := lipschitzWith_one_smoothPrimitive hO.measurableSet
  let q k := S.lipschitzComp (hL k) u
  let v := S.lipschitzComp (lipschitzWith_one_primitiveIndicator hO.measurableSet) u
  have hc k : Continuous (deriv (F k)) :=
    (contDiff_one_smoothPrimitive hO.measurableSet k).continuous_deriv (by norm_num)
  have hb k x : deriv (F k) x ∈ Set.Icc (0 : ℝ) 1 := by
    change deriv (smoothPrimitive O k) x ∈ Set.Icc (0 : ℝ) 1
    rw [deriv_smoothPrimitive hO.measurableSet]
    exact smoothIndicator_mem_Icc hO.measurableSet k x
  have hi k : Integrable (fun ω => deriv (F k) ((u : Lp ℝ 2 μ) ω) * S.Γ u u ω) μ :=
    (L1.integrable_coeFn (S.Γ (q k) u)).congr
      (S.gamma_lipschitzComp_mixed (contDiff_one_smoothPrimitive hO.measurableSet k) (hL k) u)
  have hs : MeasurableSet ((u : Lp ℝ 2 μ) ⁻¹' O) :=
    (Lp.stronglyMeasurable (u : Lp ℝ 2 μ)).measurable hO.measurableSet
  have hd := tendsto_integral_of_dominated_convergence
    (μ := μ.restrict ((u : Lp ℝ 2 μ) ⁻¹' O))
    (F := fun k ω => deriv (F k) ((u : Lp ℝ 2 μ) ω) * S.Γ u u ω)
    (f := fun ω => S.Γ u u ω) (fun ω => ‖S.Γ u u ω‖)
    (fun k => (hi k).aestronglyMeasurable.restrict)
    (L1.integrable_coeFn (S.Γ u u)).norm.integrableOn
    (fun k => ae_of_all _ fun ω => by
      rw [norm_mul, Real.norm_of_nonneg (hb k _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb k _).2) ?_
  · have he := S.tendsto_energy_mixed_of_tendsto_L2_of_energy_le
      (S.tendsto_smoothPrimitive_comp_L2 hO.measurableSet u)
      (C := S.energy.E u u) (fun k => by
        simpa using S.energy_lipschitz_comp_le (hL k) u (q k) (S.coeFn_lipschitzComp (hL k) u)) u
    apply le_of_tendsto_of_tendsto hd (he.const_mul 2)
    filter_upwards [] with k
    rw [S.two_energy_mixed_eq_integral (contDiff_one_smoothPrimitive hO.measurableSet k) (hL k) u]
    apply setIntegral_le_integral (hi k)
    filter_upwards [S.Γ_nonneg u] with ω hω
    exact mul_nonneg (hb k _).1 hω
  · apply (ae_restrict_iff' hs).mpr
    exact ae_of_all _ fun ω hω => by
      simpa only [one_mul] using
        (tendsto_deriv_smoothPrimitive_of_mem hO hω).mul_const (S.Γ u u ω)

/-- Second weak limit: small volumes force the primitive compositions to zero. -/
theorem tendsto_energy_mixed_primitive {O : ℕ → Set ℝ}
    (hO : ∀ n, MeasurableSet (O n)) (hfin : ∀ n, volume (O n) ≠ ∞)
    (hvol : Tendsto (fun n => (volume (O n)).toReal) atTop (𝓝 0)) (u : S.dom) :
    Tendsto (fun n => S.energy.E
      (S.lipschitzComp (lipschitzWith_one_primitiveIndicator (hO n)) u) u) atTop (𝓝 0) := by
  have ht : Tendsto (fun n =>
      (S.lipschitzComp (lipschitzWith_one_primitiveIndicator (hO n)) u : Lp ℝ 2 μ))
      atTop (𝓝 0) := by
    apply tendsto_Lp_of_uniform_error hvol
    intro n
    filter_upwards [S.coeFn_lipschitzComp (lipschitzWith_one_primitiveIndicator (hO n)) u,
      Lp.coeFn_zero ℝ 2 μ] with ω hc hz
    simpa only [hc, hz, Pi.zero_apply, sub_zero] using abs_primitiveIndicator_le (hO n) (hfin n) _
  have he := S.tendsto_energy_mixed_of_tendsto_L2_of_energy_le (v := 0) ht
    (C := S.energy.E u u) (fun n => by
      simpa using S.energy_lipschitz_comp_le (lipschitzWith_one_primitiveIndicator (hO n)) u _
        (S.coeFn_lipschitzComp (lipschitzWith_one_primitiveIndicator (hO n)) u)) u
  simpa using he

/-- Outer regularity supplies finite-volume open supersets of every null set. -/
theorem exists_open_null_approximants {A : Set ℝ} (hA : volume A = 0) :
    ∃ O : ℕ → Set ℝ, (∀ n, A ⊆ O n) ∧ (∀ n, IsOpen (O n)) ∧
      (∀ n, volume (O n) ≠ ∞) ∧ Tendsto (fun n => (volume (O n)).toReal) atTop (𝓝 0) := by
  have hex (n : ℕ) : ∃ O : Set ℝ, A ⊆ O ∧ IsOpen O ∧
      volume O < ENNReal.ofReal (1/((n : ℝ)+1)) := by
    apply A.exists_isOpen_lt_of_lt
    rw [hA]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  choose O hsub hopen hvol using hex
  refine ⟨O, hsub, hopen, fun n => (hvol n).trans_le (le_top) |>.ne, ?_⟩
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun n => ENNReal.toReal_le_of_le_ofReal (by positivity) (hvol n).le)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Every Lebesgue-null Borel set has zero scalar energy image mass. -/
theorem integral_indicator_gamma_eq_zero_of_null (u : S.dom) {A : Set ℝ}
    (hzero : volume A = 0) :
    (∫ ω in (u : Lp ℝ 2 μ) ⁻¹' A, S.Γ u u ω ∂μ) = 0 := by
  obtain ⟨O, hsub, hopen, hfin, hvol⟩ := exists_open_null_approximants hzero
  apply le_antisymm
  · have he := (S.tendsto_energy_mixed_primitive
      (fun n => (hopen n).measurableSet) hfin hvol u).const_mul 2
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa only [mul_zero] using he)
    filter_upwards [] with n
    apply le_trans ?_ (S.integral_indicator_gamma_le_two_energy_mixed (hopen n) u)
    apply setIntegral_mono_set (L1.integrable_coeFn (S.Γ u u)).integrableOn
      (ae_restrict_of_ae (S.Γ_nonneg u))
    exact ae_of_all _ fun ω hω => hsub n hω
  · exact integral_nonneg_of_ae (ae_restrict_of_ae (S.Γ_nonneg u))

/-- Bouleau--Hirsch I.7.1.1 in its null-level formulation, for arbitrary Borel null sets. -/
theorem gamma_eq_zero_on_null (u : S.dom) {A : Set ℝ}
    (hA : MeasurableSet A) (hzero : volume A = 0) :
    ∀ᵐ ω ∂μ, (u : Lp ℝ 2 μ) ω ∈ A → S.Γ u u ω = 0 := by
  have hz := (integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae (S.Γ_nonneg u))
    (L1.integrable_coeFn (S.Γ u u)).integrableOn).mp
      (S.integral_indicator_gamma_eq_zero_of_null u hzero)
  exact (ae_restrict_iff' ((Lp.stronglyMeasurable (u : Lp ℝ 2 μ)).measurable hA)).mp hz

/-- Scalar energy image density for every error structure and every domain element. -/
theorem energyImage_absolutelyContinuous (u : S.dom) :
    (μ.withDensity (fun ω => ENNReal.ofReal (S.Γ u u ω))).map (u : Lp ℝ 2 μ) ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hzero
  rw [Measure.map_apply (Lp.stronglyMeasurable (u : Lp ℝ 2 μ)).measurable hA,
    withDensity_apply _ ((Lp.stronglyMeasurable (u : Lp ℝ 2 μ)).measurable hA)]
  apply (lintegral_eq_zero_iff'
    ((Lp.aestronglyMeasurable (S.Γ u u)).aemeasurable.ennreal_ofReal.restrict)).mpr
  apply (ae_restrict_iff' ((Lp.stronglyMeasurable (u : Lp ℝ 2 μ)).measurable hA)).mpr
  filter_upwards [S.gamma_eq_zero_on_null u hA hzero] with ω hω hmem
  simp [hω hmem]

end ErrorCalculus.ErrorStructure
