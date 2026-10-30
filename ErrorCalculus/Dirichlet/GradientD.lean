import ErrorCalculus.Dirichlet.DensityDStructure
import ErrorCalculus.Dirichlet.FormSpace
import Mathlib.MeasureTheory.Function.Holder

noncomputable section
open MeasureTheory Filter Topology

set_option linter.unusedSectionVars false
namespace ErrorCalculus
variable {d : ℕ}
variable (ρ : (Fin d → ℝ) → ℝ) [SmoothDensityD ρ]
  [IsProbabilityMeasure (densityMeasureD ρ)]

/-- completeness gives a limit for each coordinate gradient. -/
theorem exists_gradD_limit_of_approaches (i : Fin d) {s : ℕ → protoDomD ρ}
    {u : Lp ℝ 2 (densityMeasureD ρ)} (hs : (protoFormD ρ).Approaches s u) :
    ∃ G : Lp ℝ 2 (densityMeasureD ρ), Tendsto (fun n => gradD ρ i (s n)) atTop (𝓝 G) :=
  cauchySeq_tendsto_of_complete (cauchySeq_gradD ρ i hs.1)

/-- independence follows by applying closability to the difference. -/
theorem gradD_limit_unique (i : Fin d) {s t : ℕ → protoDomD ρ}
    {u G H : Lp ℝ 2 (densityMeasureD ρ)}
    (hs : Tendsto (fun n => (s n : Lp ℝ 2 (densityMeasureD ρ))) atTop (𝓝 u))
    (ht : Tendsto (fun n => (t n : Lp ℝ 2 (densityMeasureD ρ))) atTop (𝓝 u))
    (hG : Tendsto (fun n => gradD ρ i (s n)) atTop (𝓝 G))
    (hH : Tendsto (fun n => gradD ρ i (t n)) atTop (𝓝 H)) : G = H := by
  apply sub_eq_zero.mp
  apply gradient_limit_zeroD ρ i (u := fun n => s n - t n)
  · simpa only [Submodule.coe_sub, sub_self] using hs.sub ht
  · simpa only [map_sub] using hG.sub hH

theorem exists_approaches_gradD_limit (i : Fin d) (u : (densityStructureD ρ).dom) :
    ∃ G : Lp ℝ 2 (densityMeasureD ρ), ∃ s : ℕ → protoDomD ρ,
      (protoFormD ρ).Approaches s u ∧ Tendsto (fun n => gradD ρ i (s n)) atTop (𝓝 G) := by
  obtain ⟨s, hs⟩ := ((protoFormD ρ).mem_closureDom_iff u).mp u.property
  obtain ⟨G, hG⟩ := exists_gradD_limit_of_approaches ρ i hs
  exact ⟨G, s, hs, hG⟩

/-- coordinate gradient on the entire closed domain. -/
def gradientD (i : Fin d) (u : (densityStructureD ρ).dom) : Lp ℝ 2 (densityMeasureD ρ) :=
  Classical.choose (exists_approaches_gradD_limit ρ i u)

theorem gradientD_spec (i : Fin d) (u : (densityStructureD ρ).dom) :
    ∃ s : ℕ → protoDomD ρ, (protoFormD ρ).Approaches s u ∧
      Tendsto (fun n => gradD ρ i (s n)) atTop (𝓝 (gradientD ρ i u)) :=
  Classical.choose_spec (exists_approaches_gradD_limit ρ i u)

theorem tendsto_gradD_of_approaches (i : Fin d) {s : ℕ → protoDomD ρ}
    {u : (densityStructureD ρ).dom} (hs : (protoFormD ρ).Approaches s u) :
    Tendsto (fun n => gradD ρ i (s n)) atTop (𝓝 (gradientD ρ i u)) := by
  obtain ⟨G, hG⟩ := exists_gradD_limit_of_approaches ρ i hs
  obtain ⟨t, ht, hH⟩ := gradientD_spec ρ i u
  exact (gradD_limit_unique ρ i hs.2 ht.2 hG hH) ▸ hG

@[simp] theorem gradientD_inclusion (i : Fin d) (u : protoDomD ρ) :
    gradientD ρ i ((protoFormD ρ).inclusion u) = gradD ρ i u := by
  apply tendsto_nhds_unique (tendsto_gradD_of_approaches ρ i (s := fun _ => u) ?_)
    tendsto_const_nhds
  exact ⟨⟨cauchySeq_const _, cauchySeq_const _⟩, tendsto_const_nhds⟩

theorem gradientD_add (i : Fin d) (u v : (densityStructureD ρ).dom) :
    gradientD ρ i (u + v) = gradientD ρ i u + gradientD ρ i v := by
  obtain ⟨s, hs, hG⟩ := gradientD_spec ρ i u
  obtain ⟨t, ht, hH⟩ := gradientD_spec ρ i v
  obtain ⟨r, hr, hR⟩ := gradientD_spec ρ i (u + v)
  apply gradD_limit_unique ρ i (t := fun n => s n + t n) hr.2 (hs.2.add ht.2) hR
  simpa only [map_add] using hG.add hH

theorem gradientD_smul (i : Fin d) (c : ℝ) (u : (densityStructureD ρ).dom) :
    gradientD ρ i (c • u) = c • gradientD ρ i u := by
  obtain ⟨s, hs, hG⟩ := gradientD_spec ρ i u
  obtain ⟨r, hr, hR⟩ := gradientD_spec ρ i (c • u)
  apply gradD_limit_unique ρ i (t := fun n => c • s n) hr.2 (hs.2.const_smul c) hR
  simpa only [map_smul] using hG.const_smul c

def gradientDₗ (i : Fin d) : (densityStructureD ρ).dom →ₗ[ℝ] Lp ℝ 2 (densityMeasureD ρ) where
  toFun := gradientD ρ i
  map_add' := gradientD_add ρ i
  map_smul' := gradientD_smul ρ i

/-- The continuous Hölder product used to pass to the closed carré du champ. -/
def densityL2ProductD : Lp ℝ 2 (densityMeasureD ρ) →L[ℝ]
    Lp ℝ 2 (densityMeasureD ρ) →L[ℝ] Lp ℝ 1 (densityMeasureD ρ) :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (densityMeasureD ρ) 2 2 1

theorem coeFn_densityL2ProductD (f g : Lp ℝ 2 (densityMeasureD ρ)) :
    densityL2ProductD ρ f g =ᵐ[densityMeasureD ρ] fun x => f x * g x :=
  (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder f g

theorem gammaD_eq_sum_product (u v : protoDomD ρ) :
    gammaD ρ u v = ∑ i, densityL2ProductD ρ (gradD ρ i u) (gradD ρ i v) := by
  apply Lp.ext
  filter_upwards [coeFn_gammaD ρ u v, Lp.coeFn_fun_finsetSum Finset.univ (fun i => densityL2ProductD ρ (gradD ρ i u) (gradD ρ i v)),
    ae_all_iff.mpr (fun i => coeFn_gradD ρ i u),
    ae_all_iff.mpr (fun i => coeFn_gradD ρ i v),
    ae_all_iff.mpr (fun i => coeFn_densityL2ProductD ρ (gradD ρ i u) (gradD ρ i v))]
      with x hx hsum hu hv hp
  rw [hx, hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hp i, hu i, hv i]
  rfl

/-- equality in L¹, before taking representatives. -/
theorem densityStructureD_Γ_eq_sum_product (u v : (densityStructureD ρ).dom) :
    (densityStructureD ρ).Γ u v =
      ∑ i, densityL2ProductD ρ (gradientD ρ i u) (gradientD ρ i v) := by
  obtain ⟨s, hs⟩ := ((protoFormD ρ).mem_closureDom_iff u).mp u.property
  obtain ⟨t, ht⟩ := ((protoFormD ρ).mem_closureDom_iff v).mp v.property
  have hΓ := (protoDataD ρ).closureGamma_characterization (protoFormD_isClosable ρ)
    (a := u) (b := v) hs ht
  change Tendsto (fun n => gammaD ρ (s n) (t n)) atTop
    (𝓝 ((densityStructureD ρ).Γ u v)) at hΓ
  have hG (i : Fin d) := tendsto_gradD_of_approaches ρ i (u := u) hs
  have hH (i : Fin d) := tendsto_gradD_of_approaches ρ i (u := v) ht
  have hp (i : Fin d) := ((densityL2ProductD ρ).continuous₂.tendsto
    (gradientD ρ i u, gradientD ρ i v)).comp ((hG i).prodMk_nhds (hH i))
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hp i)
  simp_rw [gammaD_eq_sum_product] at hΓ
  exact tendsto_nhds_unique hΓ hsum

/-- mixed carré du champ on the whole closed domain. -/
theorem densityStructureD_Γ_eq_gradient (u v : (densityStructureD ρ).dom) :
    (densityStructureD ρ).Γ u v =ᵐ[densityMeasureD ρ]
      fun x => ∑ i, gradientD ρ i u x * gradientD ρ i v x := by
  rw [densityStructureD_Γ_eq_sum_product]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => densityL2ProductD ρ (gradientD ρ i u) (gradientD ρ i v)),
    ae_all_iff.mpr (fun i => coeFn_densityL2ProductD ρ (gradientD ρ i u) (gradientD ρ i v))]
      with x hsum hp
  rw [hsum]
  exact Finset.sum_congr rfl (fun i _ => hp i)

theorem densityStructureD_Γ_diag_gradient (u : (densityStructureD ρ).dom) :
    (densityStructureD ρ).Γ u u =ᵐ[densityMeasureD ρ]
      fun x => ∑ i, (gradientD ρ i u x)^2 := by
  simpa only [pow_two] using densityStructureD_Γ_eq_gradient ρ u u

/-- The closed energy retains the factor 1/2. -/
theorem densityStructureD_energy_eq_gradient (u v : (densityStructureD ρ).dom) :
    (densityStructureD ρ).energy.E u v =
      (1/2:ℝ) * ∑ i, inner ℝ (gradientD ρ i u) (gradientD ρ i v) := by
  obtain ⟨s, hs⟩ := ((protoFormD ρ).mem_closureDom_iff u).mp u.property
  obtain ⟨t, ht⟩ := ((protoFormD ρ).mem_closureDom_iff v).mp v.property
  have he := (protoFormD ρ).closure_characterization (protoFormD_isClosable ρ)
    hs ht u.property v.property
  calc
    _ = ((protoFormD ρ).closure (protoFormD_isClosable ρ)).E u v :=
      (protoDataD ρ).closureGamma_energy (protoFormD_isClosable ρ) u v
    _ = _ := by
      apply tendsto_nhds_unique he
      simp_rw [protoForm_eq_inner_gradD]
      exact (tendsto_finsetSum Finset.univ fun i _ =>
        (tendsto_gradD_of_approaches ρ i hs).inner (𝕜 := ℝ)
          (tendsto_gradD_of_approaches ρ i ht)).const_mul (1/2:ℝ)

theorem densityStructureD_energy_diag_gradient (u : (densityStructureD ρ).dom) :
    (densityStructureD ρ).energy.E u u = (1/2:ℝ) * ∑ i, ‖gradientD ρ i u‖^2 := by
  simp only [densityStructureD_energy_eq_gradient, real_inner_self_eq_norm_sq]

theorem norm_gradientD_sq_le (i : Fin d) (u : (densityStructureD ρ).dom) :
    ‖gradientD ρ i u‖^2 ≤ 2 * (densityStructureD ρ).energy.E u u := by
  rw [densityStructureD_energy_diag_gradient]
  have h := Finset.single_le_sum (fun j _ => sq_nonneg ‖gradientD ρ j u‖) (Finset.mem_univ i)
  linarith

/-- The sharp constant for each coordinate. -/
theorem norm_gradientD_le (i : Fin d) (u : (densityStructureD ρ).dom) :
    ‖gradientD ρ i u‖ ≤ Real.sqrt 2 * Real.sqrt ((densityStructureD ρ).energy.E u u) := by
  have h := norm_gradientD_sq_le ρ i u
  have he := Real.sq_sqrt ((densityStructureD ρ).energy.nonneg u)
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp : 0 ≤ Real.sqrt 2 * Real.sqrt ((densityStructureD ρ).energy.E u u) := by positivity
  nlinarith [sq_nonneg (‖gradientD ρ i u‖ - Real.sqrt 2 *
    Real.sqrt ((densityStructureD ρ).energy.E u u)), mul_pow (Real.sqrt 2)
      (Real.sqrt ((densityStructureD ρ).energy.E u u)) 2]

/-- The gradient is continuous for the form norm, rather than the ambient L² norm. -/
def gradientDCLM (i : Fin d) :
    (densityStructureD ρ).energy.FormSpace →L[ℝ] Lp ℝ 2 (densityMeasureD ρ) :=
  ((gradientDₗ ρ i).comp (densityStructureD ρ).energy.formToDomain.toLinearMap).mkContinuous
    (Real.sqrt 2) (by
      intro u
      have h := norm_gradientD_sq_le ρ i ((densityStructureD ρ).energy.formToDomain u)
      have hn := (densityStructureD ρ).energy.formSpace_norm_sq u
      have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      change ‖gradientD ρ i ((densityStructureD ρ).energy.formToDomain u)‖ ≤ Real.sqrt 2 * ‖u‖
      have hp : 0 ≤ Real.sqrt 2 * ‖u‖ := by positivity
      nlinarith [sq_nonneg ‖((densityStructureD ρ).energy.formToDomain u : Lp ℝ 2 (densityMeasureD ρ))‖,
        mul_pow (Real.sqrt 2) ‖u‖ 2, norm_nonneg (gradientD ρ i ((densityStructureD ρ).energy.formToDomain u))])

theorem gradientD_continuous (i : Fin d) :
    Continuous (fun u : (densityStructureD ρ).energy.FormSpace =>
      gradientD ρ i ((densityStructureD ρ).energy.formToDomain u)) :=
  (gradientDCLM ρ i).continuous

end ErrorCalculus
