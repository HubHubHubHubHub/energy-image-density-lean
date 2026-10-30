import ErrorCalculus.Dirichlet.ClosureExamples
import Foundations.Sobolev1D.Lp

noncomputable section
open MeasureTheory Filter Topology
set_option linter.unusedSectionVars false
namespace ErrorCalculus
variable (ρ : ℝ → ℝ) [SmoothDensity ρ] [IsProbabilityMeasure (densityMeasure ρ)]

/-- The chosen C¹ representative gives back the original L² class. -/
theorem toLp_rep (u : protoDom ρ) :
    ((rep_isC1Bounded ρ u).memLp (densityMeasure ρ) 2).toLp (rep ρ u) =
      (u : Lp ℝ 2 (densityMeasure ρ)) := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans (coeFn_rep ρ u).symm

/--
The gradient of a proto-domain element is the L² class of the derivative of its C¹ representative.
-/
theorem grad_eq_toLp_deriv (u : protoDom ρ)
    (hdf : MemLp (deriv (rep ρ u)) 2 (densityMeasure ρ)) :
    grad ρ u = hdf.toLp (deriv (rep ρ u)) := by
  apply Lp.ext
  exact (coeFn_grad ρ u).trans hdf.coeFn_toLp.symm

/-- completeness provides a gradient limit for an approaching sequence. -/
theorem exists_grad_limit_of_approaches {s : ℕ → protoDom ρ}
    {u : Lp ℝ 2 (densityMeasure ρ)} (hs : (protoForm ρ).Approaches s u) :
    ∃ G : Lp ℝ 2 (densityMeasure ρ), Tendsto (fun n => grad ρ (s n)) atTop (𝓝 G) :=
  cauchySeq_tendsto_of_complete (cauchySeq_grad ρ hs.1)

/-- The limiting gradients of two C¹ approximations to the same L² class agree. -/
theorem grad_limit_unique {s t : ℕ → protoDom ρ} {u G H : Lp ℝ 2 (densityMeasure ρ)}
    (hs : Tendsto (fun n => (s n : Lp ℝ 2 (densityMeasure ρ))) atTop (𝓝 u))
    (ht : Tendsto (fun n => (t n : Lp ℝ 2 (densityMeasure ρ))) atTop (𝓝 u))
    (hG : Tendsto (fun n => grad ρ (s n)) atTop (𝓝 G))
    (hH : Tendsto (fun n => grad ρ (t n)) atTop (𝓝 H)) : G = H := by
  have hs' : Tendsto (fun n => ((rep_isC1Bounded ρ (s n)).memLp
      (densityMeasure ρ) 2).toLp (rep ρ (s n))) atTop (𝓝 ((Lp.memLp u).toLp u)) := by
    simpa only [toLp_rep, Lp.toLp_coeFn] using hs
  have ht' : Tendsto (fun n => ((rep_isC1Bounded ρ (t n)).memLp
      (densityMeasure ρ) 2).toLp (rep ρ (t n))) atTop (𝓝 ((Lp.memLp u).toLp u)) := by
    simpa only [toLp_rep, Lp.toLp_coeFn] using ht
  have hG' : Tendsto (fun n => ((rep_isC1Bounded ρ (s n)).deriv_memLp
      (densityMeasure ρ) 2).toLp (deriv (rep ρ (s n)))) atTop (𝓝 ((Lp.memLp G).toLp G)) := by
    simpa only [← grad_eq_toLp_deriv, Lp.toLp_coeFn] using hG
  have hH' : Tendsto (fun n => ((rep_isC1Bounded ρ (t n)).deriv_memLp
      (densityMeasure ρ) 2).toLp (deriv (rep ρ (t n)))) atTop (𝓝 ((Lp.memLp H).toLp H)) := by
    simpa only [← grad_eq_toLp_deriv, Lp.toLp_coeFn] using hH
  apply Lp.ext
  exact Foundations.weakDeriv_unique_of_C1_limits
    (SmoothDensity.contDiff (ρ := ρ)).continuous (SmoothDensity.pos (ρ := ρ))
    (fun n => (rep_isC1Bounded ρ (s n)).1) (fun n => (rep_isC1Bounded ρ (t n)).1)
    (fun n => (rep_isC1Bounded ρ (s n)).memLp (densityMeasure ρ) 2)
    (fun n => (rep_isC1Bounded ρ (t n)).memLp (densityMeasure ρ) 2) (Lp.memLp u)
    (fun n => (rep_isC1Bounded ρ (s n)).deriv_memLp (densityMeasure ρ) 2)
    (fun n => (rep_isC1Bounded ρ (t n)).deriv_memLp (densityMeasure ρ) 2)
    (Lp.memLp G) (Lp.memLp H) hs' ht' hG' hH'

/-- an approaching sequence together with its gradient limit. -/
theorem exists_approaches_grad_limit (u : (densityStructure ρ).dom) :
    ∃ G : Lp ℝ 2 (densityMeasure ρ), ∃ s : ℕ → protoDom ρ,
      (protoForm ρ).Approaches s u ∧ Tendsto (fun n => grad ρ (s n)) atTop (𝓝 G) := by
  obtain ⟨s, hs⟩ := ((protoForm ρ).mem_closureDom_iff u).mp u.property
  obtain ⟨G, hG⟩ := exists_grad_limit_of_approaches ρ hs
  exact ⟨G, s, hs, hG⟩

/-- The weak derivative of a closed-domain element, as a weighted L² class. -/
def weakDeriv (u : (densityStructure ρ).dom) : Lp ℝ 2 (densityMeasure ρ) :=
  Classical.choose (exists_approaches_grad_limit ρ u)

theorem weakDeriv_spec (u : (densityStructure ρ).dom) :
    ∃ s : ℕ → protoDom ρ, (protoForm ρ).Approaches s u ∧
      Tendsto (fun n => grad ρ (s n)) atTop (𝓝 (weakDeriv ρ u)) :=
  Classical.choose_spec (exists_approaches_grad_limit ρ u)

/-- Every approaching sequence converges to the same weak derivative. -/
theorem tendsto_grad_of_approaches {s : ℕ → protoDom ρ} {u : (densityStructure ρ).dom}
    (hs : (protoForm ρ).Approaches s u) :
    Tendsto (fun n => grad ρ (s n)) atTop (𝓝 (weakDeriv ρ u)) := by
  obtain ⟨G, hG⟩ := exists_grad_limit_of_approaches ρ hs
  obtain ⟨t, ht, hH⟩ := weakDeriv_spec ρ u
  exact (grad_limit_unique ρ hs.2 ht.2 hG hH) ▸ hG

/-- The weak derivative extends the original gradient. -/
@[simp] theorem weakDeriv_inclusion (u : protoDom ρ) :
    weakDeriv ρ ((protoForm ρ).inclusion u) = grad ρ u := by
  apply tendsto_nhds_unique (tendsto_grad_of_approaches ρ (s := fun _ => u) ?_)
    tendsto_const_nhds
  exact ⟨⟨cauchySeq_const _, cauchySeq_const _⟩, tendsto_const_nhds⟩

/-- additivity follows from the sum of approaching sequences. -/
theorem weakDeriv_add (u v : (densityStructure ρ).dom) :
    weakDeriv ρ (u + v) = weakDeriv ρ u + weakDeriv ρ v := by
  obtain ⟨s, hs, hG⟩ := weakDeriv_spec ρ u
  obtain ⟨t, ht, hH⟩ := weakDeriv_spec ρ v
  obtain ⟨r, hr, hR⟩ := weakDeriv_spec ρ (u + v)
  apply grad_limit_unique ρ (t := fun n => s n + t n) hr.2 (hs.2.add ht.2) hR
  simpa only [map_add] using hG.add hH

/-- homogeneity follows from scalar multiples of C¹ approximations. -/
theorem weakDeriv_smul (c : ℝ) (u : (densityStructure ρ).dom) :
    weakDeriv ρ (c • u) = c • weakDeriv ρ u := by
  obtain ⟨s, hs, hG⟩ := weakDeriv_spec ρ u
  obtain ⟨r, hr, hR⟩ := weakDeriv_spec ρ (c • u)
  apply grad_limit_unique ρ (t := fun n => c • s n) hr.2 (hs.2.const_smul c) hR
  simpa only [map_smul] using hG.const_smul c

/-- The weak derivative bundled as a linear map on the closed domain. -/
def weakDerivₗ : (densityStructure ρ).dom →ₗ[ℝ] Lp ℝ 2 (densityMeasure ρ) where
  toFun := weakDeriv ρ
  map_add' := weakDeriv_add ρ
  map_smul' := weakDeriv_smul ρ

end ErrorCalculus
