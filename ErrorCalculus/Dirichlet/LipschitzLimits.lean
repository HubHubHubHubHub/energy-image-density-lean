import ErrorCalculus.Dirichlet.LipschitzEID
import ErrorCalculus.Dirichlet.ClosureCalculusLimits
import Mathlib.Analysis.Calculus.FDeriv.Measurable

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Subtraction in the bounded coefficient of an Lp product. -/
theorem boundedMul_sub_coefficient {p : ℝ≥0∞} (a b : Ω → ℝ)
    (ha : MemLp a ∞ μ) (hb : MemLp b ∞ μ) (g : Lp ℝ p μ) :
    boundedMul (a-b) (ha.sub hb) g = boundedMul a ha g - boundedMul b hb g := by
  apply Lp.ext
  filter_upwards [coeFn_boundedMul (a-b) (ha.sub hb) g,
    coeFn_boundedMul a ha g, coeFn_boundedMul b hb g,
    Lp.coeFn_sub (boundedMul a ha g) (boundedMul b hb g)] with ω h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.sub_apply, sub_mul]

namespace ErrorStructure
variable [IsProbabilityMeasure μ] (S : ErrorStructure Ω μ)

/-- ignore coefficients where the energy density vanishes. -/
def energyCoefficient (u : S.dom) (g : ℝ → ℝ) (ω : Ω) : ℝ :=
  if S.Γ u u ω = 0 then 0 else g (S.representative u ω)

theorem measurable_energyCoefficient (u : S.dom) {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (S.energyCoefficient u g) := by
  apply Measurable.ite
    (measurableSet_eq_fun (Lp.stronglyMeasurable (S.Γ u u)).measurable measurable_const)
    measurable_const (hg.comp (S.measurable_representative u))

theorem abs_energyCoefficient_le (u : S.dom) {g : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ x, |g x| ≤ C) (ω : Ω) :
    |S.energyCoefficient u g ω| ≤ C := by
  unfold energyCoefficient
  split_ifs <;> simp_all

theorem energyCoefficient_memLp (u : S.dom) {g : ℝ → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |g x| ≤ C) :
    MemLp (S.energyCoefficient u g) ∞ μ :=
  memLp_top_of_bound (S.measurable_energyCoefficient u hg).aestronglyMeasurable C
    (ae_of_all _ (S.abs_energyCoefficient_le u hC hb))

/-- Only this transfer lemma uses EID in the limit argument. -/
theorem HasEID.energyCoefficient_tendsto {u : S.dom} (hu : S.HasEID u)
    {g : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h : ∀ᵐ x ∂volume, Tendsto (fun n => g n x) atTop (𝓝 (f x))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => S.energyCoefficient u (g n) ω) atTop
      (𝓝 (S.energyCoefficient u f ω)) := by
  filter_upwards [hu.ae_of_ae_volume S h] with ω hω
  by_cases hz : S.Γ u u ω = 0
  · simp only [energyCoefficient, hz, ite_true]
    exact tendsto_const_nhds
  · simpa only [energyCoefficient, hz, ite_false] using hω hz

/-- Null-energy masking does not change any mixed chain-rule product. -/
theorem energyCoefficient_mul_gamma (u v : S.dom) (g : ℝ → ℝ) :
    (fun ω => S.energyCoefficient u g ω * S.Γ u v ω) =ᵐ[μ]
      fun ω => g (S.representative u ω) * S.Γ u v ω := by
  filter_upwards [S.gamma_eq_zero_of_diag_eq_zero u v] with ω hω
  by_cases hz : S.Γ u u ω = 0
  · simp [energyCoefficient, hz, hω hz]
  · simp [energyCoefficient, hz]

/-- Scalar Lipschitz compositions have an L² class for the fixed measurable representative. -/
theorem scalar_composition_memLp (u : S.dom) {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) : MemLp (fun ω => F (S.representative u ω)) 2 μ := by
  let p : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have h := composition_memLp (fun _ : Fin 1 => (u : Lp ℝ 2 μ)) (hF.comp p.lipschitz)
  apply MemLp.ae_eq _ h
  filter_upwards [S.coeFn_representative u] with ω hω
  exact congrArg F hω

/-- B.4(iii): the difference of two scalar chain rules controls the energy distance. -/
theorem scalar_chain_seminorm_bound (u w z : S.dom) (a b : Ω → ℝ)
    (ha : MemLp a ∞ μ) (hb : MemLp b ∞ μ)
    (hw : ∀ v : S.dom, ⇑(S.Γ w v) =ᵐ[μ] fun ω => a ω * S.Γ u v ω)
    (hz : ∀ v : S.dom, ⇑(S.Γ z v) =ᵐ[μ] fun ω => b ω * S.Γ u v ω) :
    S.energy.seminorm (w-z) ≤
      ‖boundedMul a ha (S.toErrorData.sqrtGamma u) - boundedMul b hb (S.toErrorData.sqrtGamma u)‖ := by
  have hd (v : S.dom) : ⇑(S.Γ (w-z) v) =ᵐ[μ]
      fun ω => (a ω-b ω) * S.Γ u v ω := by
    filter_upwards [S.toErrorData.gamma_sub_left_ae w z v, hw v, hz v] with ω h1 h2 h3
    rw [h1, h2, h3, sub_mul]
  have hdiag : ⇑(S.Γ (w-z) (w-z)) =ᵐ[μ]
      fun ω => (a ω-b ω)^2 * S.Γ u u ω := by
    have hdu := hd u
    rw [S.Γ_symm (w-z) u] at hdu
    filter_upwards [hd (w-z), hdu] with ω h1 h2
    rw [h1, h2]
    ring
  let g := boundedMul (a-b) (ha.sub hb) (S.toErrorData.sqrtGamma u)
  have he : ‖g‖^2 = 2 * S.energy.E (w-z) (w-z) := by
    rw [lp_two_norm_sq, ErrorData.energy_apply]
    have hi : (∫ ω, (g ω)^2 ∂μ) = ∫ ω, S.Γ (w-z) (w-z) ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [coeFn_boundedMul (a-b) (ha.sub hb) (S.toErrorData.sqrtGamma u),
        S.toErrorData.coeFn_sqrtGamma u, S.Γ_nonneg u, hdiag] with ω hm hs hp hd
      rw [show g ω = (a ω-b ω) * Real.sqrt (S.Γ u u ω) by rw [hm, hs]; rfl,
        mul_pow, Real.sq_sqrt hp, hd]
    rw [hi]
    ring
  rw [← boundedMul_sub_coefficient]
  change Real.sqrt (S.energy.E (w-z) (w-z)) ≤ ‖g‖
  apply Real.sqrt_le_iff.mpr
  exact ⟨norm_nonneg _, by nlinarith [S.energy.nonneg (w-z)]⟩

/-- abstract closedness step for bounded convergent scalar chain coefficients. -/
theorem closed_scalar_chain (u : S.dom) (w : ℕ → S.dom) (z : Lp ℝ 2 μ)
    (a : ℕ → Ω → ℝ) (b : Ω → ℝ)
    (ha : ∀ n, MemLp (a n) ∞ μ) (hb : MemLp b ∞ μ) {C : ℝ} (hC : 0 ≤ C)
    (hCa : ∀ n, ∀ᵐ ω ∂μ, |a n ω| ≤ C) (hCb : ∀ᵐ ω ∂μ, |b ω| ≤ C)
    (hab : ∀ᵐ ω ∂μ, Tendsto (fun n => a n ω) atTop (𝓝 (b ω)))
    (hw : ∀ n v, ⇑(S.Γ (w n) v) =ᵐ[μ] fun ω => a n ω * S.Γ u v ω)
    (hwz : Tendsto (fun n => (w n : Lp ℝ 2 μ)) atTop (𝓝 z)) :
    ∃ hz : z ∈ S.dom, ∀ v : S.dom,
      ⇑(S.Γ ⟨z,hz⟩ v) =ᵐ[μ] fun ω => b ω * S.Γ u v ω := by
  have hsub : ∀ᵐ ω ∂μ, Tendsto (fun n => (a n-b) ω) atTop (𝓝 0) := by
    filter_upwards [hab] with ω ht
    simpa using ht.sub_const (b ω)
  have hbound n : ∀ᵐ ω ∂μ, |(a n-b) ω| ≤ 2*C := by
    filter_upwards [hCa n, hCb] with ω h1 h2
    exact (abs_sub _ _).trans (by linarith)
  have htwo := boundedMul_tendsto_zero_two (fun n => a n-b) (fun n => (ha n).sub hb)
    (S.toErrorData.sqrtGamma u) (mul_nonneg (by norm_num) hC) hbound hsub
  have htwo' := htwo.congr (fun n => boundedMul_sub_coefficient (a n) b (ha n) hb _)
  have hc := (tendsto_sub_nhds_zero_iff.mp htwo').cauchySeq
  have henergy : S.energy.IsCauchy w := by
    refine ⟨hwz.cauchySeq, Metric.cauchySeq_iff.mpr ?_⟩
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm, ← map_sub, S.energy.norm_j]
    exact (S.scalar_chain_seminorm_bound u (w m) (w n) (a m) (a n)
      (ha m) (ha n) (hw m) (hw n)).trans_lt (by simpa only [dist_eq_norm] using hN m hm n hn)
  obtain ⟨hz, he⟩ := S.energy_closed w henergy z hwz
  change z ∈ S.dom at hz
  refine ⟨hz, fun v => ?_⟩
  have hej := S.energy.energy_tendsto_zero_iff.mp he
  simp_rw [map_sub] at hej
  have hj := tendsto_sub_nhds_zero_iff.mp hej
  have hgamma := S.toErrorData.gamma_tendsto_of_energy hj
    (tendsto_const_nhds (x := S.energy.j v))
  rw [S.toErrorData.completedGamma_j] at hgamma
  have hprod := boundedMul_tendsto_zero_one (fun n => a n-b) (fun n => (ha n).sub hb)
    (S.Γ u v) hbound hsub
  have hprod' := hprod.congr (fun n => boundedMul_sub_coefficient (a n) b (ha n) hb _)
  have hp := tendsto_sub_nhds_zero_iff.mp hprod'
  have heq n : S.Γ (w n) v = boundedMul (a n) (ha n) (S.Γ u v) :=
    Lp.ext ((hw n v).trans (coeFn_boundedMul (a n) (ha n) (S.Γ u v)).symm)
  simp_rw [heq] at hgamma
  have hid := tendsto_nhds_unique hgamma hp
  exact (Lp.ext_iff.mp hid).trans (coeFn_boundedMul b hb (S.Γ u v))

end ErrorStructure
end ErrorCalculus
