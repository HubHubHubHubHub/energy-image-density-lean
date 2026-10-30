import ErrorCalculus.Dirichlet.LipschitzChainGeneral
import ErrorCalculus.Dirichlet.GeneratorWeights
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Stroock Varopoulos

## Main results
The exact Stroock–Varopoulos identity for error structures.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- Polarization upgrades the diagonal rule to the mixed rule. -/
theorem gamma_lipschitzComp_mixed_general {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (u : S.dom) :
    S.Γ (S.lipschitzComp hF u) u =ᵐ[μ]
      fun ω => deriv F ((u : Lp ℝ 2 μ) ω) * S.Γ u u ω := by
  have he : S.lipschitzComp (hF.add LipschitzWith.id) u = S.lipschitzComp hF u + u := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [S.coeFn_lipschitzComp (hF.add LipschitzWith.id) u,
      S.coeFn_lipschitzComp hF u,
      Lp.coeFn_add (S.lipschitzComp hF u : Lp ℝ 2 μ) (u : Lp ℝ 2 μ)] with ω h₁ h₂ h₃
    simp only [Submodule.coe_add, h₁, h₃, Pi.add_apply, h₂, id_eq]
  have hp := S.gamma_lipschitzComp_general (hF.add LipschitzWith.id) u
  rw [he] at hp
  filter_upwards [hp, S.gamma_lipschitzComp_general hF u,
    S.gamma_add_ae (S.lipschitzComp hF u) u,
    S.ae_differentiableAt_on_gamma_ne_zero hF u] with ω hp hf ha hd
  by_cases hz : S.Γ u u ω = 0
  · rw [hz, mul_zero] at hp hf ⊢
    linarith
  · have hder := ((hd hz).hasDerivAt.add (hasDerivAt_id ((u : Lp ℝ 2 μ) ω))).deriv
    change deriv (fun x => F x + id x) ((u : Lp ℝ 2 μ) ω) = _ at hder
    rw [hder] at hp
    nlinarith

/-- The scalar power clipped outside the positive compact interval. -/
def clippedPower (ε M r x : ℝ) : ℝ := (max ε (min x M)) ^ r

theorem exists_lipschitzWith_clippedPower {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (r : ℝ) : ∃ L : ℝ≥0, LipschitzWith L (clippedPower ε M r) := by
  have hc : ContDiffOn ℝ 1 (fun x : ℝ => x ^ r) (Set.Icc ε M) := by
    intro x hx
    exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (hε.trans_le hx.1))).contDiffWithinAt
  obtain ⟨L, hL⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  have hclip : LipschitzWith 1 (fun x : ℝ => max ε (min x M)) :=
    (LipschitzWith.id.min_const M).const_max ε
  have hmem (x : ℝ) : max ε (min x M) ∈ Set.Icc ε M :=
    ⟨le_max_left _ _, max_le hεM (min_le_right _ _)⟩
  refine ⟨L, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  exact (hL.dist_le_mul _ (hmem x) _ (hmem y)).trans (by
    simpa only [NNReal.coe_one, one_mul] using
      mul_le_mul_of_nonneg_left (hclip.dist_le_mul x y) L.coe_nonneg)

def powComp {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (r : ℝ) (g : S.dom) : S.dom :=
  S.lipschitzComp (exists_lipschitzWith_clippedPower hε hεM r).choose_spec g

theorem coeFn_powComp {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (r : ℝ) (g : S.dom)
    (hg : ∀ᵐ ω ∂μ, ε ≤ (g : Lp ℝ 2 μ) ω ∧ (g : Lp ℝ 2 μ) ω ≤ M) :
    (S.powComp hε hεM r g : Lp ℝ 2 μ) =ᵐ[μ] fun ω => ((g : Lp ℝ 2 μ) ω) ^ r := by
  filter_upwards [S.coeFn_lipschitzComp
    (exists_lipschitzWith_clippedPower hε hεM r).choose_spec g, hg] with ω hc hg
  simp only [powComp, hc, clippedPower, min_eq_left hg.2, max_eq_right hg.1]

theorem deriv_clippedPower {ε M x : ℝ} (hx : ε < x ∧ x < M) (r : ℝ) :
    deriv (clippedPower ε M r) x = r * x ^ (r-1) := by
  have he : clippedPower ε M r =ᶠ[𝓝 x] fun y : ℝ => y ^ r := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    simp only [clippedPower, min_eq_left hy.2.le, max_eq_right hy.1.le]
  rw [he.deriv_eq, Real.deriv_rpow_const]

/-- Locality removes the two possible nondifferentiability levels. -/
theorem deriv_clippedPower_mul_gamma {ε M : ℝ} (_hε : 0 < ε) (_hεM : ε ≤ M)
    (r : ℝ) (g : S.dom)
    (hg : ∀ᵐ ω ∂μ, ε ≤ (g : Lp ℝ 2 μ) ω ∧ (g : Lp ℝ 2 μ) ω ≤ M) :
    ∀ᵐ ω ∂μ, deriv (clippedPower ε M r) ((g : Lp ℝ 2 μ) ω) =
      r * ((g : Lp ℝ 2 μ) ω) ^ (r-1) ∨ S.Γ g g ω = 0 := by
  filter_upwards [hg, S.gamma_eq_zero_on_const g ε, S.gamma_eq_zero_on_const g M]
    with ω hg hl hr
  by_cases he : (g : Lp ℝ 2 μ) ω = ε
  · exact Or.inr (hl he)
  by_cases hm : (g : Lp ℝ 2 μ) ω = M
  · exact Or.inr (hr hm)
  exact Or.inl (deriv_clippedPower ⟨lt_of_le_of_ne hg.1 (Ne.symm he), lt_of_le_of_ne hg.2 hm⟩ r)

theorem gamma_powComp {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (r : ℝ) (g : S.dom)
    (hg : ∀ᵐ ω ∂μ, ε ≤ (g : Lp ℝ 2 μ) ω ∧ (g : Lp ℝ 2 μ) ω ≤ M) :
    S.Γ (S.powComp hε hεM r g) (S.powComp hε hεM r g) =ᵐ[μ]
      fun ω => r^2 * ((g : Lp ℝ 2 μ) ω) ^ (2*r-2) * S.Γ g g ω := by
  filter_upwards [S.gamma_lipschitzComp_general
    (exists_lipschitzWith_clippedPower hε hεM r).choose_spec g,
    S.deriv_clippedPower_mul_gamma hε hεM r g hg, hg] with ω hc hd hg
  change S.Γ (S.powComp hε hεM r g) (S.powComp hε hεM r g) ω = _ at hc
  rw [hc]
  rcases hd with hd | hz
  · rw [hd, mul_pow, ← Real.rpow_mul_natCast (le_of_lt (hε.trans_le hg.1))]
    norm_num only [Nat.cast_ofNat]
    rw [show (r-1)*(2:ℝ) = 2*r-2 by ring]
  · simp only [hz, mul_zero]

theorem gamma_powComp_mixed {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (r : ℝ) (g : S.dom)
    (hg : ∀ᵐ ω ∂μ, ε ≤ (g : Lp ℝ 2 μ) ω ∧ (g : Lp ℝ 2 μ) ω ≤ M) :
    S.Γ g (S.powComp hε hεM r g) =ᵐ[μ]
      fun ω => r * ((g : Lp ℝ 2 μ) ω) ^ (r-1) * S.Γ g g ω := by
  rw [S.Γ_symm]
  filter_upwards [S.gamma_lipschitzComp_mixed_general
    (exists_lipschitzWith_clippedPower hε hεM r).choose_spec g,
    S.deriv_clippedPower_mul_gamma hε hεM r g hg] with ω hc hd
  change S.Γ (S.powComp hε hεM r g) g ω = _ at hc
  rw [hc]
  rcases hd with hd | hz
  · rw [hd]
  · simp only [hz, mul_zero]

/-- The weighted energy density in the formulas below is an actual integrable function. -/
theorem integrable_rpow_mul_gamma {ε M : ℝ} (hε : 0 < ε) (r : ℝ) (g : S.dom)
    (hg : ∀ᵐ ω ∂μ, ε ≤ (g : Lp ℝ 2 μ) ω ∧ (g : Lp ℝ 2 μ) ω ≤ M) :
    Integrable (fun ω => ((g : Lp ℝ 2 μ) ω) ^ r * S.Γ g g ω) μ := by
  have hc : ContinuousOn (fun x : ℝ => x ^ r) (Set.Icc ε M) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt (hε.trans_le hx.1)))).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc ε M)).bddAbove_image hc.norm
  apply (L1.integrable_coeFn (S.Γ g g)).bdd_mul
    (((Lp.aestronglyMeasurable (g : Lp ℝ 2 μ)).aemeasurable.pow_const r).aestronglyMeasurable)
  filter_upwards [hg] with ω hω
  exact hC ⟨(g : Lp ℝ 2 μ) ω, hω, rfl⟩

theorem powComp_one {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (g : S.dom)
    (hg : ∀ᵐ ω ∂μ, ε ≤ (g : Lp ℝ 2 μ) ω ∧ (g : Lp ℝ 2 μ) ω ≤ M) :
    S.powComp hε hεM 1 g = g := by
  apply Subtype.ext
  apply Lp.ext
  simpa only [Real.rpow_one] using S.coeFn_powComp hε hεM 1 g hg

theorem energy_pow_mixed {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (q : ℝ) (g : S.dom)
    (hg : ∀ᵐ ω ∂μ, ε ≤ (g : Lp ℝ 2 μ) ω ∧ (g : Lp ℝ 2 μ) ω ≤ M) :
    S.energy.E g (S.powComp hε hεM (q-1) g) =
      (1/2:ℝ) * (q-1) * ∫ ω, ((g : Lp ℝ 2 μ) ω) ^ (q-2) * S.Γ g g ω ∂μ := by
  rw [ErrorData.energy_apply, integral_congr_ae (S.gamma_powComp_mixed hε hεM (q-1) g hg)]
  simp_rw [show q-1-1 = q-2 by ring, mul_assoc]
  rw [integral_const_mul]

theorem energy_pow_half {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (q : ℝ) (g : S.dom)
    (hg : ∀ᵐ ω ∂μ, ε ≤ (g : Lp ℝ 2 μ) ω ∧ (g : Lp ℝ 2 μ) ω ≤ M) :
    S.energy.E (S.powComp hε hεM (q/2) g) (S.powComp hε hεM (q/2) g) =
      (q^2/8) * ∫ ω, ((g : Lp ℝ 2 μ) ω) ^ (q-2) * S.Γ g g ω ∂μ := by
  rw [ErrorData.energy_apply, integral_congr_ae (S.gamma_powComp hε hεM (q/2) g hg)]
  simp_rw [show 2*(q/2)-2 = q-2 by ring, mul_assoc]
  rw [integral_const_mul]
  ring

/-- The generator pairing against the bounded power is integrable. -/
theorem integrable_generator_mul_pow {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (r : ℝ) (g : S.dom) (hA : (g : Lp ℝ 2 μ) ∈ S.generatorDom)
    (hg : ∀ᵐ ω ∂μ, ε ≤ (g : Lp ℝ 2 μ) ω ∧ (g : Lp ℝ 2 μ) ω ≤ M) :
    Integrable (fun ω => (-S.generator ⟨g,hA⟩ ω) * ((g : Lp ℝ 2 μ) ω) ^ r) μ := by
  have hi := ((Lp.memLp (S.generator ⟨g,hA⟩)).integrable_mul
    (Lp.memLp (S.powComp hε hεM r g : Lp ℝ 2 μ))).neg
  apply hi.congr
  filter_upwards [S.coeFn_powComp hε hεM r g hg] with ω hc
  simp only [Pi.neg_apply, Pi.mul_apply, hc, neg_mul]

/-- Exact Stroock–Varopoulos identity: the generator is tested against a form-domain
power. No extra regularity of Γ or generator-domain membership of the power is used. -/
theorem stroock_varopoulos {ε M q : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (hq : 1 < q)
    (g : S.dom) (hA : (g : Lp ℝ 2 μ) ∈ S.generatorDom)
    (hg : ∀ᵐ ω ∂μ, ε ≤ (g : Lp ℝ 2 μ) ω ∧ (g : Lp ℝ 2 μ) ω ≤ M) :
    (∫ ω, (-S.generator ⟨g,hA⟩ ω) * ((g : Lp ℝ 2 μ) ω) ^ (q-1) ∂μ) =
      (4*(q-1)/q^2) *
        S.energy.E (S.powComp hε hεM (q/2) g) (S.powComp hε hεM (q/2) g) := by
  have he : S.energy.E g (S.powComp hε hεM (q-1) g) =
      -inner ℝ (S.generator ⟨g,hA⟩) (S.powComp hε hεM (q-1) g : Lp ℝ 2 μ) :=
    S.energy.energy_eq_neg_inner_generator S.energy_closed S.dense ⟨g,hA⟩ _
  have hi : (∫ ω, (-S.generator ⟨g,hA⟩ ω) * ((g : Lp ℝ 2 μ) ω) ^ (q-1) ∂μ) =
      S.energy.E g (S.powComp hε hεM (q-1) g) := by
    rw [he, L2.inner_def, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [S.coeFn_powComp hε hεM (q-1) g hg] with ω hc
    simp only [RCLike.inner_apply, conj_trivial, hc]
    ring
  rw [hi, S.energy_pow_mixed hε hεM q g hg, S.energy_pow_half hε hεM q g hg]
  have hq0 : q ≠ 0 := by linarith
  field_simp
  ring

theorem stroock_varopoulos_le {ε M q : ℝ} (hε : 0 < ε) (hεM : ε ≤ M) (hq : 1 < q)
    (g : S.dom) (hA : (g : Lp ℝ 2 μ) ∈ S.generatorDom)
    (hg : ∀ᵐ ω ∂μ, ε ≤ (g : Lp ℝ 2 μ) ω ∧ (g : Lp ℝ 2 μ) ω ≤ M) :
    (4*(q-1)/q^2) *
      S.energy.E (S.powComp hε hεM (q/2) g) (S.powComp hε hεM (q/2) g) ≤
      ∫ ω, (-S.generator ⟨g,hA⟩ ω) * ((g : Lp ℝ 2 μ) ω) ^ (q-1) ∂μ :=
  (S.stroock_varopoulos hε hεM hq g hA hg).ge

end ErrorCalculus.ErrorStructure
