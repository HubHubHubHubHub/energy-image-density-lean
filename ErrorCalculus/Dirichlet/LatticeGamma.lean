import ErrorCalculus.Dirichlet.PiecewiseChain

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

theorem lipschitz_abs : LipschitzWith 1 (abs : ℝ → ℝ) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y

/-- Canonical absolute value in the domain. -/
def absComp (u : S.dom) : S.dom := S.lipschitzComp lipschitz_abs u

def posPart (u : S.dom) : S.dom := S.lipschitzComp (LipschitzWith.id.max_const 0) u

def negPart (u : S.dom) : S.dom := S.lipschitzComp (LipschitzWith.id.neg.max_const 0) u

theorem coeFn_absComp (u : S.dom) : (S.absComp u : Lp ℝ 2 μ) =ᵐ[μ]
    fun ω => |(u : Lp ℝ 2 μ) ω| := S.coeFn_lipschitzComp lipschitz_abs u

theorem coeFn_posPart (u : S.dom) : (S.posPart u : Lp ℝ 2 μ) =ᵐ[μ]
    fun ω => max ((u : Lp ℝ 2 μ) ω) 0 := S.coeFn_lipschitzComp _ u

theorem coeFn_negPart (u : S.dom) : (S.negPart u : Lp ℝ 2 μ) =ᵐ[μ]
    fun ω => max (-((u : Lp ℝ 2 μ) ω)) 0 := S.coeFn_lipschitzComp _ u

/-- Locality identifies the two affine branches of absolute value. -/
theorem gamma_abs_general (u : S.dom) : S.Γ (S.absComp u) (S.absComp u) =ᵐ[μ] S.Γ u u := by
  filter_upwards [S.gamma_eq_on_eq (S.absComp u) u,
    S.gamma_eq_on_eq (S.absComp u) (-u), S.coeFn_absComp u,
    Lp.coeFn_neg (u : Lp ℝ 2 μ)] with ω hp hn ha hneg
  by_cases h : 0 ≤ (u : Lp ℝ 2 μ) ω
  · exact hp (ha.trans (abs_of_nonneg h))
  · have hh := hn (ha.trans ((abs_of_neg (lt_of_not_ge h)).trans hneg.symm))
    simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hh

/-- Absolute value preserves the diagonal carré du champ on the form domain. -/
theorem Locality.gamma_abs (u : S.dom) :
    S.Γ (S.absComp u) (S.absComp u) =ᵐ[μ] S.Γ u u := S.gamma_abs_general u

theorem energy_abs (u : S.dom) : S.energy.E (S.absComp u) (S.absComp u) = S.energy.E u u := by
  simp only [ErrorData.energy_apply]
  rw [integral_congr_ae (S.gamma_abs_general u)]

/-- The positive part keeps the density exactly on the strictly positive set. -/
theorem gamma_posPart (u : S.dom) : S.Γ (S.posPart u) (S.posPart u) =ᵐ[μ]
    fun ω => if 0 < (u : Lp ℝ 2 μ) ω then S.Γ u u ω else 0 := by
  filter_upwards [S.gamma_eq_on_eq (S.posPart u) u,
    S.gamma_eq_zero_on_zero (S.posPart u), S.coeFn_posPart u] with ω he hz hp
  by_cases h : 0 < (u : Lp ℝ 2 μ) ω
  · rw [if_pos h]; exact he (hp.trans (max_eq_left h.le))
  · rw [if_neg h]; exact hz (hp.trans (max_eq_right (le_of_not_gt h)))

theorem gamma_negPart (u : S.dom) : S.Γ (S.negPart u) (S.negPart u) =ᵐ[μ]
    fun ω => if (u : Lp ℝ 2 μ) ω < 0 then S.Γ u u ω else 0 := by
  filter_upwards [S.gamma_eq_on_eq (S.negPart u) (-u),
    S.gamma_eq_zero_on_zero (S.negPart u), S.coeFn_negPart u,
    Lp.coeFn_neg (u : Lp ℝ 2 μ)] with ω he hz hp hn
  by_cases h : (u : Lp ℝ 2 μ) ω < 0
  · rw [if_pos h]
    have hh := he (hp.trans ((max_eq_left (by linarith)).trans hn.symm))
    simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hh
  · rw [if_neg h]; exact hz (hp.trans (max_eq_right (by linarith)))

theorem gamma_posPart_negPart (u : S.dom) : S.Γ (S.posPart u) (S.negPart u) =ᵐ[μ] 0 := by
  filter_upwards [S.gamma_posPart u, S.gamma_negPart u,
    S.toErrorData.gamma_cauchy_schwarz (S.posPart u) (S.negPart u)] with ω hp hn hc
  change S.Γ (S.posPart u) (S.negPart u) ω = 0
  rw [hp, hn] at hc
  by_cases h : 0 < (u : Lp ℝ 2 μ) ω
  · rw [if_pos h, if_neg (by linarith : ¬ (u : Lp ℝ 2 μ) ω < 0), mul_zero] at hc
    nlinarith [sq_nonneg (S.Γ (S.posPart u) (S.negPart u) ω)]
  · rw [if_neg h, zero_mul] at hc
    nlinarith [sq_nonneg (S.Γ (S.posPart u) (S.negPart u) ω)]

/-- Integration of an almost sure sum identity, with the normalization 1/2. -/
theorem energy_add_eq_of_gamma_add_eq (a b c d : S.dom)
    (h : ∀ᵐ ω ∂μ, S.Γ a a ω + S.Γ b b ω = S.Γ c c ω + S.Γ d d ω) :
    S.energy.E a a + S.energy.E b b = S.energy.E c c + S.energy.E d d := by
  simp only [ErrorData.energy_apply, ← mul_add]
  rw [← integral_add (L1.integrable_coeFn _) (L1.integrable_coeFn _),
    ← integral_add (L1.integrable_coeFn _) (L1.integrable_coeFn _), integral_congr_ae h]

theorem energy_posPart_add_negPart (u : S.dom) :
    S.energy.E (S.posPart u) (S.posPart u) + S.energy.E (S.negPart u) (S.negPart u) =
      S.energy.E u u := by
  have h := S.energy_add_eq_of_gamma_add_eq (S.posPart u) (S.negPart u) u 0 ?_
  · simpa using h
  · filter_upwards [S.gamma_posPart u, S.gamma_negPart u,
      S.gamma_eq_zero_on_zero u, Lp.coeFn_zero ℝ 1 μ] with ω hp hn hz h0
    simp only [map_zero, h0, Pi.zero_apply, add_zero, hp, hn]
    by_cases hp : 0 < (u : Lp ℝ 2 μ) ω
    · rw [if_pos hp, if_neg (by linarith : ¬ (u : Lp ℝ 2 μ) ω < 0), add_zero]
    · by_cases hn : (u : Lp ℝ 2 μ) ω < 0
      · rw [if_neg hp, if_pos hn, zero_add]
      · have he : (u : Lp ℝ 2 μ) ω = 0 := by linarith
        simp only [if_neg hp, if_neg hn, hz he, zero_add]

/-- Minimum, expressed using only the vector space domain and a scalar contraction. -/
def infDom (u v : S.dom) : S.dom := v - S.posPart (v-u)

def supDom (u v : S.dom) : S.dom := u + S.posPart (v-u)

theorem coeFn_infDom (u v : S.dom) : (S.infDom u v : Lp ℝ 2 μ) =ᵐ[μ]
    fun ω => min ((u : Lp ℝ 2 μ) ω) ((v : Lp ℝ 2 μ) ω) := by
  filter_upwards [Lp.coeFn_sub (v : Lp ℝ 2 μ) (S.posPart (v-u) : Lp ℝ 2 μ),
    S.coeFn_posPart (v-u), Lp.coeFn_sub (v : Lp ℝ 2 μ) (u : Lp ℝ 2 μ)] with ω hs hp hd
  simp only [infDom, Submodule.coe_sub, hs, Pi.sub_apply, hp, hd]
  by_cases h : (u : Lp ℝ 2 μ) ω ≤ (v : Lp ℝ 2 μ) ω
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]; ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]; ring

theorem coeFn_supDom (u v : S.dom) : (S.supDom u v : Lp ℝ 2 μ) =ᵐ[μ]
    fun ω => max ((u : Lp ℝ 2 μ) ω) ((v : Lp ℝ 2 μ) ω) := by
  filter_upwards [Lp.coeFn_add (u : Lp ℝ 2 μ) (S.posPart (v-u) : Lp ℝ 2 μ),
    S.coeFn_posPart (v-u), Lp.coeFn_sub (v : Lp ℝ 2 μ) (u : Lp ℝ 2 μ)] with ω hs hp hd
  simp only [supDom, Submodule.coe_add, hs, Pi.add_apply, hp, Submodule.coe_sub, hd, Pi.sub_apply]
  by_cases h : (u : Lp ℝ 2 μ) ω ≤ (v : Lp ℝ 2 μ) ω
  · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h)]; ring
  · rw [max_eq_left (le_of_not_ge h), max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]; ring

/-- The if expression is 1_{u<v}Γ[u] + 1_{u≥v}Γ[v]. -/
theorem gamma_inf (u v : S.dom) : S.Γ (S.infDom u v) (S.infDom u v) =ᵐ[μ]
    fun ω => if (u : Lp ℝ 2 μ) ω < (v : Lp ℝ 2 μ) ω then S.Γ u u ω else S.Γ v v ω := by
  filter_upwards [S.gamma_eq_on_eq (S.infDom u v) u, S.gamma_eq_on_eq (S.infDom u v) v,
    S.coeFn_infDom u v] with ω hu hv hm
  split_ifs with h
  · exact hu (hm.trans (min_eq_left h.le))
  · exact hv (hm.trans (min_eq_right (le_of_not_gt h)))

theorem gamma_sup (u v : S.dom) : S.Γ (S.supDom u v) (S.supDom u v) =ᵐ[μ]
    fun ω => if (u : Lp ℝ 2 μ) ω < (v : Lp ℝ 2 μ) ω then S.Γ v v ω else S.Γ u u ω := by
  filter_upwards [S.gamma_eq_on_eq (S.supDom u v) u, S.gamma_eq_on_eq (S.supDom u v) v,
    S.coeFn_supDom u v] with ω hu hv hm
  split_ifs with h
  · exact hv (hm.trans (max_eq_right h.le))
  · exact hu (hm.trans (max_eq_left (le_of_not_gt h)))

theorem energy_inf_add_sup (u v : S.dom) :
    S.energy.E (S.infDom u v) (S.infDom u v) + S.energy.E (S.supDom u v) (S.supDom u v) =
      S.energy.E u u + S.energy.E v v := by
  apply S.energy_add_eq_of_gamma_add_eq
  filter_upwards [S.gamma_inf u v, S.gamma_sup u v] with ω hi hs
  rw [hi, hs]; split_ifs <;> ring

end ErrorCalculus.ErrorStructure
