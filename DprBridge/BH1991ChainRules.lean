import DprBridge.BH1991LevelCancellation
import DprBridge.BH1991GammaLocality
import DprBridge.BH1991NormalContractions
import DprBridge.BH1991Printed

/-!
# Centered scalar chains and bounded Leibniz rules

## Main results
Centered scalar chain rules and bounded products are constructed on the original arbitrary BH
measure, with Γ = 2γ. The multivariate calculus is developed in `DprBridge.BH1991ChainCurrents`.

References: Bouleau–Hirsch (1991), ch. I, §§ 3–6, especially I.6.1.3, pp. 36–37; the EID
formulation in ch. V, p. 185, and Notes, p. 302; Eriksson-Bique–Murugan, Section 4.2.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ErrorCalculus
open scoped NNReal ENNReal ContDiff
universe u

namespace DprBridge.BH1991.DirichletForm

/-- Centering the real interpolant gives the sum of its centered clamp terms. -/
theorem centered_interpSum_eq (F : ℝ → ℝ) (a δ : ℝ) (N : ℕ) (t : ℝ) :
    interpSum F a δ N t - interpSum F a δ N 0 =
      ∑ k ∈ Finset.range N, (F (a + (k + 1) * δ) - F (a + k * δ)) / δ *
        (max (a + k * δ) (min t (a + (k + 1) * δ)) -
          max (a + k * δ) (min 0 (a + (k + 1) * δ))) := by
  simp only [interpSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The real interpolant of an L-Lipschitz function is L-Lipschitz for positive mesh size. -/
theorem lipschitzWith_interpSum {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    LipschitzWith L (interpSum F a δ N) := by
  have hs : ∀ k : ℕ,
      |(F (a + (k + 1) * δ) - F (a + k * δ)) / δ| ≤ (L : ℝ) := by
    intro k
    rw [abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
    have h := hF.dist_le_mul (a + (k + 1) * δ) (a + k * δ)
    simpa only [Real.dist_eq, show a + (k + 1) * δ - (a + k * δ) = δ by ring,
      abs_of_pos hδ] using h
  have hxy : ∀ x y : ℝ, x ≤ y →
      |interpSum F a δ N y - interpSum F a δ N x| ≤ (L : ℝ) * |y - x| := by
    intro x y hxy
    let c : ℕ → ℝ → ℝ := fun k t => max (a + k * δ) (min t (a + (k + 1) * δ))
    have hc : ∀ k, 0 ≤ c k y - c k x := fun k =>
      sub_nonneg.mpr (max_le_max_left _ (min_le_min_right _ hxy))
    have ht : (∑ k ∈ Finset.range N, (c k y - c k x)) =
        max a (min y (a + N * δ)) - max a (min x (a + N * δ)) := by
      have hy := sum_clamp_telescope a hδ.le N y
      have hx := sum_clamp_telescope a hδ.le N x
      have he : (∑ k ∈ Finset.range N, (c k y - c k x)) =
          (∑ k ∈ Finset.range N, (c k y - (a + k * δ))) -
            (∑ k ∈ Finset.range N, (c k x - (a + k * δ))) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [he, hy, hx]
      ring
    have hcl : LipschitzWith 1 (fun t : ℝ => max a (min t (a + N * δ))) :=
      (LipschitzWith.id.min_const _).const_max _
    have hbound : max a (min y (a + N * δ)) - max a (min x (a + N * δ)) ≤ |y - x| :=
      (le_abs_self _).trans (by simpa only [Real.dist_eq, NNReal.coe_one, one_mul]
        using (hcl.dist_le_mul y x))
    have he : interpSum F a δ N y - interpSum F a δ N x =
        ∑ k ∈ Finset.range N, (F (a + (k + 1) * δ) - F (a + k * δ)) / δ *
          (c k y - c k x) := by
      simp only [interpSum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [c]
      ring
    rw [he]
    calc
      _ ≤ ∑ k ∈ Finset.range N,
          |(F (a + (k + 1) * δ) - F (a + k * δ)) / δ * (c k y - c k x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range N, (L : ℝ) * (c k y - c k x) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul, abs_of_nonneg (hc k)]
        exact mul_le_mul_of_nonneg_right (hs k) (hc k)
      _ = (L : ℝ) * (max a (min y (a + N * δ)) - max a (min x (a + N * δ))) := by
        rw [← Finset.mul_sum, ht]
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound L.2
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq]
  rcases le_total x y with h | h
  · simpa only [abs_sub_comm] using hxy x y h
  · exact hxy y x h

/-- The centered interpolants of a Lipschitz function converge pointwise to F(t) - F(0). -/
theorem tendsto_centered_interpSum {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (t : ℝ) :
    Tendsto (fun n => interpSum F (gridStart n) (gridStep n) (gridCount n) t -
      interpSum F (gridStart n) (gridStep n) (gridCount n) 0) atTop (𝓝 (F t - F 0)) := by
  have h : ∀ x y, |F x - F y| ≤ (L : ℝ) * |x - y| := fun x y => by
    simpa only [Real.dist_eq] using hF.dist_le_mul x y
  have ht := (tendsto_add_interpSum_grid_sub F L.2 h t).sub
    (tendsto_add_interpSum_grid_sub F L.2 h 0)
  have ht' := ht.add_const (F t - F 0)
  simp only [sub_self, zero_add] at ht'
  convert ht' using 1
  ext n
  ring

variable {X : Type u} [MeasurableSpace X] {m : Measure X} (D : DirichletForm m)

/--
The clipped scalar profile, centered before composition in the form space.
Source: BH 1991, Chapter I, Sections 3--4 (contractions fixing zero).
-/
def centeredClamp (a b : ℝ) (v : D.toCapacity.Space) : D.toCapacity.Space :=
  D.centeredComp (fun t => max a (min t b))
    ((LipschitzWith.id.min_const b).const_max a) v

/-- The centered clamp is represented almost everywhere by the centered clipped profile. -/
theorem coe_centeredClamp (a b : ℝ) (v : D.toCapacity.Space) :
    ⇑(D.toCapacity.toLp (D.centeredClamp a b v)) =ᵐ[m] fun x =>
      max a (min (D.toCapacity.toLp v x) b) - max a (min 0 b) :=
  D.coe_centeredComp _ _ v

/--
For a local form and a <= b, the centered clamp multiplies Gamma by 1_(a,b). Source: BH 1991,
Chapter I, Section 6.
-/
theorem gamma_centeredClamp (hL : D.Local) (G : D.CarreDuChamp)
    (a b : ℝ) (hab : a ≤ b) (v w : D.toCapacity.Space) :
    ⇑(G.Γ (D.centeredClamp a b v) w) =ᵐ[m] fun x =>
      (Set.Ioo a b).indicator 1 (D.toCapacity.toLp v x) * G.Γ v w x := by
  obtain ⟨q, hq, hγ⟩ := D.centered_clampRule hL G (D.form.formToDomain v) a b hab
  have he : D.centeredClamp a b v = D.form.formToDomain.symm q := by
    apply D.toCapacity.eq_of_ae
    exact (D.coe_centeredClamp a b v).trans hq.symm
  rw [he]
  have hh := hγ (D.form.formToDomain w)
  simp only [LinearEquiv.symm_apply_apply] at hh
  filter_upwards [hh] with x hx
  rw [hx]
  change {x | a < D.toCapacity.toLp v x ∧ D.toCapacity.toLp v x < b}.indicator
    (fun x => G.Γ v w x) x = _
  by_cases h : a < D.toCapacity.toLp v x ∧ D.toCapacity.toLp v x < b
  · rw [Set.indicator_of_mem (show x ∈ {x | a < D.toCapacity.toLp v x ∧
        D.toCapacity.toLp v x < b} from h),
      Set.indicator_of_mem (show D.toCapacity.toLp v x ∈ Set.Ioo a b from h)]
    simp only [Pi.one_apply, one_mul]
  · rw [Set.indicator_of_notMem (show x ∉ {x | a < D.toCapacity.toLp v x ∧
        D.toCapacity.toLp v x < b} from h),
      Set.indicator_of_notMem (show D.toCapacity.toLp v x ∉ Set.Ioo a b from h)]
    simp only [zero_mul]

/-- The centered affine interpolant is the finite weighted sum of centered clamps. -/
def centeredInterp (F : ℝ → ℝ) (a δ : ℝ) (N : ℕ)
    (v : D.toCapacity.Space) : D.toCapacity.Space :=
  ∑ k ∈ Finset.range N, ((F (a + (k + 1) * δ) - F (a + k * δ)) / δ) •
    D.centeredClamp (a + k * δ) (a + (k + 1) * δ) v

/-- The form-space interpolant is represented almost everywhere by the centered real interpolant. -/
theorem coe_centeredInterp (F : ℝ → ℝ) (a δ : ℝ) (N : ℕ) (v : D.toCapacity.Space) :
    ⇑(D.toCapacity.toLp (D.centeredInterp F a δ N v)) =ᵐ[m] fun x =>
      interpSum F a δ N (D.toCapacity.toLp v x) - interpSum F a δ N 0 := by
  simp only [centeredInterp, map_sum, map_smul]
  filter_upwards [lp_coeFn_sum (Finset.range N) _,
    (ae_all_iff.mpr fun k : ℕ => D.coe_centeredClamp (a + k * δ) (a + (k + 1) * δ) v),
    (ae_all_iff.mpr fun k : ℕ => Lp.coeFn_smul
      ((F (a + (k + 1) * δ) - F (a + k * δ)) / δ)
      (D.toCapacity.toLp (D.centeredClamp (a + k * δ) (a + (k + 1) * δ) v)))] with x hs hc hm
  rw [hs, centered_interpSum_eq]
  apply Finset.sum_congr rfl
  intro k _
  rw [hm, Pi.smul_apply, smul_eq_mul, hc]

/-- For a local form, the centered interpolant multiplies Gamma by the interpolation slope. -/
theorem gamma_centeredInterp (hL : D.Local) (G : D.CarreDuChamp)
    (F : ℝ → ℝ) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (v w : D.toCapacity.Space) :
    ⇑(G.Γ (D.centeredInterp F a δ N v) w) =ᵐ[m] fun x =>
      interpSlope F a δ N (D.toCapacity.toLp v x) * G.Γ v w x := by
  simp only [centeredInterp, map_sum, sum_apply, map_smul, smul_apply]
  filter_upwards [lp_coeFn_sum (Finset.range N) _,
    (ae_all_iff.mpr fun k : ℕ => D.gamma_centeredClamp hL G
      (a + k * δ) (a + (k + 1) * δ) (by linarith) v w),
    (ae_all_iff.mpr fun k : ℕ => Lp.coeFn_smul
      ((F (a + (k + 1) * δ) - F (a + k * δ)) / δ)
      (G.Γ (D.centeredClamp (a + k * δ) (a + (k + 1) * δ) v) w))] with x hs hc hm
  rw [hs, interpSlope, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [hm, Pi.smul_apply, smul_eq_mul, hc, mul_assoc]

/--
For a local form, the diagonal Gamma of a centered interpolant is the slope squared times Gamma.
-/
theorem gamma_centeredInterp_self (hL : D.Local) (G : D.CarreDuChamp)
    (F : ℝ → ℝ) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (v : D.toCapacity.Space) :
    ⇑(G.Γ (D.centeredInterp F a δ N v) (D.centeredInterp F a δ N v)) =ᵐ[m]
      fun x => (interpSlope F a δ N (D.toCapacity.toLp v x)) ^ 2 * G.Γ v v x := by
  have h1 := D.gamma_centeredInterp hL G F a hδ N v (D.centeredInterp F a δ N v)
  have h2 := D.gamma_centeredInterp hL G F a hδ N v v
  rw [G.symm v (D.centeredInterp F a δ N v)] at h1
  filter_upwards [h1, h2] with x h1 h2
  rw [h1, h2]
  ring

/--
For a local form and an L-Lipschitz profile, interpolant energy is at most L squared times energy.
-/
theorem energy_centeredInterp_le (hL : D.Local) (G : D.CarreDuChamp)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (v : D.toCapacity.Space) :
    D.toCapacity.ener (D.centeredInterp F a δ N v) (D.centeredInterp F a δ N v) ≤
      (L : ℝ) ^ 2 * D.toCapacity.ener v v := by
  have hF' : ∀ x y : ℝ, |F x - F y| ≤ (L : ℝ) * |x - y| := by
    intro x y
    have h := hF.dist_le_mul x y
    rwa [Real.dist_eq, Real.dist_eq] at h
  have hb : ∀ t, |interpSlope F a δ N t| ≤ (L : ℝ) :=
    abs_interpSlope_le L.2 hF' a hδ N
  have hi : (∫ x, G.Γ (D.centeredInterp F a δ N v) (D.centeredInterp F a δ N v) x ∂m) ≤
      ∫ x, (L : ℝ) ^ 2 * G.Γ v v x ∂m := by
    apply integral_mono_ae (L1.integrable_coeFn _) ((L1.integrable_coeFn _).const_mul _)
    filter_upwards [D.gamma_centeredInterp_self hL G F a hδ N v, G.nonneg v] with x hx hp
    rw [hx]
    apply mul_le_mul_of_nonneg_right _ hp
    have hs := pow_le_pow_left₀ (abs_nonneg _) (hb (D.toCapacity.toLp v x)) 2
    simpa only [sq_abs] using hs
  rw [integral_const_mul, D.integral_gamma hL G, D.integral_gamma hL G] at hi
  linarith

/--
Centered interpolants converge in L2 to any representative of the centered Lipschitz composition.
-/
theorem tendsto_centeredInterp_L2 {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (v : D.toCapacity.Space) (w : Lp ℝ 2 m)
    (hw : ⇑w =ᵐ[m] fun x => F (D.toCapacity.toLp v x) - F 0) :
    Tendsto (fun n => D.toCapacity.toLp
      (D.centeredInterp F (gridStart n) (gridStep n) (gridCount n) v)) atTop (𝓝 w) := by
  have ht := Foundations.tendsto_toLp_dominated m
    (fun n => Lp.memLp (D.toCapacity.toLp
      (D.centeredInterp F (gridStart n) (gridStep n) (gridCount n) v)))
    (Lp.memLp w) ((Lp.memLp (D.toCapacity.toLp v)).norm.const_mul (L : ℝ))
    (fun n => ?_) ?_
  · have he : ∀ z : Lp ℝ 2 m, (Lp.memLp z).toLp _ = z :=
      fun z => Lp.ext (Lp.memLp z).coeFn_toLp
    simpa only [he] using ht
  · filter_upwards [D.coe_centeredInterp F (gridStart n) (gridStep n) (gridCount n) v] with x hx
    rw [hx, Real.norm_eq_abs, Real.norm_eq_abs]
    simpa only [Real.dist_eq, sub_zero] using
      (lipschitzWith_interpSum hF (gridStart n) (gridStep_pos n) (gridCount n)).dist_le_mul
        (D.toCapacity.toLp v x) 0
  · filter_upwards [hw, ae_all_iff.mpr (fun n =>
      D.coe_centeredInterp F (gridStart n) (gridStep n) (gridCount n) v)] with x hx hn
    simp only [hn, hx]
    exact tendsto_centered_interpSum hF _

/--
An energy bound and L2 convergence imply convergence of Gamma integrals against bounded form tests.
-/
theorem tendsto_integral_mul_gamma_of_energy_bound (G : D.CarreDuChamp)
    {p : ℕ → D.toCapacity.Space} {q : D.toCapacity.Space} {C : ℝ}
    (hE : ∀ n, D.toCapacity.ener (p n) (p n) ≤ C)
    (hT : Tendsto (fun n => D.toCapacity.toLp (p n)) atTop (𝓝 (D.toCapacity.toLp q)))
    {z : D.toCapacity.Space} (hz : z ∈ D.toCapacity.bddSpace) (v : D.toCapacity.Space) :
    Tendsto (fun n => ∫ x, D.toCapacity.toLp z x * G.Γ (p n) v x ∂m) atTop
      (𝓝 (∫ x, D.toCapacity.toLp z x * G.Γ q v x ∂m)) := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hT)
  have hR : ∀ n, ‖p n‖ ≤ Real.sqrt (B ^ 2 + C) := by
    intro n
    have hn := D.form.formSpace_norm_sq (p n)
    have hb : ‖D.toCapacity.toLp (p n)‖ ≤ B := hB _ ⟨n, rfl⟩
    have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [← Real.sqrt_sq (norm_nonneg (p n))]
    apply Real.sqrt_le_sqrt
    have he := hE n
    rw [D.toCapacity.ener_apply] at he
    change ‖p n‖ ^ 2 = ‖D.toCapacity.toLp (p n)‖ ^ 2 +
      D.form.E (D.form.formToDomain (p n)) (D.form.formToDomain (p n)) at hn
    linarith
  exact D.toCapacity.tendsto_apply_of_bounded hR hT
    ((D.toCapacity.pairCLM hz).comp (G.Γ.flip v))

/--
For a local form, a centered Lipschitz composition obeys the scalar Gamma chain rule when the
profile has the prescribed strict derivative outside countably many levels. The derivative values on
those exceptional levels are arbitrary. Source: BH 1991, Chapter I, Section 6.
-/
theorem gamma_centered_comp (hL : D.Local) (G : D.CarreDuChamp)
    {F F' : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) {N : Set ℝ}
    (hN : N.Countable) (hd : ∀ t ∉ N, HasStrictDerivAt F (F' t) t)
    (u v w : D.toCapacity.Space)
    (hw : ⇑(D.toCapacity.toLp w) =ᵐ[m] fun x => F (D.toCapacity.toLp u x) - F 0) :
    ⇑(G.Γ w v) =ᵐ[m] fun x => F' (D.toCapacity.toLp u x) * G.Γ u v x := by
  let W : ℕ → D.toCapacity.Space := fun n =>
    D.centeredInterp F (gridStart n) (gridStep n) (gridCount n) u
  let S : ℕ → ℝ → ℝ := fun n => interpSlope F (gridStart n) (gridStep n) (gridCount n)
  have hE : ∀ n, D.toCapacity.ener (W n) (W n) ≤ (L : ℝ) ^ 2 * D.toCapacity.ener u u :=
    fun n => D.energy_centeredInterp_le hL G hF _ (gridStep_pos n) _ u
  have hT := D.tendsto_centeredInterp_L2 hF u (D.toCapacity.toLp w) hw
  have hγW : ∀ n, ⇑(G.Γ (W n) v) =ᵐ[m] fun x => S n (D.toCapacity.toLp u x) * G.Γ u v x :=
    fun n => D.gamma_centeredInterp hL G F _ (gridStep_pos n) _ u v
  let N' : Set ℝ := N ∪ Set.range ((↑) : ℚ → ℝ)
  have hzero : ∀ᵐ x ∂m, D.toCapacity.toLp u x ∈ N' → G.Γ u v x = 0 :=
    D.gamma_eq_zero_on_countable_levels hL G u v (hN.union (Set.countable_range _))
  have hF' : ∀ x y : ℝ, |F x - F y| ≤ (L : ℝ) * |x - y| := by
    intro x y
    have h := hF.dist_le_mul x y
    rwa [Real.dist_eq, Real.dist_eq] at h
  have hbd : ∀ n t, |S n t| ≤ (L : ℝ) := fun n t =>
    abs_interpSlope_le L.2 hF' _ (gridStep_pos n) _ t
  have hpt : ∀ᵐ x ∂m, Tendsto (fun n => S n (D.toCapacity.toLp u x) * G.Γ u v x) atTop
      (𝓝 (F' (D.toCapacity.toLp u x) * G.Γ u v x)) := by
    filter_upwards [hzero] with x hx
    by_cases hm : D.toCapacity.toLp u x ∈ N'
    · rw [hx hm]
      simp only [mul_zero]
      exact tendsto_const_nhds
    · exact (tendsto_interpSlope_grid (hd _ (fun h => hm (Or.inl h)))
        (fun h => hm (Or.inr h))).mul_const _
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => S n (D.toCapacity.toLp u x) * G.Γ u v x) m :=
    fun n => (((measurable_interpSlope _ _ _ _).comp_aemeasurable
      (Lp.aestronglyMeasurable (D.toCapacity.toLp u)).aemeasurable).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable _)
  have htm := aestronglyMeasurable_of_tendsto_ae atTop hmeas hpt
  have hgi : Integrable (fun x => G.Γ u v x) m := L1.integrable_coeFn _
  have hlimb : ∀ᵐ x ∂m,
      ‖F' (D.toCapacity.toLp u x) * G.Γ u v x‖ ≤ (L : ℝ) * ‖G.Γ u v x‖ := by
    filter_upwards [hpt] with x hx
    refine le_of_tendsto' hx.norm (fun n => ?_)
    rw [norm_mul, Real.norm_eq_abs (S n _)]
    exact mul_le_mul_of_nonneg_right (hbd n _) (norm_nonneg _)
  have hti := Integrable.mono' (hgi.norm.const_mul (L : ℝ)) htm hlimb
  apply D.toCapacity.ae_eq_of_integral_mul_eq D.denseRange_toCapacity (L1.integrable_coeFn _) hti
  intro z hz
  have h1 := D.tendsto_integral_mul_gamma_of_energy_bound G hE hT hz v
  obtain ⟨Cz, hCz⟩ := hz
  have hcongr : ∀ n, ∫ x, D.toCapacity.toLp z x * G.Γ (W n) v x ∂m =
      ∫ x, D.toCapacity.toLp z x * (S n (D.toCapacity.toLp u x) * G.Γ u v x) ∂m := fun n =>
    integral_congr_ae ((hγW n).mono fun x h => by dsimp only; rw [h])
  have h2 : Tendsto (fun n => ∫ x, D.toCapacity.toLp z x * G.Γ (W n) v x ∂m) atTop
      (𝓝 (∫ x, D.toCapacity.toLp z x * (F' (D.toCapacity.toLp u x) * G.Γ u v x) ∂m)) := by
    simp only [hcongr]
    refine tendsto_integral_of_dominated_convergence
      (fun x => Cz * ((L : ℝ) * ‖G.Γ u v x‖))
      (fun n => (Lp.aestronglyMeasurable _).mul (hmeas n)) ((hgi.norm.const_mul _).const_mul _)
      (fun n => ?_) ?_
    · filter_upwards [hCz] with x hx
      rw [norm_mul, norm_mul, Real.norm_eq_abs (D.toCapacity.toLp z x),
        Real.norm_eq_abs (S n _)]
      exact mul_le_mul hx (mul_le_mul_of_nonneg_right (hbd n _) (norm_nonneg _)) (by positivity)
        ((abs_nonneg _).trans hx)
    · filter_upwards [hpt] with x hx
      exact hx.const_mul _
  exact tendsto_nhds_unique h1 h2

/--
For a local BH form with a carre du champ, centered Lipschitz compositions belong to its domain.
Source: BH 1991, Chapter I, Sections 3--4 (contractions fixing zero).
-/
theorem exists_centered_lipschitz (hL : D.Local) (G : D.CarreDuChamp)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (u : D.form.dom) :
    ∃ w : D.form.dom, ⇑(w : Lp ℝ 2 m) =ᵐ[m] fun x => F ((u : Lp ℝ 2 m) x) - F 0 := by
  have hm := (lipschitzWith_centered hF).comp_memLp (sub_self _) (Lp.memLp (u : Lp ℝ 2 m))
  let w : Lp ℝ 2 m := hm.toLp _
  have hw := hm.coeFn_toLp
  have ht := D.tendsto_centeredInterp_L2 hF (D.form.formToDomain.symm u) w hw
  have he := fun n => D.energy_centeredInterp_le hL G hF (gridStart n)
    (gridStep_pos n) (gridCount n) (D.form.formToDomain.symm u)
  simp only [D.toCapacity.ener_apply] at he
  obtain ⟨hw', _⟩ := D.closed.mem_dom_of_tendsto_of_energy_le ht he
  exact ⟨⟨w, hw'⟩, hw⟩

/--
For a local BH form, every centered C1 Lipschitz composition lies in the domain and satisfies
its scalar Gamma chain identity, on an arbitrary measure.
Source: BH 1991, I.6.1.3, pp. 36--37; EBM, Section 4.2.
-/
theorem centered_scalar_chainRule :
  D.Local → ∀ (G : D.CarreDuChamp) (f : D.form.dom) (F : ℝ → ℝ) (L : ℝ≥0),
    ContDiff ℝ 1 F → LipschitzWith L F →
    ∃ w : D.form.dom,
      (⇑(w : Lp ℝ 2 m) =ᵐ[m] fun x => F ((f : Lp ℝ 2 m) x) - F 0) ∧
      ∀ g : D.form.dom,
        ⇑(G.Γ (D.form.formToDomain.symm w) (D.form.formToDomain.symm g)) =ᵐ[m]
          fun x => deriv F ((f : Lp ℝ 2 m) x) *
            G.Γ (D.form.formToDomain.symm f) (D.form.formToDomain.symm g) x := by
  intro hL G f F L hC hF
  obtain ⟨w, hw⟩ := D.exists_centered_lipschitz hL G hF f
  refine ⟨w, hw, fun g => ?_⟩
  exact D.gamma_centered_comp hL G hF Set.countable_empty
    (fun _ _ => hC.contDiffAt.hasStrictDerivAt one_ne_zero)
    (D.form.formToDomain.symm f) (D.form.formToDomain.symm g) (D.form.formToDomain.symm w) hw

/--
For a local form, a domain representative of the square of a bounded argument satisfies Gamma(f
squared, v) = 2 f Gamma(f, v) almost everywhere.
Source: BH 1991, Chapter I, Section 6; EBM, Section 4.2.
-/
theorem gamma_bounded_square (hL : D.Local) (G : D.CarreDuChamp)
    (f q v : D.toCapacity.Space) {M : ℝ}
    (hM : ∀ᵐ x ∂m, |D.toCapacity.toLp f x| ≤ M)
    (hq : ⇑(D.toCapacity.toLp q) =ᵐ[m] fun x => (D.toCapacity.toLp f x) ^ 2) :
    ⇑(G.Γ q v) =ᵐ[m] fun x => 2 * D.toCapacity.toLp f x * G.Γ f v x := by
  let R : ℝ := max M 0 + 1
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hMR : M < R := by dsimp [R]; linarith [le_max_left M 0]
  have hF := lipschitzWith_clamp_sq hR0
  have hd : ∀ t ∉ ({-R, R} : Set ℝ),
      HasStrictDerivAt (fun s : ℝ => (max (-R) (min s R)) ^ 2)
        (if |t| < R then 2 * t else 0) t := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    by_cases h : |t| < R
    · rw [if_pos h]
      exact hasStrictDerivAt_clamp_sq h
    · rw [if_neg h]
      have hlt : R < |t| := lt_of_le_of_ne (not_lt.1 h) (fun e => by
        rcases (abs_eq hR0).1 e.symm with h1 | h1
        · exact ht.2 h1
        · exact ht.1 h1)
      exact hasStrictDerivAt_clamp_sq_of_lt_abs hR0 hlt
  have hqF : ⇑(D.toCapacity.toLp q) =ᵐ[m] fun x =>
      (max (-R) (min (D.toCapacity.toLp f x) R)) ^ 2 - (max (-R) (min 0 R)) ^ 2 := by
    filter_upwards [hq, hM] with x h1 h2
    rw [h1, min_eq_left (by linarith [(abs_le.1 h2).2]),
      max_eq_right (by linarith [(abs_le.1 h2).1]),
      min_eq_left hR0, max_eq_right (by linarith), zero_pow (by decide), sub_zero]
  have h := D.gamma_centered_comp hL G hF ((Set.countable_singleton R).insert (-R)) hd f v q hqF
  filter_upwards [h, hM] with x h1 h2
  rw [h1, if_pos (by linarith)]

/--
For a local form, any domain representative of the product of two bounded arguments satisfies
the Gamma Leibniz identity almost everywhere.
Source: BH 1991, Chapter I, Section 6; EBM, Section 4.2.
-/
theorem gamma_bounded_product (hL : D.Local) (G : D.CarreDuChamp)
    (f g p v : D.toCapacity.Space)
    (hf : f ∈ D.toCapacity.bddSpace) (hg : g ∈ D.toCapacity.bddSpace)
    (hp : ⇑(D.toCapacity.toLp p) =ᵐ[m] fun x => D.toCapacity.toLp f x * D.toCapacity.toLp g x) :
    ⇑(G.Γ p v) =ᵐ[m] fun x =>
      D.toCapacity.toLp f x * G.Γ g v x + D.toCapacity.toLp g x * G.Γ f v x := by
  have hs := D.toCapacity.bddSpace.add_mem hf hg
  have hd := D.toCapacity.bddSpace.sub_mem hf hg
  let q₁ := D.toCapacity.mulS (f + g) (f + g)
  let q₂ := D.toCapacity.mulS (f - g) (f - g)
  have hq₁ : ⇑(D.toCapacity.toLp q₁) =ᵐ[m] fun x => (D.toCapacity.toLp (f + g) x) ^ 2 := by
    simpa only [pow_two] using D.toCapacity.coeFn_toLp_mulS hs hs
  have hq₂ : ⇑(D.toCapacity.toLp q₂) =ᵐ[m] fun x => (D.toCapacity.toLp (f - g) x) ^ 2 := by
    simpa only [pow_two] using D.toCapacity.coeFn_toLp_mulS hd hd
  have hpQ : p = (1 / 4 : ℝ) • (q₁ - q₂) := by
    apply D.toCapacity.eq_of_ae
    simp only [map_smul, map_sub]
    filter_upwards [hp, hq₁, hq₂,
      Lp.coeFn_smul (1 / 4 : ℝ) (D.toCapacity.toLp q₁ - D.toCapacity.toLp q₂),
      Lp.coeFn_sub (D.toCapacity.toLp q₁) (D.toCapacity.toLp q₂),
      Lp.coeFn_add (D.toCapacity.toLp f) (D.toCapacity.toLp g),
      Lp.coeFn_sub (D.toCapacity.toLp f) (D.toCapacity.toLp g)] with x a b c d e k l
    simp only [map_add] at b
    simp only [map_sub] at c
    rw [a, d, Pi.smul_apply, smul_eq_mul, e, Pi.sub_apply, b, c, k, l,
      Pi.add_apply, Pi.sub_apply]
    ring
  obtain ⟨C₁, h₁⟩ := hs
  obtain ⟨C₂, h₂⟩ := hd
  have e₁ := D.gamma_bounded_square hL G (f + g) q₁ v h₁ hq₁
  have e₂ := D.gamma_bounded_square hL G (f - g) q₂ v h₂ hq₂
  simp only [map_add, map_sub, add_apply, sub_apply] at e₁ e₂
  rw [hpQ]
  simp only [map_smul, map_sub, smul_apply, sub_apply]
  filter_upwards [e₁, e₂,
    Lp.coeFn_smul (1 / 4 : ℝ) (G.Γ q₁ v - G.Γ q₂ v),
    Lp.coeFn_sub (G.Γ q₁ v) (G.Γ q₂ v),
    Lp.coeFn_add (G.Γ f v) (G.Γ g v), Lp.coeFn_sub (G.Γ f v) (G.Γ g v),
    Lp.coeFn_add (D.toCapacity.toLp f) (D.toCapacity.toLp g),
    Lp.coeFn_sub (D.toCapacity.toLp f) (D.toCapacity.toLp g)] with x a b c d e k l r
  rw [e, Pi.add_apply, l, Pi.add_apply] at a
  rw [k, Pi.sub_apply, r, Pi.sub_apply] at b
  rw [c, Pi.smul_apply, smul_eq_mul, d, Pi.sub_apply, a, b]
  ring

/--
For a local BH form, two bounded domain elements have a domain product satisfying the Gamma
Leibniz identity against every domain element.
Source: BH 1991, I.6.1.3, pp. 36--37; EBM, Section 4.2.
-/
theorem bounded_leibnizRule :
  D.Local → ∀ (G : D.CarreDuChamp) (f g : D.form.dom),
    D.Bounded f → D.Bounded g → ∃ w : D.form.dom,
      (⇑(w : Lp ℝ 2 m) =ᵐ[m] fun x => (f : Lp ℝ 2 m) x * (g : Lp ℝ 2 m) x) ∧
      ∀ v : D.form.dom,
        ⇑(G.Γ (D.form.formToDomain.symm w) (D.form.formToDomain.symm v)) =ᵐ[m]
          fun x => (f : Lp ℝ 2 m) x *
            G.Γ (D.form.formToDomain.symm g) (D.form.formToDomain.symm v) x +
            (g : Lp ℝ 2 m) x * G.Γ (D.form.formToDomain.symm f) (D.form.formToDomain.symm v) x := by
  intro hL G f g hf hg
  obtain ⟨w, hw⟩ := D.bounded_product f g hf hg
  refine ⟨w, hw, fun v => ?_⟩
  apply D.gamma_bounded_product hL G _ _ _ _ _ _ hw
  · exact (D.bounded_iff_toCapacity _).1 hf
  · exact (D.bounded_iff_toCapacity _).1 hg

/--
For a local form, absolute value has a domain representative satisfying the scalar Gamma chain
identity with coefficient 1 on positive values and -1 on nonpositive values.
-/
theorem centered_abs_chainRule (hL : D.Local) (G : D.CarreDuChamp) (f : D.form.dom) :
    ∃ w : D.form.dom,
      (⇑(w : Lp ℝ 2 m) =ᵐ[m] fun x => |(f : Lp ℝ 2 m) x|) ∧
      ∀ g : D.form.dom,
        ⇑(G.Γ (D.form.formToDomain.symm w) (D.form.formToDomain.symm g)) =ᵐ[m]
          fun x => (if 0 < (f : Lp ℝ 2 m) x then 1 else -1) *
            G.Γ (D.form.formToDomain.symm f) (D.form.formToDomain.symm g) x := by
  obtain ⟨w, hw⟩ := D.exists_centered_lipschitz hL G ErrorStructure.lipschitz_abs f
  refine ⟨w, by simpa only [abs_zero, sub_zero] using hw, fun g => ?_⟩
  apply D.gamma_centered_comp hL G (F' := fun t => if 0 < t then 1 else -1)
    ErrorStructure.lipschitz_abs (Set.countable_singleton 0)
    (fun t ht => ?_) (D.form.formToDomain.symm f) (D.form.formToDomain.symm g)
    (D.form.formToDomain.symm w) hw
  rcases lt_or_gt_of_ne (show t ≠ 0 from ht) with h | h
  · rw [if_neg (not_lt.2 h.le)]
    apply (hasStrictDerivAt_id t).neg.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with s hs
    exact (abs_of_neg hs).symm
  · rw [if_pos h]
    apply (hasStrictDerivAt_id t).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with s hs
    exact (abs_of_pos hs).symm

end DprBridge.BH1991.DirichletForm
