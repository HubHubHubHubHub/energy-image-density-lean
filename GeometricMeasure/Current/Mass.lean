import GeometricMeasure.Current.MeasureCurrent
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! Bounded smooth approximation and exact masses on open sets. -/

noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped ENNReal Topology

namespace GeometricMeasure
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private def currentClip (v : F) : F := (max 1 ‖v‖)⁻¹ • v

private theorem currentClip_zero : currentClip (0 : F) = 0 := by
  simp [currentClip]

private theorem continuous_currentClip : Continuous (currentClip : F → F) := by
  apply Continuous.smul _ continuous_id
  exact (continuous_const.max continuous_norm).inv₀
    (fun v => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

private theorem norm_currentClip_le_one (v : F) : ‖currentClip v‖ ≤ 1 := by
  have hpos : 0 < max (1 : ℝ) ‖v‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [currentClip, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
    ← div_eq_inv_mul]
  exact (div_le_one hpos).mpr (le_max_right _ _)

private theorem norm_currentClip_sub_le (v z : F) (hz : ‖z‖ ≤ 1) :
    ‖currentClip v - z‖ ≤ 2 * ‖v - z‖ := by
  have hdiff : ‖currentClip v - v‖ ≤ ‖v - z‖ := by
    by_cases hv : ‖v‖ ≤ 1
    · simp only [currentClip, max_eq_left hv, inv_one, one_smul, sub_self, norm_zero]
      exact norm_nonneg _
    · have hv' : 1 < ‖v‖ := lt_of_not_ge hv
      have hv0 : ‖v‖ ≠ 0 := ne_of_gt (zero_lt_one.trans hv')
      have hinv : ‖v‖⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_one.trans hv')).mpr hv'.le
      have heq : currentClip v - v = (‖v‖⁻¹ - 1) • v := by
        simp [currentClip, max_eq_right hv'.le, sub_smul]
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hinv)]
      have hmul : ‖v‖⁻¹ * ‖v‖ = 1 := inv_mul_cancel₀ hv0
      have htri := norm_sub_norm_le v z
      nlinarith
  calc
    ‖currentClip v - z‖ ≤ ‖currentClip v - v‖ + ‖v - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖v - z‖ := by linarith

private theorem exists_bounded_smooth_currentTest
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    {U : Set (EuclideanSpace ℝ (Fin d))}
    {q : EuclideanSpace ℝ (Fin d) → F} (hq : Continuous q)
    (hc : HasCompactSupport q) (hs : tsupport q ⊆ U)
    (hn : ∀ x, ‖q x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ ω : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞),
      tsupport (ω : EuclideanSpace ℝ (Fin d) → F) ⊆ U ∧
      (∀ x, ‖ω x‖ ≤ 1) ∧ (∫ x, ‖ω x - q x‖ ∂ν) < ε := by
  let δ := ε / (4 * (ν.real univ + 1))
  have hmass : 0 ≤ ν.real univ := ENNReal.toReal_nonneg
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g, hg, hdist, hsupport⟩ := hq.exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ => δ) continuous_const (fun _ => hδ)
  let ω : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞) :=
    ⟨fun x => (1 + δ)⁻¹ • g x, hg.const_smul _, (hc.mono hsupport).smul_left,
      subset_univ _⟩
  have hpos : 0 < 1 + δ := by linarith
  have hnorm : ∀ x, ‖ω x‖ ≤ 1 := by
    intro x
    have hh : ‖g x‖ ≤ 1 + δ := by
      have := norm_le_norm_add_norm_sub' (g x) (q x)
      have hd := hdist x
      rw [dist_eq_norm] at hd
      linarith [hn x]
    change ‖(1 + δ)⁻¹ • g x‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), ← div_eq_inv_mul]
    exact (div_le_one hpos).mpr hh
  have herror : ∀ x, ‖ω x - q x‖ ≤ 2 * δ := by
    intro x
    have heq : ω x - q x = (1 + δ)⁻¹ • (g x - q x) -
        (δ / (1 + δ)) • q x := by
      change (1 + δ)⁻¹ • g x - q x = _
      rw [smul_sub, sub_sub, ← add_smul]
      have he : (1 + δ)⁻¹ + δ / (1 + δ) = 1 := by field_simp
      rw [he, one_smul]
    rw [heq]
    calc
      _ ≤ ‖(1 + δ)⁻¹ • (g x - q x)‖ + ‖(δ / (1 + δ)) • q x‖ := norm_sub_le _ _
      _ = (1 + δ)⁻¹ * ‖g x - q x‖ + (δ / (1 + δ)) * ‖q x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hpos), abs_of_pos (div_pos hδ hpos)]
      _ ≤ (1 + δ)⁻¹ * δ + (δ / (1 + δ)) * 1 := by
        gcongr
        · simpa only [dist_eq_norm] using (hdist x).le
        · exact hn x
      _ ≤ 2 * δ := by
        have hi : (1 + δ)⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr (by linarith)
        rw [div_eq_mul_inv]
        nlinarith
  refine ⟨ω, (tsupport_smul_subset_right _ _).trans
    ((closure_mono hsupport).trans hs), hnorm, ?_⟩
  have hqi := hq.integrable_of_hasCompactSupport hc (μ := ν)
  have hωi := ω.integrable (locallyIntegrableOn_const (1 : ℝ)) (μ := ν)
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ (Fin d), 2 * δ ∂ν :=
      integral_mono (hωi.sub hqi).norm (integrable_const _) herror
    _ = ν.real univ * (2 * δ) := by simp
    _ < ε := by
      dsimp [δ]
      have he : ν.real univ * (2 * (ε / (4 * (ν.real univ + 1)))) =
          (ν.real univ * 2 * ε) / (4 * (ν.real univ + 1)) := by ring
      rw [he]
      apply (div_lt_iff₀ (by positivity : 0 < 4 * (ν.real univ + 1))).mpr
      nlinarith

set_option maxHeartbeats 1000000 in
theorem exists_currentTest_norm_le_one_approx
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    {U K : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : EuclideanSpace ℝ (Fin d) → F}
    (hf : Integrable f ν) (hsupp : Function.support f ⊆ K)
    (hnorm : ∀ᵐ x ∂ν, ‖f x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ ω : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞),
      tsupport (ω : EuclideanSpace ℝ (Fin d) → F) ⊆ U ∧
      (∀ x, ‖ω x‖ ≤ 1) ∧ (∫ x, ‖ω x - f x‖ ∂ν) < ε := by
  obtain ⟨q₀, hc₀, herr₀, hq₀, hi₀⟩ :=
    hf.exists_hasCompactSupport_integral_sub_le (show 0 < ε / 8 by positivity)
  obtain ⟨L, hLc, hLcl, hKL, hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨χ, hχK, hχL, hχc, hχn⟩ := exists_continuous_one_zero_of_isCompact hK
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKL)
  have hχs : tsupport (χ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ L := by
    apply closure_minimal _ hLcl
    intro x hx
    by_contra h
    exact hx (hχL (show x ∈ (interior L)ᶜ from fun hx => h (interior_subset hx)))
  let q₁ := fun x => χ x • q₀ x
  have hq₁ : Continuous q₁ := χ.continuous.smul hq₀
  have hc₁ : HasCompactSupport q₁ := hχc.smul_right
  have hs₁ : tsupport q₁ ⊆ U := (tsupport_smul_subset_left _ _).trans (hχs.trans hLU)
  have hi₁ := hq₁.integrable_of_hasCompactSupport hc₁ (μ := ν)
  have herr₁ : ∫ x, ‖q₁ x - f x‖ ∂ν ≤ ε / 8 := by
    apply le_trans (integral_mono (hi₁.sub hf).norm (hf.sub hi₀).norm _) herr₀
    intro x
    have heq : χ x • f x = f x := by
      by_cases hx : x ∈ K
      · rw [hχK hx, Pi.one_apply, one_smul]
      · have hz : f x = 0 := Function.notMem_support.mp (fun h => hx (hsupp h))
        simp [hz]
    have hχabs : |χ x| ≤ 1 := abs_le.mpr ⟨by linarith [(hχn x).1], (hχn x).2⟩
    calc
      ‖q₁ x - f x‖ = ‖χ x • (q₀ x - f x)‖ := by rw [smul_sub, heq]
      _ ≤ ‖q₀ x - f x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) hχabs
      _ = ‖f x - q₀ x‖ := norm_sub_rev _ _
  let q := fun x => currentClip (q₁ x)
  have hq : Continuous q := continuous_currentClip.comp hq₁
  have hc : HasCompactSupport q := hc₁.comp_left currentClip_zero
  have hs : tsupport q ⊆ U := by
    apply subset_trans (closure_mono ?_) hs₁
    intro x hx hx₁
    exact hx (by simp [q, hx₁, currentClip_zero])
  have hi := hq.integrable_of_hasCompactSupport hc (μ := ν)
  have herr : ∫ x, ‖q x - f x‖ ∂ν ≤ ε / 4 := by
    calc
      _ ≤ ∫ x, 2 * ‖q₁ x - f x‖ ∂ν := by
        apply integral_mono_ae (hi.sub hf).norm ((hi₁.sub hf).norm.const_mul 2)
        filter_upwards [hnorm] with x hx
        exact norm_currentClip_sub_le _ _ hx
      _ = 2 * ∫ x, ‖q₁ x - f x‖ ∂ν := integral_const_mul _ _
      _ ≤ ε / 4 := by linarith
  obtain ⟨ω, hωs, hωn, hωerr⟩ := exists_bounded_smooth_currentTest ν hq hc hs
    (fun x => norm_currentClip_le_one _) (show 0 < ε / 2 by positivity)
  have hωi := ω.integrable (locallyIntegrableOn_const (1 : ℝ)) (μ := ν)
  refine ⟨ω, hωs, hωn, ?_⟩
  calc
    _ ≤ ∫ x, ‖ω x - q x‖ + ‖q x - f x‖ ∂ν :=
      integral_mono (hωi.sub hf).norm ((hωi.sub hi).norm.add (hi.sub hf).norm)
        (fun x => norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ = (∫ x, ‖ω x - q x‖ ∂ν) + ∫ x, ‖q x - f x‖ ∂ν :=
      integral_add (hωi.sub hi).norm (hi.sub hf).norm
    _ < ε := by linarith

set_option maxHeartbeats 1000000 in
theorem testFunctionalMassOn_eq_of_paired_density
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    (T : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin d))) F (⊤ : ℕ∞) →L[ℝ] ℝ)
    (B : F →L[ℝ] G →L[ℝ] ℝ)
    (hB : ∀ v w, ‖B v w‖ ≤ ‖v‖ * ‖w‖)
    {p : EuclideanSpace ℝ (Fin d) → G} (hp : Integrable p ν)
    (hpn : ∀ᵐ x ∂ν, ‖p x‖ = 1)
    {q : EuclideanSpace ℝ (Fin d) → F} (hq : Integrable q ν)
    (hqn : ∀ᵐ x ∂ν, ‖q x‖ ≤ 1) (hpq : ∀ᵐ x ∂ν, B (q x) (p x) = 1)
    (hT : ∀ ω, T ω = ∫ x, B (ω x) (p x) ∂ν)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hupper : testFunctionalMassOn T U ≤ ν U) :
    testFunctionalMassOn T U = ν U := by
  apply le_antisymm hupper
  by_contra h
  have hlt : testFunctionalMassOn T U < ν U := lt_of_not_ge h
  obtain ⟨K, hKU, hK, hKm⟩ := hU.exists_lt_isCompact hlt
  have hKmeas := hK.isClosed.measurableSet
  have htop : testFunctionalMassOn T U ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top ν U) hupper
  have hgap : 0 < ν.real K - (testFunctionalMassOn T U).toReal := by
    exact sub_pos.mpr ((ENNReal.toReal_lt_toReal htop (measure_ne_top ν K)).mpr hKm)
  have hfi : Integrable (K.indicator q) ν := hq.indicator hKmeas
  have hfn : ∀ᵐ x ∂ν, ‖K.indicator q x‖ ≤ 1 := by
    filter_upwards [hqn] with x hx
    by_cases h : x ∈ K <;> simp [h, hx]
  obtain ⟨ω, hωs, hωn, hωerr⟩ := exists_currentTest_norm_le_one_approx
    ν hU hK hKU hfi support_indicator_subset hfn hgap
  have hωi := ω.integrable_bilin B (hp.locallyIntegrable.locallyIntegrableOn _)
  have heq : (fun x => B (K.indicator q x) (p x)) =ᵐ[ν]
      K.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hpq] with x hx
    by_cases h : x ∈ K <;> simp [h, hx]
  have hki : Integrable (fun x => B (K.indicator q x) (p x)) ν :=
    ((integrable_const (1 : ℝ)).indicator hKmeas).congr heq.symm
  have hkval : (∫ x, B (K.indicator q x) (p x) ∂ν) = ν.real K := by
    rw [integral_congr_ae heq, integral_indicator hKmeas]
    simp
  have herr : |T ω - ν.real K| ≤ ∫ x, ‖ω x - K.indicator q x‖ ∂ν := by
    rw [hT, ← hkval, ← integral_sub hωi hki, ← Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_ae (hωi.sub hki).norm
      ((ω.integrable (locallyIntegrableOn_const (1 : ℝ))).sub hfi).norm
    filter_upwards [hpn] with x hx
    simpa only [map_sub, sub_apply, Pi.sub_apply, hx, mul_one] using
      hB (ω x - K.indicator q x) (p x)
  have htest : T ω ≤ (testFunctionalMassOn T U).toReal := by
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp
      (ofReal_apply_le_testFunctionalMassOn T U ω hωs hωn)
  have habs := (abs_sub_comm (T ω) (ν.real K)) ▸ herr
  have hval := le_abs_self (ν.real K - T ω)
  linarith

theorem measureOneCurrent_mass_eq_variation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    testFunctionalMassOn (measureOneCurrent M) U = M.variation U := by
  apply testFunctionalMassOn_eq_of_paired_density M.variation (measureOneCurrent M)
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    (fun v w => v.le_opNorm w) (integrable_polarDensity M) (norm_polarDensity_ae M)
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).integrable_comp_iff.mpr
      (integrable_polarDensity M))
    (q := fun x => InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (polarDensity M x))
    _ _ (measureOneCurrent_apply M) hU (measureOneCurrent_mass_le M U)
  · filter_upwards [norm_polarDensity_ae M] with x hx
    simp [hx]
  · filter_upwards [norm_polarDensity_ae M] with x hx
    simp [InnerProductSpace.toDual_apply_apply, hx]

set_option maxHeartbeats 1000000 in
theorem signedTestCurrent_mass_eq_totalVariation
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    testFunctionalMassOn (signedTestCurrent D) U = D.totalVariation U := by
  classical
  haveI : IsFiniteMeasure D.totalVariation := by
    unfold SignedMeasure.totalVariation
    infer_instance
  obtain ⟨A, hA, hpA, hnA⟩ := D.toJordanDecomposition.mutuallySingular
  let q := fun x : EuclideanSpace ℝ (Fin d) => if x ∈ A then (-1 : ℝ) else 1
  have hqm : Measurable q := Measurable.ite hA measurable_const measurable_const
  have hqn : ∀ x, ‖q x‖ = 1 := by intro x; by_cases hx : x ∈ A <;> simp [q, hx]
  have hqi : Integrable q D.totalVariation :=
    (integrable_const (1 : ℝ)).mono' hqm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => (hqn x).le))
  have hqp : q =ᵐ[D.toJordanDecomposition.posPart] (fun _ => 1) := by
    filter_upwards [compl_mem_ae_iff.mpr hpA] with x hx
    have hxA : x ∉ A := hx
    simp [q, hxA]
  have hqm' : q =ᵐ[D.toJordanDecomposition.negPart] (fun _ => -1) := by
    filter_upwards [mem_ae_iff.mpr hnA] with x hx
    simp [q, hx]
  apply testFunctionalMassOn_eq_of_paired_density D.totalVariation (signedTestCurrent D)
    (ContinuousLinearMap.mul ℝ ℝ) (fun v w => by simp [norm_mul])
    hqi (Filter.Eventually.of_forall hqn) hqi
    (Filter.Eventually.of_forall (fun x => (hqn x).le))
    (p := q) (q := q) _ _ hU (signedTestCurrent_mass_le D U)
  · apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ A <;> simp [q, hx]
  · intro φ
    change signedTestCurrent D φ = ∫ x, φ x * q x ∂D.totalVariation
    have heqp : (fun x => φ x * q x) =ᵐ[D.toJordanDecomposition.posPart] φ := by
      filter_upwards [hqp] with x hx
      simp [hx]
    have heqn : (fun x => φ x * q x) =ᵐ[D.toJordanDecomposition.negPart]
        (fun x => -φ x) := by
      filter_upwards [hqm'] with x hx
      simp [hx]
    have hip : Integrable (fun x => φ x * q x) D.toJordanDecomposition.posPart :=
      (φ.integrable (locallyIntegrableOn_const (1 : ℝ))).congr heqp.symm
    have hin : Integrable (fun x => φ x * q x) D.toJordanDecomposition.negPart :=
      (φ.integrable (locallyIntegrableOn_const (1 : ℝ))).neg.congr heqn.symm
    rw [signedTestCurrent_apply, SignedMeasure.totalVariation,
      integral_add_measure hip hin, integral_congr_ae heqp,
      integral_congr_ae heqn, integral_neg, sub_eq_add_neg]

private theorem measure_eq_of_currentTest_integrals
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ : ScalarCurrentTest d, (∫ x, φ x ∂μ) = ∫ x, φ x ∂ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  apply eq_of_forall_dist_le
  intro ε hε
  let δ := ε / (μ.real univ + ν.real univ + 1)
  have hm : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
  have hn : 0 ≤ ν.real univ := ENNReal.toReal_nonneg
  have hden : 0 < μ.real univ + ν.real univ + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hfc : Continuous (fun x => f x) := f.continuous
  obtain ⟨g, hg, hdist, hsupport⟩ := hfc.exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ => δ) continuous_const (fun _ => hδ)
  let φ : ScalarCurrentTest d := ⟨g, hg, f.hasCompactSupport.mono hsupport, subset_univ _⟩
  have hbound : ∀ x, ‖f x - φ x‖ ≤ δ := by
    intro x
    change ‖f x - g x‖ ≤ δ
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using (hdist x).le
  have hμ : |(∫ x, f x ∂μ) - ∫ x, φ x ∂μ| ≤ δ * μ.real univ := by
    rw [← integral_sub (hfc.integrable_of_hasCompactSupport f.hasCompactSupport)
      (φ.integrable (locallyIntegrableOn_const (1 : ℝ))), ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound)
  have hν : |(∫ x, f x ∂ν) - ∫ x, φ x ∂ν| ≤ δ * ν.real univ := by
    rw [← integral_sub (hfc.integrable_of_hasCompactSupport f.hasCompactSupport)
      (φ.integrable (locallyIntegrableOn_const (1 : ℝ))), ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound)
  have heq := h φ
  have hsum : δ * μ.real univ + δ * ν.real univ ≤ ε := by
    dsimp [δ]
    rw [← mul_add, div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  rw [Real.dist_eq]
  calc
    _ ≤ |(∫ x, f x ∂μ) - ∫ x, φ x ∂μ| +
        |(∫ x, f x ∂ν) - ∫ x, φ x ∂ν| := by
      rw [heq]
      simpa only [abs_sub_comm] using
        (abs_sub_le (∫ x, f x ∂μ) (∫ x, φ x ∂ν) (∫ x, f x ∂ν))
    _ ≤ ε := (add_le_add hμ hν).trans hsum

theorem signedTestCurrent_injective : Function.Injective (signedTestCurrent (d := d)) := by
  intro D₁ D₂ h
  have heq : D₁.toJordanDecomposition.posPart + D₂.toJordanDecomposition.negPart =
      D₂.toJordanDecomposition.posPart + D₁.toJordanDecomposition.negPart := by
    apply measure_eq_of_currentTest_integrals
    intro φ
    have hh := congrArg (fun T : ScalarCurrentTest d →L[ℝ] ℝ => T φ) h
    simp only [signedTestCurrent_apply] at hh
    rw [integral_add_measure (φ.integrable (locallyIntegrableOn_const (1 : ℝ)))
        (φ.integrable (locallyIntegrableOn_const (1 : ℝ))),
      integral_add_measure (φ.integrable (locallyIntegrableOn_const (1 : ℝ)))
        (φ.integrable (locallyIntegrableOn_const (1 : ℝ)))]
    linarith
  have hs := Measure.toSignedMeasure_congr heq
  simp only [Measure.toSignedMeasure_add] at hs
  have hd₁ := D₁.toSignedMeasure_toJordanDecomposition
  have hd₂ := D₂.toSignedMeasure_toJordanDecomposition
  rw [JordanDecomposition.toSignedMeasure] at hd₁ hd₂
  rw [← hd₁, ← hd₂]
  exact sub_eq_sub_iff_add_eq_add.mpr hs

theorem measureDivergence_unique
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    {D₁ D₂ : SignedMeasure (EuclideanSpace ℝ (Fin d))}
    (h₁ : HasMeasureDivergence M D₁) (h₂ : HasMeasureDivergence M D₂) : D₁ = D₂ := by
  apply signedTestCurrent_injective
  ext φ
  exact (h₁ φ).trans (h₂ φ).symm

theorem boundary_measureOneCurrent_mass_eq
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (hD : HasMeasureDivergence M D)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    testFunctionalMassOn (oneCurrentBoundary (measureOneCurrent M)) U = D.totalVariation U := by
  rw [boundary_measureOneCurrent_eq_neg M D hD, ← signedTestCurrent_neg,
    signedTestCurrent_mass_eq_totalVariation (-D) hU, SignedMeasure.totalVariation_neg]

theorem hasMeasureDivergence_zero_measure_iff
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) :
    HasMeasureDivergence (0 : VectorMeasure (EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d))) D ↔ D = 0 := by
  have hz : HasMeasureDivergence (0 : VectorMeasure (EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d))) 0 := by
    intro φ
    simp [signedTestCurrent_zero, measureOneCurrent_zero, oneCurrentBoundary]
  exact ⟨fun h => measureDivergence_unique 0 h hz, fun h => h ▸ hz⟩

theorem hasMeasureDivergence_dimension_zero_iff
    (M : VectorMeasure (EuclideanSpace ℝ (Fin 0)) (EuclideanSpace ℝ (Fin 0)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin 0))) : HasMeasureDivergence M D ↔ D = 0 := by
  rw [eq_zero_of_dimension_zero M, hasMeasureDivergence_zero_measure_iff]

end GeometricMeasure
