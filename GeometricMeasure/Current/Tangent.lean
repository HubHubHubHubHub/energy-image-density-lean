import GeometricMeasure.Current.LocalizedDilation
import GeometricMeasure.VectorMeasure.SingularDifferentiation
import GeometricMeasure.VectorMeasure.GoodRadii

/-!
# Nonzero divergence-free tangents

## Main results
De Philippis–Rindler approach (2016, § 2), with point (ii) replaced, for the singular part `|M|ˢ =
M.variation.singularPart volume`, by a vector lower bound: the weak limit `N` of dilations
normalized by singular mass satisfies `2⁻ᵈ ≤ ⟨N, χ · ⟨p(x₀), ·⟩⟩`, is divergence-free in `ball 0 1`,
and (concrete cutoff `tentCutoff`, zero outside `ball 0 1`) satisfies `0 < N.variation (ball 0 1)`.

Nonvanishing concerns the open unit ball `ball 0 1`, rather than `B_{1/2}` as in DPR (2.2): DPR
point (ii) on `B_{1/2}` is **not** claimed here.

Contents:
* § 2: `polarTestField`, `vectorMeasurePairing_localizedDilation`;
* § 3: one-radius lower bound `pairing_massNormalizedDilation_ge`,
`inv_two_pow_le_measureReal_ratio`;
* § 4: `exists_tangent_divergenceFreeOn_pairing_ge` (pointwise) and its almost-everywhere version;
* § 5: nonvanishing, `tentCutoff`, `ae_exists_nonzero_divergenceFree_tangent`;
* O1: `exists_tangent_pairing_ge`, `ae_exists_tangent_pairing_ge` (arbitrary codomain).
-/

noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d m : ℕ}

/-! ### § 2. Polar test field and pairing of a localized dilation -/

/-- The test field `y ↦ χ y • ⟨v, ·⟩`. -/
def polarTestField (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) : BoundedCovectorField d m :=
  (ContinuousLinearMap.toSpanSingleton ℝ (innerSL ℝ v)).compLeftContinuousBounded _ χ

theorem polarTestField_apply (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin m)) :
    polarTestField χ v y w = χ y * inner ℝ v w := by
  simp [polarTestField, ContinuousLinearMap.compLeftContinuousBounded]

/-- Pairing of a localized dilation: integral over the source ball against `|M|`. -/
theorem vectorMeasurePairing_localizedDilation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ)
    (ω : BoundedCovectorField d m) :
    vectorMeasurePairing (localizedDilation M x₀ r hr c) ω =
      c * ∫ y in closedBall x₀ |r|,
        ω (dilationEquiv x₀ r hr y) (polarDensity M y) ∂M.variation := by
  rw [localizedDilation, vectorMeasurePairing_smul]
  congr 1
  unfold vectorMeasurePairing
  rw [(dilationEquiv x₀ r hr).measurableEmbedding.variation_map]
  calc
    _ = ∫ y, ω y (polarDensity (M.restrict (closedBall x₀ |r|))
          ((dilationEquiv x₀ r hr).symm y))
        ∂((M.restrict (closedBall x₀ |r|)).variation.map (dilationEquiv x₀ r hr)) :=
      integral_congr_ae ((polarDensity_map_equiv _ _).mono (fun y hy => congrArg (ω y) hy))
    _ = ∫ y, ω (dilationEquiv x₀ r hr y) (polarDensity (M.restrict (closedBall x₀ |r|)) y)
        ∂(M.restrict (closedBall x₀ |r|)).variation := by
      rw [integral_map_equiv]
      simp only [MeasurableEquiv.symm_apply_apply]
    _ = _ := by
      rw [VectorMeasure.variation_restrict measurableSet_closedBall]
      exact integral_congr_ae ((polarDensity_restrict M measurableSet_closedBall).mono
        (fun y hy => congrArg (ω (dilationEquiv x₀ r hr y)) hy))

/-! ### § 3. One-radius lower bound -/

theorem inner_polar_ge_one_sub {v w : EuclideanSpace ℝ (Fin m)} (hv : ‖v‖ = 1) :
    1 - ‖w - v‖ ≤ inner ℝ v w := by
  have h1 : inner ℝ v w = inner ℝ v v + inner ℝ v (w - v) := by
    rw [inner_sub_right]; ring
  have h2 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have h3 : |inner ℝ v (w - v)| ≤ ‖w - v‖ := by
    simpa [hv] using abs_real_inner_le_norm v (w - v)
  have h4 := neg_le_of_abs_le h3
  linarith

theorem indicator_closedBall_half_le_cutoff
    (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) (hχ0 : ∀ y, 0 ≤ χ y)
    (hχB : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2), χ y = 1)
    (x₀ : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) (y : EuclideanSpace ℝ (Fin d)) :
    (closedBall x₀ (r / 2)).indicator 1 y ≤ χ (dilationEquiv x₀ r hr.ne' y) := by
  by_cases hy : y ∈ closedBall x₀ (r / 2)
  · rw [indicator_of_mem hy, Pi.one_apply]
    have hmem : dilationEquiv x₀ r hr.ne' y ∈
        closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2) := by
      rw [← mem_preimage, preimage_closedBall_dilation, abs_of_pos hr]
      convert hy using 2
      ring
    rw [hχB _ hmem]
  · rw [indicator_of_notMem hy]
    exact hχ0 _

/-- **One-radius lower bound.** Neither `0 < ν (B̄_r)` nor finiteness of `ν` is assumed. -/
theorem pairing_massNormalizedDilation_ge
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (hν : ν ≤ M.variation)
    (x₀ : EuclideanSpace ℝ (Fin d)) (hx : ‖polarDensity M x₀‖ = 1) {r : ℝ} (hr : 0 < r)
    (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) (hχ0 : ∀ y, 0 ≤ χ y)
    (hχ1 : ∀ y, χ y ≤ 1)
    (hχB : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2), χ y = 1) :
    ν.real (closedBall x₀ (r / 2)) / ν.real (closedBall x₀ r) -
        (∫ y in closedBall x₀ r, ‖polarDensity M y - polarDensity M x₀‖ ∂M.variation) /
          ν.real (closedBall x₀ r) ≤
      vectorMeasurePairing (massNormalizedDilation M ν x₀ r hr.ne')
        (polarTestField χ (polarDensity M x₀)) := by
  set v := polarDensity M x₀ with hvdef
  set B := closedBall x₀ r with hB
  set S := dilationEquiv x₀ r hr.ne' with hS
  rw [massNormalizedDilation, vectorMeasurePairing_localizedDilation, abs_of_pos hr]
  simp only [polarTestField_apply]
  have hc : 0 ≤ (ν.real B)⁻¹ := inv_nonneg.mpr measureReal_nonneg
  rw [div_sub_div_same, div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_left _ hc
  have hiF : Integrable (fun y => χ (S y) * inner ℝ v (polarDensity M y))
      (M.variation.restrict B) := by
    have h := integrable_boundedCovector_apply M.variation (integrable_polarDensity M)
      ((polarTestField χ v).compContinuous ⟨S, (dilationHomeomorph x₀ r hr.ne').continuous⟩)
    refine (h.congr (Eventually.of_forall (fun y => ?_))).restrict
    simp [BoundedContinuousFunction.compContinuous_apply, polarTestField_apply]
  have hiE : Integrable (fun y => ‖polarDensity M y - v‖) (M.variation.restrict B) :=
    ((integrable_polarDensity M).sub (integrable_const v)).norm.restrict
  have hiI : Integrable ((closedBall x₀ (r / 2)).indicator (1 : EuclideanSpace ℝ (Fin d) → ℝ))
      (M.variation.restrict B) :=
    (integrable_const (1 : ℝ)).indicator measurableSet_closedBall
  have hν2 : ν.real (closedBall x₀ (r / 2)) ≤ M.variation.real (closedBall x₀ (r / 2)) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (hν _)
  have hI : ∫ y in B, (closedBall x₀ (r / 2)).indicator 1 y ∂M.variation =
      M.variation.real (closedBall x₀ (r / 2)) := by
    rw [integral_indicator_one measurableSet_closedBall,
      measureReal_restrict_apply measurableSet_closedBall,
      inter_eq_left.mpr (closedBall_subset_closedBall (by linarith))]
  calc
    ν.real (closedBall x₀ (r / 2)) - ∫ y in B, ‖polarDensity M y - v‖ ∂M.variation
        ≤ M.variation.real (closedBall x₀ (r / 2)) -
          ∫ y in B, ‖polarDensity M y - v‖ ∂M.variation := by linarith
    _ = ∫ y in B, ((closedBall x₀ (r / 2)).indicator 1 y - ‖polarDensity M y - v‖)
          ∂M.variation := by rw [integral_sub hiI hiE, hI]
    _ ≤ ∫ y in B, χ (S y) * inner ℝ v (polarDensity M y) ∂M.variation := by
      apply integral_mono (hiI.sub hiE) hiF
      intro y
      have hI1 := indicator_closedBall_half_le_cutoff χ hχ0 hχB x₀ hr y
      have hin := inner_polar_ge_one_sub (w := polarDensity M y) hx
      have he : 0 ≤ ‖polarDensity M y - v‖ := norm_nonneg _
      have h0 := hχ0 (S y)
      have h1 := hχ1 (S y)
      simp only [Pi.sub_apply]
      nlinarith [mul_le_mul_of_nonneg_left hin h0, mul_le_mul_of_nonneg_right h1 he]

theorem inv_two_pow_le_measureReal_ratio
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    (x₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hpos : 0 < ν (closedBall x₀ r))
    (h : ν (closedBall x₀ r) ≤ 2 ^ d * ν (closedBall x₀ (r / 2))) :
    ((2 : ℝ) ^ d)⁻¹ ≤ ν.real (closedBall x₀ (r / 2)) / ν.real (closedBall x₀ r) := by
  have hp : 0 < ν.real (closedBall x₀ r) := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hR : ν.real (closedBall x₀ r) ≤ 2 ^ d * ν.real (closedBall x₀ (r / 2)) := by
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) h
    simpa [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow] using h'
  rw [le_div_iff₀ hp, inv_mul_le_iff₀ (by positivity)]
  exact hR

/-! ### § 4. Tangent at a point, then almost everywhere (m = d) -/

theorem ofReal_abs_inv_toReal_mul_le {S Dm K : ℝ≥0∞} {r : ℝ} (hr : 0 < r)
    (hS0 : S ≠ 0) (hSt : S ≠ ⊤) (hD : Dm ≤ K * S) :
    ENNReal.ofReal |(S.toReal)⁻¹ * r| * Dm ≤ ENNReal.ofReal r * K := by
  have hSpos : 0 < S.toReal := ENNReal.toReal_pos hS0 hSt
  rw [abs_of_pos (mul_pos (inv_pos.mpr hSpos) hr), ENNReal.ofReal_mul (inv_nonneg.mpr hSpos.le),
    ENNReal.ofReal_inv_of_pos hSpos, ENNReal.ofReal_toReal hSt]
  calc
    S⁻¹ * ENNReal.ofReal r * Dm ≤ S⁻¹ * ENNReal.ofReal r * (K * S) := by gcongr
    _ = ENNReal.ofReal r * K * (S⁻¹ * S) := by ring
    _ = ENNReal.ofReal r * K := by rw [ENNReal.inv_mul_cancel hS0 hSt, mul_one]

/--
**Pointwise tangent**: under the measure-differentiation assumptions at `x₀` and frequently good
radii for `ν ≤ |M|`, a subsequence of dilations normalized by `ν` converges weakly to `N`,
carried by `B̄(0,1)`, of mass `≤ 2`, divergence-free in `ball 0 1`, with `2⁻ᵈ ≤ ⟨N, χ ⟨p(x₀), ·⟩⟩`.
-/
theorem exists_tangent_divergenceFreeOn_pairing_ge
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (hdiv : HasMeasureDivergence M D)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (hν : ν ≤ M.variation)
    (x₀ : EuclideanSpace ℝ (Fin d)) (hx : ‖polarDensity M x₀‖ = 1)
    (hgood : ∃ᶠ r in 𝓝[>] (0 : ℝ),
      ν (closedBall x₀ r) ≤ 2 ^ d * ν (closedBall x₀ (r / 2)))
    (hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ν (closedBall x₀ r))
    (hratio : Tendsto (fun r => M.variation (closedBall x₀ r) / ν (closedBall x₀ r))
      (𝓝[>] (0 : ℝ)) (𝓝 1))
    (herr : Tendsto (fun r => (∫ y in closedBall x₀ r,
        ‖polarDensity M y - polarDensity M x₀‖ ∂M.variation) / ν.real (closedBall x₀ r))
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    {b : ℝ≥0∞} (hb : b ≠ ⊤)
    (hD : Tendsto (fun r => D.totalVariation (closedBall x₀ r) / ν (closedBall x₀ r))
      (𝓝[>] (0 : ℝ)) (𝓝 b))
    (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) (hχ0 : ∀ y, 0 ≤ χ y)
    (hχ1 : ∀ y, χ y ≤ 1)
    (hχB : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2), χ y = 1) :
    ∃ rs : ℕ → ℝ, ∃ hrs : ∀ n, 0 < rs n, Tendsto rs atTop (𝓝[>] (0 : ℝ)) ∧
      ∃ N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)),
        N.variation (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 ∧
        N.variation univ ≤ 2 ∧
        VectorMeasureWeaklyTendsto
          (fun n => massNormalizedDilation M ν x₀ (rs n) (hrs n).ne') N ∧
        HasMeasureDivergenceOn N 0 (ball 0 1) ∧
        ((2 : ℝ) ^ d)⁻¹ ≤ vectorMeasurePairing N (polarTestField χ (polarDensity M x₀)) := by
  haveI : IsFiniteMeasure ν := isFiniteMeasure_of_le _ hν
  set K : ℝ≥0∞ := b + 1 with hKdef
  have hK : K ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hb, ENNReal.one_ne_top⟩
  have hlt2 := hratio.eventually_lt_const (by norm_num : (1 : ℝ≥0∞) < 2)
  have hltK := hD.eventually_lt_const (ENNReal.lt_add_right hb one_ne_zero)
  have hfreq := hgood.and_eventually
    ((eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)).and (hpos.and (hlt2.and hltK)))
  obtain ⟨rs, hrs_t, hP⟩ := exists_seq_forall_of_frequently hfreq
  have hrs0 : ∀ n, 0 < rs n := fun n => (hP n).2.1
  have hrsne : ∀ n, rs n ≠ 0 := fun n => (hrs0 n).ne'
  have habs : ∀ n, |rs n| = rs n := fun n => abs_of_pos (hrs0 n)
  set cs : ℕ → ℝ := fun n => (ν.real (closedBall x₀ |rs n|))⁻¹ with hcs
  have hmass : ∀ n, ENNReal.ofReal |cs n| * M.variation (closedBall x₀ |rs n|) ≤
      ((2 : ℝ≥0) : ℝ≥0∞) := by
    intro n
    rw [← variation_localizedDilation_univ M x₀ (rs n) (hrsne n) (cs n)]
    change (massNormalizedDilation M ν x₀ (rs n) (hrsne n)).variation univ ≤ _
    rw [variation_massNormalizedDilation_univ M ν x₀ (rs n) (hrsne n)
      (by rw [habs n]; exact (hP n).2.2.1), habs n]
    exact_mod_cast (hP n).2.2.2.1.le
  have hrs_t0 : Tendsto rs atTop (𝓝 0) := (tendsto_nhdsWithin_iff.mp hrs_t).1
  have hsmall : Tendsto (fun n => ENNReal.ofReal |cs n * rs n| *
      D.totalVariation (closedBall x₀ |rs n|)) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n => ENNReal.ofReal (rs n) * K) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hrs_t0) (Or.inr hK)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => zero_le) (fun n => ?_)
    have hS0 : ν (closedBall x₀ (rs n)) ≠ 0 := (hP n).2.2.1.ne'
    have hSt : ν (closedBall x₀ (rs n)) ≠ ⊤ := measure_ne_top _ _
    have hDle : D.totalVariation (closedBall x₀ (rs n)) ≤ K * ν (closedBall x₀ (rs n)) :=
      ((ENNReal.div_lt_iff (Or.inl hS0) (Or.inl hSt)).mp (hP n).2.2.2.2).le
    simp only [hcs, habs n, measureReal_def]
    exact ofReal_abs_inv_toReal_mul_le (hrs0 n) hS0 hSt hDle
  obtain ⟨φ, hφ, N, hsupp, hmassN, hconv, hdivN⟩ :=
    exists_localizedDilation_weak_subseq_divergenceFreeOn M D hdiv x₀ rs cs hrsne 2 hmass hsmall
  have hsub : Tendsto (rs ∘ φ) atTop (𝓝[>] (0 : ℝ)) := hrs_t.comp hφ.tendsto_atTop
  refine ⟨rs ∘ φ, fun n => hrs0 (φ n), hsub, N, hsupp, by exact_mod_cast hmassN, hconv, hdivN, ?_⟩
  have hlow : ∀ n, ((2 : ℝ) ^ d)⁻¹ - (∫ y in closedBall x₀ (rs (φ n)),
        ‖polarDensity M y - polarDensity M x₀‖ ∂M.variation) /
          ν.real (closedBall x₀ (rs (φ n))) ≤
      vectorMeasurePairing (massNormalizedDilation M ν x₀ (rs (φ n)) (hrsne (φ n)))
        (polarTestField χ (polarDensity M x₀)) := by
    intro n
    have h1 := pairing_massNormalizedDilation_ge M ν hν x₀ hx (hrs0 (φ n)) χ hχ0 hχ1 hχB
    have h2 := inv_two_pow_le_measureReal_ratio ν x₀ (rs (φ n)) (hP (φ n)).2.2.1 (hP (φ n)).1
    linarith
  have he := herr.comp hsub
  have hconst : Tendsto (fun n => ((2 : ℝ) ^ d)⁻¹ - (∫ y in closedBall x₀ (rs (φ n)),
        ‖polarDensity M y - polarDensity M x₀‖ ∂M.variation) /
          ν.real (closedBall x₀ (rs (φ n)))) atTop (𝓝 (((2 : ℝ) ^ d)⁻¹ - 0)) :=
    tendsto_const_nhds.sub he
  rw [sub_zero] at hconst
  exact le_of_tendsto_of_tendsto' hconst (hconv _) hlow

/-- **Almost-everywhere tangent** for the singular part `|M|ˢ` of `|M|`. -/
theorem ae_exists_tangent_divergenceFreeOn_pairing_ge
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (hdiv : HasMeasureDivergence M D)
    (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) (hχ0 : ∀ y, 0 ≤ χ y)
    (hχ1 : ∀ y, χ y ≤ 1)
    (hχB : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2), χ y = 1) :
    ∀ᵐ x₀ ∂M.variation.singularPart volume,
      ∃ rs : ℕ → ℝ, ∃ hrs : ∀ n, 0 < rs n, Tendsto rs atTop (𝓝[>] (0 : ℝ)) ∧
      ∃ N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)),
        N.variation (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 ∧
        N.variation univ ≤ 2 ∧
        VectorMeasureWeaklyTendsto (fun n =>
          massNormalizedDilation M (M.variation.singularPart volume) x₀ (rs n) (hrs n).ne') N ∧
        HasMeasureDivergenceOn N 0 (ball 0 1) ∧
        ((2 : ℝ) ^ d)⁻¹ ≤ vectorMeasurePairing N (polarTestField χ (polarDensity M x₀)) := by
  haveI : IsFiniteMeasure D.totalVariation := by
    unfold SignedMeasure.totalVariation
    infer_instance
  filter_upwards [ae_frequently_closedBall_le_two_pow_mul_half (M.variation.singularPart volume)
      (M.variation.mutuallySingular_singularPart volume),
    ae_mem_singularBesicovitchPoints M volume (fun _ : Unit => D.totalVariation),
    ae_tendsto_polar_singular_closedBall_error M volume] with x hgood hx herr
  obtain ⟨hp, hpos, -, hratio, -, -, -, hβ⟩ := hx
  exact exists_tangent_divergenceFreeOn_pairing_ge M D hdiv _
    (M.variation.singularPart_le volume) x hp hgood hpos hratio herr (hβ ()).1.ne (hβ ()).2.1
    χ hχ0 hχ1 hχB

/-! ### § 5. Nonvanishing in the open ball, concrete cutoff -/

theorem vectorMeasurePairing_eq_zero_of_variation_eq_zero
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ω : BoundedCovectorField d m) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : N.variation U = 0) (hω : ∀ y ∉ U, ω y = 0) :
    vectorMeasurePairing N ω = 0 := by
  unfold vectorMeasurePairing
  apply integral_eq_zero_of_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hU] with y hy
  simp [hω y hy]

theorem variation_pos_of_pairing_pos
    (N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ω : BoundedCovectorField d m) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hω : ∀ y ∉ U, ω y = 0) (hpos : 0 < vectorMeasurePairing N ω) :
    0 < N.variation U := by
  apply pos_iff_ne_zero.mpr
  intro hU
  rw [vectorMeasurePairing_eq_zero_of_variation_eq_zero N ω hU hω] at hpos
  exact lt_irrefl _ hpos

theorem polarTestField_eq_zero
    (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) {y : EuclideanSpace ℝ (Fin d)} (hy : χ y = 0) :
    polarTestField χ v y = 0 := by
  ext w
  simp [polarTestField_apply, hy]

/-- Tent cutoff: `1` on `B̄(0,1/2)`, `0` outside `ball 0 1` (support `B̄(0,3/4)`). -/
def tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => max 0 (min 1 (3 - 4 * ‖y‖)))
    (continuous_const.max (continuous_const.min
      (continuous_const.sub (continuous_const.mul continuous_norm)))) 1
    (fun y => by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [le_max_left (0 : ℝ) (min 1 (3 - 4 * ‖y‖))]
      · exact max_le (by norm_num) (min_le_left _ _))

theorem tentCutoff_apply (y : EuclideanSpace ℝ (Fin d)) :
    (tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) y =
      max 0 (min 1 (3 - 4 * ‖y‖)) := rfl

theorem tentCutoff_nonneg (y : EuclideanSpace ℝ (Fin d)) :
    0 ≤ (tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) y := by
  rw [tentCutoff_apply]; exact le_max_left _ _

theorem tentCutoff_le_one (y : EuclideanSpace ℝ (Fin d)) :
    (tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) y ≤ 1 := by
  rw [tentCutoff_apply]; exact max_le (by norm_num) (min_le_left _ _)

theorem tentCutoff_eq_one {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) :
    (tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) y = 1 := by
  rw [mem_closedBall, dist_zero_right] at hy
  rw [tentCutoff_apply, min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem tentCutoff_eq_zero {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∉ ball (0 : EuclideanSpace ℝ (Fin d)) 1) :
    (tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) y = 0 := by
  rw [mem_ball, dist_zero_right, not_lt] at hy
  rw [tentCutoff_apply, min_eq_right (by linarith), max_eq_left (by linarith)]

/--
**Nonzero divergence-free tangent**, `|M|ˢ`-almost everywhere: the limit `N` is
divergence-free in `ball 0 1` and `0 < N.variation (ball 0 1)` (open unit ball; DPR point (ii) on
`B_{1/2}`
is not claimed).
-/
theorem ae_exists_nonzero_divergenceFree_tangent
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (D : SignedMeasure (EuclideanSpace ℝ (Fin d))) (hdiv : HasMeasureDivergence M D) :
    ∀ᵐ x₀ ∂M.variation.singularPart volume,
      ∃ rs : ℕ → ℝ, ∃ hrs : ∀ n, 0 < rs n, Tendsto rs atTop (𝓝[>] (0 : ℝ)) ∧
      ∃ N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)),
        N.variation (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 ∧
        N.variation univ ≤ 2 ∧
        VectorMeasureWeaklyTendsto (fun n =>
          massNormalizedDilation M (M.variation.singularPart volume) x₀ (rs n) (hrs n).ne') N ∧
        HasMeasureDivergenceOn N 0 (ball 0 1) ∧
        ((2 : ℝ) ^ d)⁻¹ ≤ vectorMeasurePairing N (polarTestField tentCutoff (polarDensity M x₀)) ∧
        0 < N.variation (ball 0 1) := by
  filter_upwards [ae_exists_tangent_divergenceFreeOn_pairing_ge M D hdiv tentCutoff
    tentCutoff_nonneg tentCutoff_le_one (fun y hy => tentCutoff_eq_one hy)] with x hx
  obtain ⟨rs, hrs, ht, N, h1, h2, h3, h4, h5⟩ := hx
  refine ⟨rs, hrs, ht, N, h1, h2, h3, h4, h5, ?_⟩
  exact variation_pos_of_pairing_pos N _
    (fun y hy => polarTestField_eq_zero _ _ (tentCutoff_eq_zero hy))
    (lt_of_lt_of_le (by positivity) h5)

/-! ### Option O1. Arbitrary codomain, without divergence -/

theorem exists_tangent_pairing_ge
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (hν : ν ≤ M.variation)
    (x₀ : EuclideanSpace ℝ (Fin d)) (hx : ‖polarDensity M x₀‖ = 1)
    (hgood : ∃ᶠ r in 𝓝[>] (0 : ℝ),
      ν (closedBall x₀ r) ≤ 2 ^ d * ν (closedBall x₀ (r / 2)))
    (hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ν (closedBall x₀ r))
    (hratio : Tendsto (fun r => M.variation (closedBall x₀ r) / ν (closedBall x₀ r))
      (𝓝[>] (0 : ℝ)) (𝓝 1))
    (herr : Tendsto (fun r => (∫ y in closedBall x₀ r,
        ‖polarDensity M y - polarDensity M x₀‖ ∂M.variation) / ν.real (closedBall x₀ r))
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) (hχ0 : ∀ y, 0 ≤ χ y)
    (hχ1 : ∀ y, χ y ≤ 1)
    (hχB : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2), χ y = 1) :
    ∃ rs : ℕ → ℝ, ∃ hrs : ∀ n, 0 < rs n, Tendsto rs atTop (𝓝[>] (0 : ℝ)) ∧
      ∃ N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)),
        N.variation (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 ∧
        N.variation univ ≤ 2 ∧
        VectorMeasureWeaklyTendsto
          (fun n => massNormalizedDilation M ν x₀ (rs n) (hrs n).ne') N ∧
        ((2 : ℝ) ^ d)⁻¹ ≤ vectorMeasurePairing N (polarTestField χ (polarDensity M x₀)) := by
  haveI : IsFiniteMeasure ν := isFiniteMeasure_of_le _ hν
  have hlt2 := hratio.eventually_lt_const (by norm_num : (1 : ℝ≥0∞) < 2)
  have hfreq := hgood.and_eventually
    ((eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)).and (hpos.and hlt2))
  obtain ⟨rs, hrs_t, hP⟩ := exists_seq_forall_of_frequently hfreq
  have hrs0 : ∀ n, 0 < rs n := fun n => (hP n).2.1
  have hrsne : ∀ n, rs n ≠ 0 := fun n => (hrs0 n).ne'
  have habs : ∀ n, |rs n| = rs n := fun n => abs_of_pos (hrs0 n)
  set cs : ℕ → ℝ := fun n => (ν.real (closedBall x₀ |rs n|))⁻¹ with hcs
  have hmass : ∀ n, ENNReal.ofReal |cs n| * M.variation (closedBall x₀ |rs n|) ≤
      ((2 : ℝ≥0) : ℝ≥0∞) := by
    intro n
    rw [← variation_localizedDilation_univ M x₀ (rs n) (hrsne n) (cs n)]
    change (massNormalizedDilation M ν x₀ (rs n) (hrsne n)).variation univ ≤ _
    rw [variation_massNormalizedDilation_univ M ν x₀ (rs n) (hrsne n)
      (by rw [habs n]; exact (hP n).2.2.1), habs n]
    exact_mod_cast (hP n).2.2.2.le
  obtain ⟨φ, hφ, N, hsupp, hmassN, hconv⟩ :=
    exists_localizedDilation_weak_subseq M x₀ rs cs hrsne 2 hmass
  have hsub : Tendsto (rs ∘ φ) atTop (𝓝[>] (0 : ℝ)) := hrs_t.comp hφ.tendsto_atTop
  refine ⟨rs ∘ φ, fun n => hrs0 (φ n), hsub, N, hsupp, by exact_mod_cast hmassN, hconv, ?_⟩
  have hlow : ∀ n, ((2 : ℝ) ^ d)⁻¹ - (∫ y in closedBall x₀ (rs (φ n)),
        ‖polarDensity M y - polarDensity M x₀‖ ∂M.variation) /
          ν.real (closedBall x₀ (rs (φ n))) ≤
      vectorMeasurePairing (massNormalizedDilation M ν x₀ (rs (φ n)) (hrsne (φ n)))
        (polarTestField χ (polarDensity M x₀)) := by
    intro n
    have h1 := pairing_massNormalizedDilation_ge M ν hν x₀ hx (hrs0 (φ n)) χ hχ0 hχ1 hχB
    have h2 := inv_two_pow_le_measureReal_ratio ν x₀ (rs (φ n)) (hP (φ n)).2.2.1 (hP (φ n)).1
    linarith
  have hconst := (tendsto_const_nhds (x := ((2 : ℝ) ^ d)⁻¹)).sub (herr.comp hsub)
  rw [sub_zero] at hconst
  exact le_of_tendsto_of_tendsto' hconst (hconv _) hlow

theorem ae_exists_tangent_pairing_ge
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (χ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) (hχ0 : ∀ y, 0 ≤ χ y)
    (hχ1 : ∀ y, χ y ≤ 1)
    (hχB : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2), χ y = 1) :
    ∀ᵐ x₀ ∂M.variation.singularPart volume,
      ∃ rs : ℕ → ℝ, ∃ hrs : ∀ n, 0 < rs n, Tendsto rs atTop (𝓝[>] (0 : ℝ)) ∧
      ∃ N : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)),
        N.variation (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 ∧
        N.variation univ ≤ 2 ∧
        VectorMeasureWeaklyTendsto (fun n =>
          massNormalizedDilation M (M.variation.singularPart volume) x₀ (rs n) (hrs n).ne') N ∧
        ((2 : ℝ) ^ d)⁻¹ ≤ vectorMeasurePairing N (polarTestField χ (polarDensity M x₀)) := by
  filter_upwards [ae_frequently_closedBall_le_two_pow_mul_half (M.variation.singularPart volume)
      (M.variation.mutuallySingular_singularPart volume),
    ae_mem_singularBesicovitchPoints M volume (fun _ : Unit => M.variation),
    ae_tendsto_polar_singular_closedBall_error M volume] with x hgood hx herr
  obtain ⟨hp, hpos, -, hratio, -⟩ := hx
  exact exists_tangent_pairing_ge M _ (M.variation.singularPart_le volume) x hp hgood hpos
    hratio herr χ hχ0 hχ1 hχB

end GeometricMeasure
