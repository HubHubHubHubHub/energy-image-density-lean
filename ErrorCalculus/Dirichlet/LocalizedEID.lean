import ErrorCalculus.Dirichlet.LocalizedWeights

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {d : ℕ}

/-- chain rule and integration by parts with a scalar localization. -/
theorem localized_ibp (hd : 0 < d) (u : Fin d → S.dom)
    (hu : ∀ j, (u j : Lp ℝ 2 μ) ∈ S.generatorDom)
    (w : Fin d → Fin d → S.dom) (hw : ∀ i j, AEBounded (μ := μ) (w i j : Lp ℝ 2 μ))
    (ψ : Ω → ℝ)
    (hinv : ∀ i k, ∀ᵐ a ∂μ, ∑ j, (w i j : Lp ℝ 2 μ) a * S.Γ (u j) (u k) a =
      ψ a * (if i = k then 1 else 0))
    (i : Fin d) (φ : (Fin d → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (hk : HasCompactSupport φ) :
    (∫ a, fderiv ℝ φ (S.representativeVec u a) (Pi.single i 1) * ψ a ∂μ) =
      ∫ a, φ (S.representativeVec u a) * S.generatorDivergence u hu w i a ∂μ := by
  classical
  have he : (fun a => fderiv ℝ φ (S.representativeVec u a) (Pi.single i 1) * ψ a) =ᵐ[μ]
      fun a => ∑ j, (w i j : Lp ℝ 2 μ) a * S.Γ (S.compactComp hd u φ hφ hk) (u j) a := by
    filter_upwards [ae_all_iff.mpr (fun j => S.gamma_comp_eq_sum hd u hφ hk
      (S.compactComp hd u φ hφ hk) (S.coeFn_compactComp hd u φ hφ hk) (u j)),
      ae_all_iff.mpr (hinv i)] with a hc hi
    symm
    simp_rw [hc]
    calc
      _ = ∑ k, fderiv ℝ φ (S.representativeVec u a) (Pi.single k 1) *
          (∑ j, (w i j : Lp ℝ 2 μ) a * S.Γ (u j) (u k) a) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro j _
        rw [S.Γ_symm (u k) (u j)]
        ring
      _ = _ := by simp [hi]
  exact (integral_congr_ae he).trans
    (S.hasDivergence_of_generator_coeFn hd u hu w hw i φ hφ hk)

/--
Integration by parts for the finite localized measure yields absolute continuity; the divergence
remains integrable on the source, without division by the cutoff.
-/
theorem map_withDensity_absolutelyContinuous_of_localized_weights (hd : 0 < d)
    (u : Fin d → S.dom) (hu : ∀ j, (u j : Lp ℝ 2 μ) ∈ S.generatorDom)
    (w : Fin d → Fin d → S.dom) (hw : ∀ i j, AEBounded (μ := μ) (w i j : Lp ℝ 2 μ))
    (ψ : Ω → ℝ) (hm : Measurable ψ) (h0 : ∀ a, 0 ≤ ψ a) (h1 : ∀ a, ψ a ≤ 1)
    (hinv : ∀ i k, ∀ᵐ a ∂μ, ∑ j, (w i j : Lp ℝ 2 μ) a * S.Γ (u j) (u k) a =
      ψ a * (if i = k then 1 else 0)) :
    (μ.withDensity (fun a => ENNReal.ofReal (ψ a))).map (S.toEuclidean u) ≪ volume := by
  have hle : μ.withDensity (fun a => ENNReal.ofReal (ψ a)) ≤ μ := by
    calc
      _ ≤ μ.withDensity 1 := withDensity_mono
        (Eventually.of_forall (fun a => by simpa using ENNReal.ofReal_le_ofReal (h1 a)))
      _ = μ := withDensity_one
  letI : IsFiniteMeasure (μ.withDensity (fun a => ENNReal.ofReal (ψ a))) :=
    isFiniteMeasure_of_le μ hle
  apply Foundations.absolutelyContinuous_map_of_ibp hd (S.measurable_toEuclidean u)
    (C := fun i => ‖S.generatorDivergence u hu w i‖) (fun i => norm_nonneg _)
  intro i φ hφ hk
  have H := S.localized_ibp hd u hu w hw ψ hinv i (φ ∘ euclideanEquiv d)
    ((hφ.of_le (by simp)).comp (euclideanEquiv d).contDiff)
    (hk.comp_homeomorph (euclideanEquiv d).toHomeomorph)
  simp_rw [fderiv_comp_euclideanEquiv (hφ.differentiable (by simp))] at H
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (h0 _), smul_eq_mul, mul_comm (ψ _)]
  change |∫ a, fderiv ℝ φ (euclideanEquiv d (S.representativeVec u a))
    (EuclideanSpace.basisFun (Fin d) ℝ i) * ψ a ∂μ| ≤ _
  rw [H]
  exact abs_integral_mul_L1_le (S.generatorDivergence u hu w i) (fun a => φ.norm_coe_le_norm _)

omit [IsProbabilityMeasure μ] in
/-- Countable gluing of localized laws. Eventual equality to one is stronger than
pointwise monotone convergence and permits a direct null-set proof. -/
theorem absolutelyContinuous_map_of_eventually_one {E : Type*} [MeasurableSpace E]
    (X : Ω → E) (hX : Measurable X) (ν : Measure E) (ψ : ℕ → Ω → ℝ)
    (hm : ∀ n, Measurable (ψ n))
    (hψ : ∀ᵐ a ∂μ, ∀ᶠ n : ℕ in atTop, ψ n a = 1)
    (ha : ∀ n, (μ.withDensity (fun a => ENNReal.ofReal (ψ n a))).map X ≪ ν) :
    μ.map X ≪ ν := by
  apply Measure.AbsolutelyContinuous.mk
  intro B hB hν
  rw [Measure.map_apply hX hB]
  have hn (n : ℕ) : ∀ᵐ a ∂μ, ENNReal.ofReal (ψ n a) ≠ 0 → X a ∉ B := by
    apply (ae_withDensity_iff (hm n).ennreal_ofReal).mp
    have hz := ha n hν
    rw [Measure.map_apply hX hB] at hz
    exact ae_iff.mpr (by simpa only [Set.preimage, not_not] using hz)
  have he : ∀ᵐ a ∂μ, X a ∉ B := by
    filter_upwards [ae_all_iff.mpr hn, hψ] with a hn hψ
    obtain ⟨n,hn1⟩ := hψ.exists
    exact hn n (by rw [hn1]; simp)
  simpa only [Set.preimage, not_not] using ae_iff.mp he

/--
In positive dimension, generator-domain coordinates with bounded domain representatives of every
carré-du-champ entry and an a.e. positive determinant have an absolutely continuous joint law.
-/
theorem absolutelyContinuous_map_of_det_pos (hd : 0 < d) (u : Fin d → S.dom)
    (hu : ∀ j, (u j : Lp ℝ 2 μ) ∈ S.generatorDom)
    (hΓ : ∀ i j, ∃ v : S.dom,
      ⇑(v : Lp ℝ 2 μ) =ᵐ[μ] S.Γ (u i) (u j) ∧ AEBounded (μ := μ) (v : Lp ℝ 2 μ))
    (hdet : ∀ᵐ a ∂μ, 0 < (Matrix.of (fun i j => S.Γ (u i) (u j) a)).det) :
    μ.map (S.toEuclidean u) ≪ volume := by
  classical
  let v : Fin d → Fin d → S.dom := fun i j => (hΓ i j).choose
  let A : Fin d → Fin d → Ω → ℝ := fun i j => S.representative (v i j)
  have hA (i j : Fin d) : A i j ∈ S.boundedDomAlgebra :=
    ⟨v i j, S.coeFn_representative (v i j),
      (hΓ i j).choose_spec.2.congr (S.coeFn_representative (v i j))⟩
  have hAG (i j : Fin d) : A i j =ᵐ[μ] S.Γ (u i) (u j) :=
    (S.coeFn_representative (v i j)).symm.trans (hΓ i j).choose_spec.1
  let D : Ω → ℝ := fun a => (Matrix.of (fun i j => A i j a)).det
  have hmD : Measurable D := by
    dsimp [D]
    simp_rw [Matrix.det_apply', Matrix.of_apply]
    apply Finset.measurable_sum
    intro σ _
    apply measurable_const.mul
    exact Finset.measurable_prod _ (fun i _ => S.measurable_representative (v (σ i) i))
  have hD : ∀ᵐ a ∂μ, 0 < D a := by
    filter_upwards [hdet, ae_all_iff.mpr (fun i => ae_all_iff.mpr (hAG i))] with a hd he
    simpa only [D, he] using hd
  let ψ : ℕ → Ω → ℝ := fun n a => localizationCutoff ((1/2 : ℝ)^n) (D a)
  have hmψ (n : ℕ) : Measurable (ψ n) :=
    (localizationCutoff_contDiff _).continuous.measurable.comp hmD
  apply absolutelyContinuous_map_of_eventually_one (S.toEuclidean u)
    (S.measurable_toEuclidean u) volume ψ hmψ
    (hD.mono (fun a ha => localizationCutoff_eventually_one ha))
  intro n
  apply S.map_withDensity_absolutelyContinuous_of_localized_weights hd u hu
    (S.localizedWeights ((1/2 : ℝ)^n) (by positivity) A hA)
    (S.bounded_localizedWeights ((1/2 : ℝ)^n) (by positivity) A hA)
    (ψ n) (hmψ n) (fun a => localizationCutoff_nonneg _ _) (fun a => localizationCutoff_le_one _ _)
  exact S.localizedWeights_inverse u ((1/2 : ℝ)^n) (by positivity) A hA hAG

/-- The same conclusion with product Lebesgue measure. -/
theorem absolutelyContinuous_map_representativeVec_of_det_pos (hd : 0 < d) (u : Fin d → S.dom)
    (hu : ∀ j, (u j : Lp ℝ 2 μ) ∈ S.generatorDom)
    (hΓ : ∀ i j, ∃ v : S.dom,
      ⇑(v : Lp ℝ 2 μ) =ᵐ[μ] S.Γ (u i) (u j) ∧ AEBounded (μ := μ) (v : Lp ℝ 2 μ))
    (hdet : ∀ᵐ a ∂μ, 0 < (Matrix.of (fun i j => S.Γ (u i) (u j) a)).det) :
    μ.map (S.representativeVec u) ≪ volume :=
  absolutelyContinuous_map_pi_of_euclidean (S.measurable_representativeVec u)
    (S.absolutelyContinuous_map_of_det_pos hd u hu hΓ hdet)

end ErrorCalculus.ErrorStructure
