import GeometricMeasure.Current.PolarFreezing
import GeometricMeasure.Current.Tangent
import GeometricMeasure.Current.VectorMeasureCompactness

/-!
# common positive extraction

## Main results
DPR p. 7, §2.2(i)–(ii). Good radii and weak compactness supply a common subsequence. The terms are
singular; their positive limit has mass one and a lower bound against the tent function. Neither
singularity of the limit nor convergence in variation is asserted.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ}

/--
Change-of-variables formula for the real integral under c ≥ 0; no additional
integrability assumption. DPR p. 7: positive weak extraction, normalization and singularity of the
terms.
-/
theorem integral_positiveDilation (s : Measure (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    (∫ y, f y ∂positiveDilation s x r hr c) =
      c * ∫ y in closedBall x |r|, f (dilationEquiv x r hr y) ∂s := by
  rw [positiveDilation, integral_smul_measure, ENNReal.toReal_ofReal hc, integral_map_equiv]
  rfl

/--
The real mass ratio at radii r/2 and r bounds the tent integral from below, for r > 0 and a finite
measure. DPR p. 7: positive weak extraction, normalization and singularity of the terms.
-/
theorem normalizedDilation_cutoff_ge (s : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure s] (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    s.real (closedBall x (r / 2)) / s.real (closedBall x r) ≤
      ∫ y, tentCutoff y ∂positiveDilation s x r hr.ne' (blowupScale s x r) := by
  rw [integral_positiveDilation s _ x r hr.ne' (blowupScale_nonneg _ _ _),
    blowupScale, abs_of_pos hr, div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr measureReal_nonneg)
  have hI : ∫ y in closedBall x r,
      (closedBall x (r / 2)).indicator (1 : EuclideanSpace ℝ (Fin d) → ℝ) y ∂s =
      s.real (closedBall x (r / 2)) := by
    rw [integral_indicator_one measurableSet_closedBall,
      measureReal_restrict_apply measurableSet_closedBall,
      inter_eq_left.mpr (closedBall_subset_closedBall (by linarith))]
  rw [← hI]
  apply integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall)
    (((tentCutoff : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ).compContinuous
      ⟨dilationEquiv x r hr.ne', (dilationHomeomorph x r hr.ne').continuous⟩).integrable _)
  exact fun y => indicator_closedBall_half_le_cutoff tentCutoff tentCutoff_nonneg
    (fun _ hy => tentCutoff_eq_one hy) x hr y

/--
Positive weak extraction from good radii and compactness, with a common subsequence. DPR p. 7:
positive weak extraction, normalization and singularity of the terms.
-/
theorem exists_positive_tangent_of_goodRadii
    (s : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure s]
    (x : EuclideanSpace ℝ (Fin d))
    (hgood : ∃ᶠ r in 𝓝[>] (0 : ℝ),
      s (closedBall x r) ≤ 2 ^ d * s (closedBall x (r / 2)))
    (hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < s (closedBall x r)) :
    ∃ rs : ℕ → ℝ, ∃ hrs : ∀ n, 0 < rs n,
      Tendsto rs atTop (𝓝[>] (0 : ℝ)) ∧
      (∀ n, 0 < s (closedBall x (rs n))) ∧
      ∃ ν : FiniteMeasure (EuclideanSpace ℝ (Fin d)),
        ν.mass ≤ 1 ∧ ν (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 ∧
        Tendsto (fun n => normalizedPositiveDilation s x (rs n) (hrs n).ne' ) atTop (𝓝 ν) ∧
        ((2 : ℝ) ^ d)⁻¹ ≤ ∫ y, tentCutoff y ∂(ν : Measure (EuclideanSpace ℝ (Fin d))) ∧
        0 < (ν : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 1) := by
  obtain ⟨rs, ht, hP⟩ := exists_seq_forall_of_frequently (hgood.and_eventually
    ((eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)).and hpos))
  have hrs : ∀ n, 0 < rs n := fun n => (hP n).2.1
  let μs : ℕ → Unit → FiniteMeasure (EuclideanSpace ℝ (Fin d)) := fun n _ =>
    ⟨positiveDilation s x (rs n) (hrs n).ne' (blowupScale s x (rs n)), inferInstance⟩
  have hmass : ∀ n, ∀ i, (μs n i).mass ≤ 1 := by
    intro n i
    apply ENNReal.coe_le_coe.mp
    rw [FiniteMeasure.ennreal_mass]
    change positiveDilation _ _ _ _ _ univ ≤ _
    rw [positiveDilation_normalized_univ s x _ _
      (by simpa [abs_of_pos (hrs n)] using (hP n).2.2)]
    rfl
  have hsupp : ∀ n, ∀ i, μs n i (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ = 0 := by
    intro n i
    apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
    exact positiveDilation_compl _ _ _ _ _
  obtain ⟨φ, hφ, α, hαmass, hαsupp, hαconv⟩ :=
    exists_finiteMeasure_family_subseq μs (isCompact_closedBall 0 1) 1 hmass hsupp
  have hlow : ((2 : ℝ) ^ d)⁻¹ ≤ ∫ y, tentCutoff y ∂(α () : Measure (EuclideanSpace ℝ (Fin d))) := by
    apply ge_of_tendsto' (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp (hαconv ()) tentCutoff)
    intro n
    exact (inv_two_pow_le_measureReal_ratio s x (rs (φ n)) (hP (φ n)).2.2
      (hP (φ n)).1).trans (normalizedDilation_cutoff_ge s x (hrs (φ n)))
  refine ⟨rs ∘ φ, fun n => hrs (φ n), ht.comp hφ.tendsto_atTop,
    fun n => (hP (φ n)).2.2, α (), hαmass (), hαsupp (), hαconv (), hlow, ?_⟩
  apply pos_iff_ne_zero.mpr
  intro hz
  have hi : (∫ y, tentCutoff y ∂(α () : Measure (EuclideanSpace ℝ (Fin d)))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with y hy
    exact tentCutoff_eq_zero hy
  rw [hi] at hlow
  exact (not_le_of_gt (by positivity : 0 < ((2 : ℝ) ^ d)⁻¹)) hlow

/--
Lebesgue null sets are preserved by the dilation, including nonzero negative scales. DPR p. 7:
positive weak extraction, normalization and singularity of the terms.
-/
theorem volume_absolutelyContinuous_map_dilation
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin d))) ≪ volume.map (dilationEquiv x r hr) := by
  have heq : (volume : Measure (EuclideanSpace ℝ (Fin d))).map (dilationEquiv x r hr) =
      ENNReal.ofReal |((r⁻¹) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))⁻¹| • volume := by
    have hf : (fun y : EuclideanSpace ℝ (Fin d) => r⁻¹ • (y + -x)) =
        dilationEquiv x r hr := rfl
    rw [← hf]
    change Measure.map ((fun y : EuclideanSpace ℝ (Fin d) => r⁻¹ • y) ∘
      (fun y => y + -x)) volume = _
    rw [← Measure.map_map (measurable_const_smul _) (measurable_add_const _),
      map_add_right_eq_self, Measure.map_addHaar_smul volume (inv_ne_zero hr)]
  rw [heq]
  apply Measure.absolutelyContinuous_smul
  exact ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ (inv_ne_zero hr))))

/--
Singularity with respect to volume is preserved under every dilation, for r ≠ 0 and every scalar c.
DPR p. 7: positive weak extraction, normalization and singularity of the terms.
-/
theorem positiveDilation_singular
    (s : Measure (EuclideanSpace ℝ (Fin d))) (hs : s ⟂ₘ volume)
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    positiveDilation s x r hr c ⟂ₘ volume := by
  have h := (dilationEquiv x r hr).measurableEmbedding.mutuallySingular_map
    (hs.restrict (closedBall x |r|))
  exact Measure.MutuallySingular.smul _
    (h.mono_ac (Measure.AbsolutelyContinuous.refl _) (volume_absolutelyContinuous_map_dilation x r hr))

/--
Total mass of any weak limit of these normalized positive dilations is one. DPR p. 7: positive weak
extraction, normalization and singularity of the terms.
-/
theorem normalizedPositiveDilation_limit_mass
    (s : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure s]
    (x : EuclideanSpace ℝ (Fin d)) (rs : ℕ → ℝ) (hrs : ∀ n, 0 < rs n)
    (hp : ∀ n, 0 < s (closedBall x (rs n)))
    (ν : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (hν : Tendsto (fun n => normalizedPositiveDilation s x (rs n) (hrs n).ne') atTop (𝓝 ν)) :
    ν.mass = 1 := by
  have hm : ∀ n, (normalizedPositiveDilation s x (rs n) (hrs n).ne').mass = 1 := by
    intro n
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_mass]
    exact positiveDilation_normalized_univ s x _ _ (by simpa [abs_of_pos (hrs n)] using hp n)
  have h := (FiniteMeasure.continuous_mass.tendsto ν).comp hν
  change Tendsto (fun n => (normalizedPositiveDilation s x (rs n) (hrs n).ne').mass)
    atTop (𝓝 ν.mass) at h
  simp only [hm] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end GeometricMeasure
