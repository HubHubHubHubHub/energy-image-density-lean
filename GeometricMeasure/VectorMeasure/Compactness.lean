import GeometricMeasure.VectorMeasure.WeakConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-! Simultaneous extraction of finite positive measures and Euclidean RN assembly. -/
noncomputable section
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology

namespace GeometricMeasure
variable {d : ℕ} {m : ℕ}

/-- The map/comap identity used in Prokhorov, with the support hypothesis explicit. -/
theorem finiteMeasure_map_comap_subtype
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d))) (hμ : μ Kᶜ = 0) :
    (FiniteMeasure.comap (Subtype.val : K → EuclideanSpace ℝ (Fin d)) μ).map
      Subtype.val = μ := by
  let f : K → EuclideanSpace ℝ (Fin d) := Subtype.val
  have hf : Topology.IsClosedEmbedding f := Topology.IsClosedEmbedding.subtypeVal hK.isClosed
  have rf : range f = K := Subtype.range_val
  apply FiniteMeasure.eq_of_forall_toMeasure_apply_eq
  intro s hs
  simp only [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_comap]
  rw [Measure.map_apply measurable_subtype_coe hs,
    Measure.comap_apply _ Subtype.val_injective, image_preimage_eq_inter_range]
  · rw [← Measure.restrict_apply hs, Measure.restrict_eq_self_of_ae_mem]
    apply (FiniteMeasure.null_iff_toMeasure_null μ (range f)ᶜ).mp
    rw [rf]
    exact hμ
  · exact fun t ht => hf.measurableEmbedding.measurableSet_image' ht
  · exact hf.continuous.measurable hs

theorem exists_finiteMeasure_family_subseq
    {ι : Type*} [Fintype ι]
    (μs : ℕ → ι → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (C : ℝ≥0)
    (hmass : ∀ n, ∀ i, (μs n i).mass ≤ C)
    (hsupport : ∀ n, ∀ i, μs n i Kᶜ = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ α : ι → FiniteMeasure (EuclideanSpace ℝ (Fin d)),
        (∀ i, (α i).mass ≤ C) ∧ (∀ i, α i Kᶜ = 0) ∧
        (∀ i, Tendsto (fun j => μs (φ j) i) atTop (𝓝 (α i))) := by
  classical
  by_cases hKe : K = ∅
  · have hz (n : ℕ) (i : ι) : μs n i = 0 := by
      apply (FiniteMeasure.mass_zero_iff _).mp
      have h := hsupport n i
      rw [hKe, compl_empty] at h
      exact h
    refine ⟨id, strictMono_id, fun _ => 0, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro i
      simp only [hz]
      exact tendsto_const_nhds
  haveI : Nonempty K := Set.nonempty_iff_ne_empty.mpr hKe |>.to_subtype
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : (Icc (0 : ℝ≥0) C × ProbabilityMeasure K) →
      FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
    fun z => (z.1.val • z.2.toFiniteMeasure).map Subtype.val
  have hF : Continuous F := by
    apply (FiniteMeasure.continuous_map continuous_subtype_val).comp
    exact (continuous_subtype_val.comp continuous_fst).smul
      ((ProbabilityMeasure.toFiniteMeasure_isEmbedding K).continuous.comp continuous_snd)
  let μK (n : ℕ) (i : ι) := FiniteMeasure.comap
    (Subtype.val : K → EuclideanSpace ℝ (Fin d)) (μs n i)
  let z (n : ℕ) (i : ι) : Icc (0 : ℝ≥0) C × ProbabilityMeasure K :=
    (⟨(μK n i).mass, zero_le, (FiniteMeasure.mass_comap_le _ _).trans (hmass n i)⟩,
      (μK n i).normalize)
  have hz (n : ℕ) (i : ι) : F (z n i) = μs n i := by
    change ((μK n i).mass • (μK n i).normalize.toFiniteMeasure).map _ = _
    rw [← FiniteMeasure.self_eq_mass_smul_normalize]
    exact finiteMeasure_map_comap_subtype hK _ (hsupport n i)
  obtain ⟨a, φ, hφ, ha⟩ := CompactSpace.tendsto_subseq z
  refine ⟨φ, hφ, fun i => F (a i), ?_, ?_, ?_⟩
  · intro i
    apply (FiniteMeasure.mass_map_le _ _).trans
    calc
      _ = (a i).1.val := by
        change ((a i).1.val • (a i).2.toFiniteMeasure) univ = _
        rw [FiniteMeasure.smul_apply]
        change (a i).1.val * (a i).2.toFiniteMeasure.mass = _
        rw [ProbabilityMeasure.mass_toFiniteMeasure, mul_one]
      _ ≤ C := (a i).1.property.2
  · intro i
    apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
    rw [FiniteMeasure.toMeasure_map, Measure.map_apply measurable_subtype_coe hK.measurableSet.compl]
    simp
  · intro i
    have hi := hF.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp ha) i)
    simpa only [Function.comp_def, hz] using hi

def positiveFamilyReference
    (αpos : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (αneg : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  ∑ i, ((αpos i : Measure (EuclideanSpace ℝ (Fin d))) +
    (αneg i : Measure (EuclideanSpace ℝ (Fin d))))

instance isFiniteMeasure_positiveFamilyReference
    (αpos : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (αneg : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d))) :
    IsFiniteMeasure (positiveFamilyReference αpos αneg) := by
  unfold positiveFamilyReference
  infer_instance

theorem positiveFamily_pos_le
    (αpos : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (αneg : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d))) (i : Fin m) :
    (αpos i : Measure (EuclideanSpace ℝ (Fin d))) ≤ positiveFamilyReference αpos αneg := by
  intro s
  simp only [positiveFamilyReference, Measure.finsetSum_apply, Measure.add_apply]
  exact (le_self_add : (αpos i : Measure _) s ≤ (αpos i : Measure _) s +
    (αneg i : Measure _) s).trans (Finset.single_le_sum (f := fun j => (αpos j : Measure _) s + (αneg j : Measure _) s)
      (fun _ _ => zero_le) (Finset.mem_univ i))

theorem positiveFamily_neg_le
    (αpos : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (αneg : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d))) (i : Fin m) :
    (αneg i : Measure (EuclideanSpace ℝ (Fin d))) ≤ positiveFamilyReference αpos αneg := by
  intro s
  simp only [positiveFamilyReference, Measure.finsetSum_apply, Measure.add_apply]
  exact (le_add_self : (αneg i : Measure _) s ≤ (αpos i : Measure _) s +
    (αneg i : Measure _) s).trans (Finset.single_le_sum (f := fun j => (αpos j : Measure _) s + (αneg j : Measure _) s)
      (fun _ _ => zero_le) (Finset.mem_univ i))

def positiveFamilyDensity
    (αpos : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (αneg : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) :=
  fun x => WithLp.toLp 2 (fun i =>
    ((αpos i : Measure (EuclideanSpace ℝ (Fin d))).rnDeriv
      (positiveFamilyReference αpos αneg) x).toReal -
    ((αneg i : Measure (EuclideanSpace ℝ (Fin d))).rnDeriv
      (positiveFamilyReference αpos αneg) x).toReal)

theorem integrable_positiveFamilyDensity
    (αpos : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (αneg : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d))) :
    Integrable (positiveFamilyDensity αpos αneg) (positiveFamilyReference αpos αneg) := by
  apply integrable_piLp_iff.mpr
  intro i
  exact Measure.integrable_toReal_rnDeriv.sub Measure.integrable_toReal_rnDeriv

def assemblePositiveFamily
    (αpos : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (αneg : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d))) :
    VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)) :=
  (positiveFamilyReference αpos αneg).withDensityᵥ (positiveFamilyDensity αpos αneg)

theorem coord_assemblePositiveFamily
    (αpos : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (αneg : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d))) (i : Fin m) :
    coord (assemblePositiveFamily αpos αneg) i =
      (αpos i : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure -
      (αneg i : Measure (EuclideanSpace ℝ (Fin d))).toSignedMeasure := by
  apply VectorMeasure.ext
  intro s hs
  rw [coord_apply, assemblePositiveFamily,
    withDensityᵥ_apply (integrable_positiveFamilyDensity αpos αneg) hs]
  rw [eval_integral_piLp (fun j =>
    ((integrable_positiveFamilyDensity αpos αneg).eval_piLp j).restrict)]
  change (∫ x in s, _ - _ ∂positiveFamilyReference αpos αneg) = _
  rw [integral_sub Measure.integrable_toReal_rnDeriv.restrict
    Measure.integrable_toReal_rnDeriv.restrict,
    Measure.setIntegral_toReal_rnDeriv (positiveFamily_pos_le αpos αneg i).absolutelyContinuous,
    Measure.setIntegral_toReal_rnDeriv (positiveFamily_neg_le αpos αneg i).absolutelyContinuous,
    Measure.toSignedMeasure_sub_apply hs]

theorem variation_assemblePositiveFamily_compl
    (αpos : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (αneg : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hpos : ∀ i, αpos i Kᶜ = 0) (hneg : ∀ i, αneg i Kᶜ = 0) :
    (assemblePositiveFamily αpos αneg).variation Kᶜ = 0 := by
  rw [assemblePositiveFamily, Measure.variation_withDensityᵥ (integrable_positiveFamilyDensity _ _)]
  apply withDensity_absolutelyContinuous
  simp only [positiveFamilyReference, Measure.finsetSum_apply, Measure.add_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [(FiniteMeasure.null_iff_toMeasure_null _ _).mp (hpos i),
    (FiniteMeasure.null_iff_toMeasure_null _ _).mp (hneg i), add_zero]


def boundedCovectorCoefficient (ω : BoundedCovectorField d m) (i : Fin m) :
    BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).compLeftContinuousBounded _ ω

@[simp] theorem boundedCovectorCoefficient_apply
    (ω : BoundedCovectorField d m) (i : Fin m) (x : EuclideanSpace ℝ (Fin d)) :
    boundedCovectorCoefficient ω i x = ω x (EuclideanSpace.single i 1) := rfl

theorem covector_apply_eq_sum
    (ℓ : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin m)) :
    ℓ v = ∑ i, v i * ℓ (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, smul_eq_mul]

theorem vectorMeasurePairing_assemblePositiveFamily
    (αpos : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (αneg : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (ω : BoundedCovectorField d m) :
    vectorMeasurePairing (assemblePositiveFamily αpos αneg) ω =
      ∑ i, ((∫ x, ω x (EuclideanSpace.single i 1) ∂(αpos i : Measure _)) -
        (∫ x, ω x (EuclideanSpace.single i 1) ∂(αneg i : Measure _))) := by
  let ν := positiveFamilyReference αpos αneg
  haveI : IsFiniteMeasure ν := isFiniteMeasure_positiveFamilyReference αpos αneg
  haveI (i : Fin m) : (αpos i : Measure _).HaveLebesgueDecomposition ν :=
    Measure.haveLebesgueDecomposition_of_sigmaFinite _ _
  haveI (i : Fin m) : (αneg i : Measure _).HaveLebesgueDecomposition ν :=
    Measure.haveLebesgueDecomposition_of_sigmaFinite _ _
  let g := boundedCovectorCoefficient ω
  have hp (i : Fin m) : Integrable (fun x =>
      ((αpos i : Measure _).rnDeriv ν x).toReal * g i x) ν :=
    (integrable_toReal_rnDeriv_mul_iff
      (positiveFamily_pos_le αpos αneg i).absolutelyContinuous).mpr ((g i).integrable _)
  have hn (i : Fin m) : Integrable (fun x =>
      ((αneg i : Measure _).rnDeriv ν x).toReal * g i x) ν :=
    (integrable_toReal_rnDeriv_mul_iff
      (positiveFamily_neg_le αpos αneg i).absolutelyContinuous).mpr ((g i).integrable _)
  rw [assemblePositiveFamily,
    vectorMeasurePairing_withDensityᵥ _ (integrable_positiveFamilyDensity αpos αneg)]
  calc
    _ = ∫ x, ∑ i, (((αpos i : Measure _).rnDeriv ν x).toReal * g i x -
        ((αneg i : Measure _).rnDeriv ν x).toReal * g i x) ∂ν := by
      apply integral_congr_ae
      filter_upwards with x
      rw [covector_apply_eq_sum]
      apply Finset.sum_congr rfl
      intro i hi
      change (_ - _) * _ = _ * _ - _ * _
      exact sub_mul _ _ _
    _ = ∑ i, ∫ x, (((αpos i : Measure _).rnDeriv ν x).toReal * g i x -
        ((αneg i : Measure _).rnDeriv ν x).toReal * g i x) ∂ν :=
      integral_finsetSum _ (fun i _ => (hp i).sub (hn i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_sub (hp i) (hn i),
        integral_toReal_rnDeriv_mul (positiveFamily_pos_le αpos αneg i).absolutelyContinuous,
        integral_toReal_rnDeriv_mul (positiveFamily_neg_le αpos αneg i).absolutelyContinuous]
      rfl

def coordinatePositiveFinite
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (i : Fin m) : FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
  ⟨coordinatePositiveMeasure M i, inferInstance⟩

def coordinateNegativeFinite
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (i : Fin m) : FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
  ⟨coordinateNegativeMeasure M i, inferInstance⟩

theorem assemble_coordinateParts_eq
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m))) :
    assemblePositiveFamily (coordinatePositiveFinite M) (coordinateNegativeFinite M) = M := by
  apply ext_of_coord_eq
  intro i
  rw [coord_assemblePositiveFamily, coord_eq_coordinateParts]
  rfl

theorem vectorMeasurePairing_eq_coordinateParts
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (ω : BoundedCovectorField d m) :
    vectorMeasurePairing M ω =
      ∑ i, ((∫ x, ω x (EuclideanSpace.single i 1) ∂coordinatePositiveMeasure M i) -
        (∫ x, ω x (EuclideanSpace.single i 1) ∂coordinateNegativeMeasure M i)) := by
  have h := vectorMeasurePairing_assemblePositiveFamily
    (coordinatePositiveFinite M) (coordinateNegativeFinite M) ω
  rw [assemble_coordinateParts_eq] at h
  exact h

theorem weaklyTendsto_assemble_of_coordinateParts_tendsto
    (Ms : ℕ → VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (αpos : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (αneg : Fin m → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (hpos : ∀ i, Tendsto (fun n => coordinatePositiveFinite (Ms n) i) atTop (𝓝 (αpos i)))
    (hneg : ∀ i, Tendsto (fun n => coordinateNegativeFinite (Ms n) i) atTop (𝓝 (αneg i))) :
    VectorMeasureWeaklyTendsto Ms (assemblePositiveFamily αpos αneg) := by
  intro ω
  rw [vectorMeasurePairing_assemblePositiveFamily]
  simp only [vectorMeasurePairing_eq_coordinateParts]
  apply tendsto_finsetSum
  intro i hi
  exact ((FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp (hpos i))
    (boundedCovectorCoefficient ω i)).sub
    ((FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp (hneg i))
      (boundedCovectorCoefficient ω i))

def coordinateFiniteFamily
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (i : Fin m × Bool) : FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
  if i.2 then coordinateNegativeFinite M i.1 else coordinatePositiveFinite M i.1

theorem coordinateFiniteFamily_le_variation
    (M : VectorMeasure (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin m)))
    (i : Fin m × Bool) :
    (coordinateFiniteFamily M i : Measure _) ≤ M.variation := by
  cases i with
  | mk i b =>
    cases b
    · exact coordinatePositiveMeasure_le_variation M i
    · exact coordinateNegativeMeasure_le_variation M i

theorem finiteMeasure_mass_le_of_le
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (h : (μ : Measure _) ≤ ν)
    (C : ℝ≥0) (hν : ν univ ≤ (C : ℝ≥0∞)) : μ.mass ≤ C := by
  apply ENNReal.coe_le_coe.mp
  rw [FiniteMeasure.ennreal_mass]
  exact (h univ).trans hν

theorem finiteMeasure_compl_eq_zero_of_le
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (h : (μ : Measure _) ≤ ν)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hν : ν Kᶜ = 0) : μ Kᶜ = 0 := by
  apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
  exact le_antisymm ((h Kᶜ).trans hν.le) zero_le

end GeometricMeasure

