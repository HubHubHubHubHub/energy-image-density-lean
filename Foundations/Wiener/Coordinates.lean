import Foundations.Wiener.SchauderMap
import Foundations.Wiener.Dyadic

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

namespace Foundations

/-- A dyadic point of the closed unit interval, including the right endpoint. -/
noncomputable def dyadicPoint (j n : ℕ) (hn : n ≤ 2^j) : WienerTime :=
  ⟨(n : ℝ≥0) / 2^j, zero_le, (div_le_one (by positivity)).mpr (by exact_mod_cast hn)⟩

@[simp] theorem dyadicPoint_coe (j n : ℕ) (hn : n ≤ 2^j) :
    ((dyadicPoint j n hn : ℝ≥0) : ℝ) = (n : ℝ)/2^j := by
  simp [dyadicPoint]

/-- The continuous linear coefficient functional given by the explicit second difference. -/
noncomputable def schauderCoordinateCLM : SchauderIndex → PathSpace →L[ℝ] ℝ
  | none => ContinuousMap.evalCLM ℝ ⟨1, by simp⟩
  | some ⟨j,k⟩ => Real.sqrt ((2:ℝ)^j) •
      ((2 : ℝ) • ContinuousMap.evalCLM ℝ (dyadicPoint (j+1) (2*k+1) (by
        rw [pow_succ]; omega)) -
       ContinuousMap.evalCLM ℝ (dyadicPoint j k (Nat.le_of_lt k.isLt)) -
       ContinuousMap.evalCLM ℝ (dyadicPoint j (k+1) k.isLt))

/-- The product-valued coordinate map; each coordinate is a continuous linear functional. -/
noncomputable def schauderCoordinate (ω : PathSpace) : SchauderIndex → ℝ :=
  fun i => schauderCoordinateCLM i ω

theorem continuous_schauderCoordinate : Continuous schauderCoordinate :=
  continuous_pi fun i => (schauderCoordinateCLM i).continuous

/-- Biorthogonality of the explicit coefficient functionals and the Schauder path family. -/
theorem schauderCoordinateCLM_schauderPath (i l : SchauderIndex) :
    schauderCoordinateCLM i (schauderPath l) = if l=i then 1 else 0 := by
  classical
  cases i with
  | none =>
    cases l with
    | none => simp [schauderCoordinateCLM, schauderPath, schauderCoefficient]
    | some l =>
      obtain ⟨j,k⟩ := l
      simpa [schauderCoordinateCLM, schauderPath, schauderCoefficient] using
        (show schauder j k 1 = 0 from integral_haar_eq_zero j k k.isLt)
  | some i =>
    obtain ⟨j,k⟩ := i
    have hmid := dyadic_midpoint_grid j k
    push_cast at hmid
    cases l with
    | none =>
      simp only [schauderCoordinateCLM, smul_apply, sub_apply,
        ContinuousMap.evalCLM_apply, schauderPath, ContinuousMap.coe_mk, schauderCoefficient,
        dyadicPoint_coe, smul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, reduceCtorEq, if_false]
      rw [← hmid]
      ring
    | some l =>
      obtain ⟨l,n⟩ := l
      simp only [schauderCoordinateCLM, smul_apply, sub_apply,
        ContinuousMap.evalCLM_apply, schauderPath, ContinuousMap.coe_mk, schauderCoefficient,
        dyadicPoint_coe, smul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
      rw [← hmid, schauder_secondDifference]
      by_cases hl : l=j
      · subst l
        by_cases hn : n=k
        · subst n; simp
        · have hv : n.val ≠ k.val := fun h => hn (Fin.ext h)
          simp [hn, hv]
      · have hne : (some ⟨l,n⟩ : SchauderIndex) ≠ some ⟨j,k⟩ :=
          fun h => hl (congrArg Sigma.fst (Option.some.inj h))
        simp [hl, hne]

/-- Every included coefficient is exactly recovered from a partial sum. -/
theorem schauderCoordinate_schauderPartial (N : ℕ) (ξ : SchauderIndex → ℝ)
    {i : SchauderIndex} (hi : i ∈ schauderIndices N) :
    schauderCoordinate (schauderPartial N ξ) i = ξ i := by
  classical
  simp [schauderCoordinate, schauderPartial, map_sum, schauderCoordinateCLM_schauderPath, hi]

/-- The inverse identity holds on the entire uniform convergence set. -/
theorem schauderCoordinate_schauderMap {ξ : SchauderIndex → ℝ} (hξ : ξ ∈ schauderGoodSet) :
    schauderCoordinate (schauderMap ξ) = ξ := by
  funext i
  obtain ⟨N, hi⟩ := exists_mem_schauderIndices i
  have hlim := ((schauderCoordinateCLM i).continuous.tendsto _).comp (tendsto_schauderPartial hξ)
  have heq : (fun n => schauderCoordinateCLM i (schauderPartial n ξ)) =ᶠ[atTop] fun _ => ξ i := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact schauderCoordinate_schauderPartial n ξ (monotone_schauderIndices hn hi)
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' heq.symm)

theorem map_schauderCoordinate_wienerMeasure :
    wienerMeasure.map schauderCoordinate = schauderGaussianMeasure := by
  rw [wienerMeasure, Measure.map_map continuous_schauderCoordinate.measurable measurable_schauderMap]
  have heq : schauderCoordinate ∘ schauderMap =ᵐ[schauderGaussianMeasure] id :=
    ae_mem_schauderGoodSet.mono fun _ h => schauderCoordinate_schauderMap h
  rw [Measure.map_congr heq, Measure.map_id]

theorem measurePreserving_schauderCoordinate :
    MeasurePreserving schauderCoordinate wienerMeasure schauderGaussianMeasure :=
  ⟨continuous_schauderCoordinate.measurable, map_schauderCoordinate_wienerMeasure⟩

/-- The inverse identity on paths, outside one Wiener-null set. -/
theorem schauderMap_schauderCoordinate_ae : ∀ᵐ ω ∂wienerMeasure,
    schauderMap (schauderCoordinate ω) = ω := by
  rw [wienerMeasure, ae_map_iff measurable_schauderMap.aemeasurable]
  · filter_upwards [ae_mem_schauderGoodSet] with ξ hξ
    rw [schauderCoordinate_schauderMap hξ]
  · exact measurableSet_eq_fun
      (measurable_schauderMap.comp continuous_schauderCoordinate.measurable) measurable_id

/-- The two explicitly specified maps form a measure-space isomorphism modulo null sets. -/
theorem wienerCoordinateEquiv :
    MeasurePreserving schauderMap schauderGaussianMeasure wienerMeasure ∧
    MeasurePreserving schauderCoordinate wienerMeasure schauderGaussianMeasure ∧
    (∀ᵐ ξ ∂schauderGaussianMeasure, schauderCoordinate (schauderMap ξ) = ξ) ∧
    (∀ᵐ ω ∂wienerMeasure, schauderMap (schauderCoordinate ω) = ω) :=
  ⟨measurePreserving_schauderMap, measurePreserving_schauderCoordinate,
    ae_mem_schauderGoodSet.mono fun _ h => schauderCoordinate_schauderMap h,
    schauderMap_schauderCoordinate_ae⟩

end Foundations
