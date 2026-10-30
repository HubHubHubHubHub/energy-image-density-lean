import GeometricMeasure.Analysis.CoordinateTransport
import GeometricMeasure.Current.NormalFamily
import GeometricMeasure.Current.LinearCombinations
import GeometricMeasure.Current.MollificationDiagonal

/-!
# Coordinate Normal Family

## Main results
DPR Corollary 1.12 in coordinate form, field by field from `ErrorCalculus.PolarCurrent n`,
`PolarCurrent.IsNormal` and `ErrorCalculus.DePhilippisRindler n`
(`C_lean/ErrorCalculus/Dirichlet/{PolarCurrent,DePhilippisRindlerHypothesis}.lean`), without
importing ErrorCalculus. Copied fields: finite mass `mass`, measurable `direction`, transported
Euclidean norm `‖(PiLp.continuousLinearEquiv 2 ℝ _).symm (direction y)‖ = 1` (= `polarNorm`),
boundary `∫ Σⱼ fderiv φ y (Pi.single j 1) · direction y j ∂mass` (= `boundary` = `action`),
normality through two finite measures σp, σm on compactly supported `ContDiff ℝ ∞` tests. Approach:
transport by `WithLp.toLp 2` (1); normality implies measure divergence of mass.map toLp ⊗
transported direction, with transported D = σp − σm (boundary = −div on both sides); polar interface
`absolutelyContinuous_volume_of_unit_density`; return to product volume by volume preservation.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff

namespace GeometricMeasure
variable {n : ℕ}

/-- Direction transported to Euclidean space: x ↦ toLp (direction (ofLp x)). -/
def coordinateDirection (direction : (Fin n → ℝ) → (Fin n → ℝ)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun x => WithLp.toLp 2 (direction (WithLp.ofLp x))

/-- Transported divergence: (σp − σm) pushed forward by toLp, a finite signed measure. -/
def coordinateDivergence (σp σm : Measure (Fin n → ℝ)) [IsFiniteMeasure σp]
    [IsFiniteMeasure σm] : SignedMeasure (EuclideanSpace ℝ (Fin n)) :=
  (σp.map (WithLp.toLp 2)).toSignedMeasure + -(σm.map (WithLp.toLp 2)).toSignedMeasure

/-- A measurable direction remains measurable after transport. -/
theorem measurable_coordinateDirection {direction : (Fin n → ℝ) → (Fin n → ℝ)}
    (hdir : Measurable direction) : Measurable (coordinateDirection direction) :=
  (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp (hdir.comp measurable_coordinateOfLp)

/--
Transported Euclidean norm: `polarNorm (direction y) = 1` mass-a.e. gives ‖transported direction‖ =
1 (mass.map toLp)-a.e.
-/
theorem ae_norm_coordinateDirection (mass : Measure (Fin n → ℝ))
    {direction : (Fin n → ℝ) → (Fin n → ℝ)}
    (hnorm : ∀ᵐ y ∂mass,
      ‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm (direction y)‖ = 1) :
    ∀ᵐ x ∂(mass.map (WithLp.toLp 2)), ‖coordinateDirection direction x‖ = 1 := by
  rw [measurableEmbedding_coordinateToLp.ae_map_iff]
  filter_upwards [hnorm] with y hy
  exact hy

/--
normality in the sense of (`PolarCurrent.IsNormal`, copied fields) implies measure divergence in the
distributional sense (`HasMeasureDivergence`, boundary = −div) for the transported current (mass.map
toLp).withDensityᵥ (transported direction), with transported D = σp − σm.
-/
theorem hasMeasureDivergence_of_coordinate_normal
    (mass : Measure (Fin n → ℝ)) [IsFiniteMeasure mass]
    (direction : (Fin n → ℝ) → (Fin n → ℝ)) (hdir : Measurable direction)
    (hnorm : ∀ᵐ y ∂mass,
      ‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm (direction y)‖ = 1)
    (σp σm : Measure (Fin n → ℝ)) [IsFiniteMeasure σp] [IsFiniteMeasure σm]
    (hb : ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, ∑ j, fderiv ℝ φ y (Pi.single j 1) * direction y j ∂mass) =
        -(∫ y, φ y ∂σp) + ∫ y, φ y ∂σm) :
    HasMeasureDivergence ((mass.map (WithLp.toLp 2)).withDensityᵥ (coordinateDirection direction))
      (coordinateDivergence σp σm) := by
  intro ψ
  have hvp := variation_and_polar_of_unit_density (mass.map (WithLp.toLp 2))
    (measurable_coordinateDirection hdir).aestronglyMeasurable
    (ae_norm_coordinateDirection mass hnorm)
  obtain ⟨hφ, hcs⟩ := contDiff_hasCompactSupport_comp_coordinateToLp ψ.contDiff ψ.hasCompactSupport
  have hbψ := hb _ hφ hcs
  have hsum : ∀ y, ∑ j, fderiv ℝ (fun y : Fin n → ℝ => ψ (WithLp.toLp 2 y)) y (Pi.single j 1) *
      direction y j = fderiv ℝ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (WithLp.toLp 2 y)
        (WithLp.toLp 2 (direction y)) := fun y => by
    rw [sum_apply_single_mul, fderiv_comp_coordinateToLp]
  simp only [hsum] at hbψ
  have hpol : (fun x => fderiv ℝ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) x
      (polarDensity ((mass.map (WithLp.toLp 2)).withDensityᵥ (coordinateDirection direction)) x))
      =ᵐ[mass.map (WithLp.toLp 2)]
      fun x => fderiv ℝ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) x (coordinateDirection direction x) :=
    hvp.2.mono (fun x hx => congrArg _ hx)
  rw [coordinateDivergence, signedTestCurrent_add, signedTestCurrent_neg, add_apply, neg_apply,
    signedTestCurrent_toSignedMeasure, signedTestCurrent_toSignedMeasure,
    oneCurrentBoundary_apply, measureOneCurrent_apply, currentTestDerivative_apply, hvp.1,
    integral_congr_ae hpol,
    measurableEmbedding_coordinateToLp.integral_map, measurableEmbedding_coordinateToLp.integral_map,
    measurableEmbedding_coordinateToLp.integral_map]
  simp only [coordinateDirection]
  rw [hbψ]
  ring

/--
DPR arXiv pp. 4–5, **Corollary 1.12, coordinate form** (fields of `ErrorCalculus.PolarCurrent n` and
`PolarCurrent.IsNormal` copied without importing ErrorCalculus): n finite polar currents on `Fin n →
ℝ` (finite masses, measurable directions of Euclidean norm 1 a.e.), normal (boundary = −(σp − σm) on
compactly supported `ContDiff ℝ ∞` tests); every measure ν (no finiteness required) with ν ≪ massᵢ
and span{directionᵢ(y)} = ℝⁿ ν-a.e. satisfies ν ≪ volume (product volume on `Fin n → ℝ`). Every n.
-/
theorem absolutelyContinuous_volume_of_coordinate_normal
    (mass : Fin n → Measure (Fin n → ℝ)) [hfin : ∀ i, IsFiniteMeasure (mass i)]
    (direction : Fin n → (Fin n → ℝ) → (Fin n → ℝ)) (hdir : ∀ i, Measurable (direction i))
    (hnorm : ∀ i, ∀ᵐ y ∂(mass i),
      ‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm (direction i y)‖ = 1)
    (hnormal : ∀ i, ∃ σp σm : Measure (Fin n → ℝ), IsFiniteMeasure σp ∧ IsFiniteMeasure σm ∧
      ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ y, ∑ j, fderiv ℝ φ y (Pi.single j 1) * direction i y j ∂(mass i)) =
          -(∫ y, φ y ∂σp) + ∫ y, φ y ∂σm)
    (ν : Measure (Fin n → ℝ)) (hν : ∀ i, ν ≪ mass i)
    (hspan : ∀ᵐ y ∂ν, Submodule.span ℝ (range fun i => direction i y) = ⊤) :
    ν ≪ volume := by
  have hdiv : ∀ i, ∃ D : SignedMeasure (EuclideanSpace ℝ (Fin n)), HasMeasureDivergence
      (((mass i).map (WithLp.toLp 2)).withDensityᵥ (coordinateDirection (direction i))) D := by
    intro i
    obtain ⟨σp, σm, hp, hm, hb⟩ := hnormal i
    exact ⟨_, hasMeasureDivergence_of_coordinate_normal (mass i) (direction i) (hdir i) (hnorm i)
      σp σm hb⟩
  choose D hD using hdiv
  apply absolutelyContinuous_volume_of_map_coordinateToLp
  refine absolutelyContinuous_volume_of_unit_density (fun i => (mass i).map (WithLp.toLp 2))
    (fun i => coordinateDirection (direction i))
    (fun i => (measurable_coordinateDirection (hdir i)).aestronglyMeasurable)
    (fun i => ae_norm_coordinateDirection (mass i) (hnorm i)) D hD _
    (fun i => (hν i).map (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable) ?_
  rw [measurableEmbedding_coordinateToLp.ae_map_iff]
  filter_upwards [hspan] with y hy
  simpa only [coordinateDirection, WithLp.ofLp_toLp] using
    span_range_coordinateToLp_eq_top (fun i => direction i y) hy

/--
**coordinate statement**: field-by-field copy of `ErrorCalculus.DePhilippisRindler n`, with
the structure `PolarCurrent n` expanded into its five fields and `IsNormal`, `boundary`, `action`,
`polarNorm` into their definitions.
-/
def CoordinateDePhilippisRindler (n : ℕ) : Prop :=
  ∀ (mass : Fin n → Measure (Fin n → ℝ)), (∀ i, IsFiniteMeasure (mass i)) →
  ∀ (direction : Fin n → (Fin n → ℝ) → (Fin n → ℝ)), (∀ i, Measurable (direction i)) →
  (∀ i, ∀ᵐ y ∂(mass i),
    ‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm (direction i y)‖ = 1) →
  (∀ i, ∃ σp σm : Measure (Fin n → ℝ), IsFiniteMeasure σp ∧ IsFiniteMeasure σm ∧
    ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, ∑ j, fderiv ℝ φ y (Pi.single j 1) * direction i y j ∂(mass i)) =
        -(∫ y, φ y ∂σp) + ∫ y, φ y ∂σm) →
  ∀ ν : Measure (Fin n → ℝ), IsFiniteMeasure ν →
    (∀ i, ν ≪ mass i) →
    (∀ᵐ y ∂ν, Submodule.span ℝ (Set.range (fun i => direction i y)) = ⊤) →
    ν ≪ volume

/--
DPR arXiv pp. 4–5, Corollary 1.12 in the exact form of `ErrorCalculus.DePhilippisRindler n`, with
fields expanded: the coordinate statement is proved for every n. The bridge to (projections of
`PolarCurrent` fields, 4–5.6) is NOT provided here: it belongs to a separate bridge project.
-/
theorem coordinateDePhilippisRindler (n : ℕ) : CoordinateDePhilippisRindler n := by
  intro mass hfin direction hdir hnorm hnormal ν _ hν hspan
  exact absolutelyContinuous_volume_of_coordinate_normal (hfin := hfin) mass direction hdir hnorm
    hnormal ν hν hspan

end GeometricMeasure
