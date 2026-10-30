import ErrorCalculus.Dirichlet.ImageCondExp
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Image L1Transfer

## Main results
Pushforward of an arbitrary signed L¹ density, as a continuous linear map to L¹ of the image law.
Unlike image Γ, the second input need not factor through X.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n : ℕ} (X : Fin n → Lp ℝ 2 μ)

/-- Isometric L¹ pullback along the measurable image representative. -/
def imageL1Pullback : Lp ℝ 1 (imageLaw X) →ₗᵢ[ℝ] Lp ℝ 1 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (imageRepresentative_preserving X)

theorem imageL1Pullback_ae (a : Lp ℝ 1 (imageLaw X)) :
    ⇑(imageL1Pullback X a) =ᵐ[μ] fun ω => a (imageRepresentative X ω) :=
  Lp.coeFn_compMeasurePreserving a (imageRepresentative_preserving X)

/-- Measurable factor of the conditional expectation; chosen only after factorization is proved. -/
def imageL1Representative (a : Lp ℝ 1 μ) : (Fin n → ℝ) → ℝ :=
  (stronglyMeasurable_condExp (m := imageSigma X) (μ := μ) (f := ⇑a)).exists_eq_measurable_comp.choose

theorem measurable_imageL1Representative (a : Lp ℝ 1 μ) : Measurable (imageL1Representative X a) :=
  (stronglyMeasurable_condExp (m := imageSigma X) (μ := μ) (f := ⇑a)).exists_eq_measurable_comp.choose_spec.1.measurable

theorem imageL1Representative_comp (a : Lp ℝ 1 μ) :
    (imageL1Representative X a) ∘ imageRepresentative X = μ[⇑a | imageSigma X] :=
  (stronglyMeasurable_condExp (m := imageSigma X) (μ := μ) (f := ⇑a)).exists_eq_measurable_comp.choose_spec.2.symm

theorem integrable_imageL1Representative (a : Lp ℝ 1 μ) :
    Integrable (imageL1Representative X a) (imageLaw X) := by
  apply (integrable_map_measure (measurable_imageL1Representative X a).aestronglyMeasurable
    (measurable_imageRepresentative X).aemeasurable).mpr
  rw [imageL1Representative_comp]
  exact integrable_condExp

/-- L¹ class of the conditional density on the image space. -/
def imageL1Class (a : Lp ℝ 1 μ) : Lp ℝ 1 (imageLaw X) :=
  (memLp_one_iff_integrable.mpr (integrable_imageL1Representative X a)).toLp _

theorem imageL1Class_ae (a : Lp ℝ 1 μ) :
    ⇑(imageL1Class X a) =ᵐ[imageLaw X] imageL1Representative X a := MemLp.coeFn_toLp _

theorem imageL1Class_pullback (a : Lp ℝ 1 μ) :
    imageL1Pullback X (imageL1Class X a) = condExpL1CLM ℝ (imageSigma_le X) μ a := by
  apply Lp.ext
  have he := ae_eq_comp (measurable_imageRepresentative X).aemeasurable (imageL1Class_ae X a)
  have hc := condExp_ae_eq_condExpL1CLM (imageSigma_le X) (L1.integrable_coeFn a)
  have ht : (L1.integrable_coeFn a).toL1 (⇑a) = a := by
    apply Lp.ext
    exact MemLp.coeFn_toLp _
  rw [ht] at hc
  filter_upwards [imageL1Pullback_ae X (imageL1Class X a), he, hc] with ω hp he hc
  exact hp.trans (he.trans ((congrFun (imageL1Representative_comp X a) ω).trans hc))

/-- Linear conditional transfer to the image law. -/
def imageL1Linear : Lp ℝ 1 μ →ₗ[ℝ] Lp ℝ 1 (imageLaw X) where
  toFun := imageL1Class X
  map_add' a b := by
    apply (imageL1Pullback X).injective
    rw [map_add, imageL1Class_pullback, imageL1Class_pullback, imageL1Class_pullback, map_add]
  map_smul' c a := by
    apply (imageL1Pullback X).injective
    simp only [map_smul, imageL1Class_pullback, RingHom.id_apply]

/-- Continuous transfer of signed L¹ densities; its pullback is the L¹ conditional expectation. -/
def imageL1 : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (imageLaw X) :=
  (imageL1Linear X).mkContinuous ‖condExpL1CLM ℝ (imageSigma_le X) μ‖ (fun a => by
    change ‖imageL1Class X a‖ ≤ _
    rw [← (imageL1Pullback X).norm_map, imageL1Class_pullback]
    exact (condExpL1CLM ℝ (imageSigma_le X) μ).le_opNorm a)

theorem imageL1_condExp (a : Lp ℝ 1 μ) :
    (fun ω => imageL1 X a (imageRepresentative X ω)) =ᵐ[μ] μ[⇑a | imageSigma X] := by
  have he := ae_eq_comp (measurable_imageRepresentative X).aemeasurable (imageL1Class_ae X a)
  exact he.trans (Filter.Eventually.of_forall (congrFun (imageL1Representative_comp X a)))

/-- The defining bounded-test identity for the arbitrary signed density. -/
theorem imageL1_characterization (a : Lp ℝ 1 μ) (h : ImageTest (Fin n → ℝ)) :
    (∫ y, h y * imageL1 X a y ∂imageLaw X) =
      ∫ ω, h (imageRepresentative X ω) * a ω ∂μ := by
  have htest : StronglyMeasurable[imageSigma X] (fun ω => h (imageRepresentative X ω)) :=
    h.measurable.stronglyMeasurable.comp_measurable (measurable_imageRepresentative_imageSigma X)
  have hprod := condExp_mul_of_stronglyMeasurable_left htest
    ((h.comp _ (measurable_imageRepresentative X)).integrable_mul a) (L1.integrable_coeFn a)
  calc
    _ = ∫ ω, h (imageRepresentative X ω) * imageL1 X a (imageRepresentative X ω) ∂μ :=
      integral_map_of_stronglyMeasurable (measurable_imageRepresentative X)
        (h.measurable.mul (Lp.stronglyMeasurable (imageL1 X a)).measurable).stronglyMeasurable
    _ = ∫ ω, h (imageRepresentative X ω) * μ[⇑a | imageSigma X] ω ∂μ :=
      integral_congr_ae ((imageL1_condExp X a).mono (fun ω he => congrArg (fun t => h (imageRepresentative X ω) * t) he))
    _ = ∫ ω, μ[(fun ω => h (imageRepresentative X ω) * a ω) | imageSigma X] ω ∂μ :=
      (integral_congr_ae hprod).symm
    _ = _ := integral_condExp (imageSigma_le X)

end ErrorCalculus
