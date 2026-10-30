import ErrorCalculus.Dirichlet.ImageTests
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorData
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorData Ω μ) {m : ℕ} (X : Fin m → Lp ℝ 2 μ)

/-- The finite positive measure with density Γ[TF]. -/
def gammaMeasure (F : S.imageDom X) : Measure Ω :=
  μ.withDensity (fun ω => ENNReal.ofReal (S.Γ (S.imageLift X F) (S.imageLift X F) ω))

instance gammaMeasure_finite (F : S.imageDom X) : IsFiniteMeasure (S.gammaMeasure X F) :=
  isFiniteMeasure_withDensity_ofReal (L1.integrable_coeFn _).hasFiniteIntegral

/-- absolute continuity survives the measurable pushforward. -/
theorem gammaMeasure_map_ac (F : S.imageDom X) :
    (S.gammaMeasure X F).map (imageRepresentative X) ≪ imageLaw X :=
  (withDensity_absolutelyContinuous _ _).map (measurable_imageRepresentative X)

/-- The RN derivative is finite almost everywhere. -/
theorem imageGamma_rnDeriv_lt_top (F : S.imageDom X) :
    ∀ᵐ x ∂imageLaw X,
      ((S.gammaMeasure X F).map (imageRepresentative X)).rnDeriv (imageLaw X) x < ⊤ :=
  Measure.rnDeriv_lt_top _ _

/-- The diagonal, as the L¹ class of the real RN derivative. -/
def imageGammaDiag (F : S.imageDom X) : Lp ℝ 1 (imageLaw X) :=
  (memLp_one_iff_integrable.mpr (Measure.integrable_toReal_rnDeriv
    (μ := (S.gammaMeasure X F).map (imageRepresentative X)) (ν := imageLaw X))).toLp _

theorem imageGammaDiag_ae_eq (F : S.imageDom X) :
    ⇑(S.imageGammaDiag X F) =ᵐ[imageLaw X] fun x =>
      (((S.gammaMeasure X F).map (imageRepresentative X)).rnDeriv (imageLaw X) x).toReal :=
  MemLp.coeFn_toLp _

theorem imageGammaDiag_nonneg (F : S.imageDom X) :
    0 ≤ᵐ[imageLaw X] ⇑(S.imageGammaDiag X F) := by
  filter_upwards [S.imageGammaDiag_ae_eq X F] with x hx
  rw [hx]; exact ENNReal.toReal_nonneg

/-- The diagonal characterization, via RN and change of variables. -/
theorem imageGammaDiag_characterization (F : S.imageDom X) (H : ImageTest (Fin m → ℝ)) :
    H.integral (S.imageGammaDiag X F) =
      (H.comp (imageRepresentative X) (measurable_imageRepresentative X)).integral
        (S.Γ (S.imageLift X F) (S.imageLift X F)) := by
  change (∫ x, H x * S.imageGammaDiag X F x ∂imageLaw X) = _
  calc
    _ = ∫ x, (((S.gammaMeasure X F).map (imageRepresentative X)).rnDeriv
        (imageLaw X) x).toReal * H x ∂imageLaw X := by
      apply integral_congr_ae
      filter_upwards [S.imageGammaDiag_ae_eq X F] with x hx
      rw [hx, mul_comm]
    _ = ∫ x, H x ∂(S.gammaMeasure X F).map (imageRepresentative X) :=
      integral_toReal_rnDeriv_mul (S.gammaMeasure_map_ac X F)
    _ = ∫ ω, H (imageRepresentative X ω) ∂S.gammaMeasure X F :=
      integral_map_of_stronglyMeasurable (measurable_imageRepresentative X)
        H.measurable.stronglyMeasurable
    _ = ∫ ω, (ENNReal.ofReal (S.Γ (S.imageLift X F) (S.imageLift X F) ω)).toReal *
        H (imageRepresentative X ω) ∂μ :=
      integral_withDensity_eq_integral_toReal_smul₀
        (Lp.aestronglyMeasurable _).aemeasurable.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [S.Γ_nonneg (S.imageLift X F)] with ω hω
      rw [ENNReal.toReal_ofReal hω, mul_comm]
      rfl

/-- polarization of the positive diagonal. -/
def imageGamma (F G : S.imageDom X) : Lp ℝ 1 (imageLaw X) :=
  (1 / 4 : ℝ) • (S.imageGammaDiag X (F + G) - S.imageGammaDiag X (F - G))

/-- mixed characterization against every bounded measurable test. -/
theorem imageGamma_characterization (F G : S.imageDom X) (H : ImageTest (Fin m → ℝ)) :
    H.integral (S.imageGamma X F G) =
      (H.comp (imageRepresentative X) (measurable_imageRepresentative X)).integral
        (S.Γ (S.imageLift X F) (S.imageLift X G)) := by
  simp only [imageGamma, map_smul, map_sub, S.imageGammaDiag_characterization,
    map_add, LinearMap.add_apply, LinearMap.sub_apply, S.Γ_symm (S.imageLift X G), smul_eq_mul]
  ring

/-- The mixed characterization determines the image class uniquely. -/
theorem imageGamma_unique (F G : S.imageDom X) (g : Lp ℝ 1 (imageLaw X))
    (h : ∀ H : ImageTest (Fin m → ℝ), H.integral g =
      (H.comp (imageRepresentative X) (measurable_imageRepresentative X)).integral
        (S.Γ (S.imageLift X F) (S.imageLift X G))) : g = S.imageGamma X F G := by
  apply ImageTest.eq_of_integral_eq
  intro H
  rw [h H, S.imageGamma_characterization]

/-- polarization recovers the RN diagonal. -/
theorem imageGamma_self (F : S.imageDom X) : S.imageGamma X F F = S.imageGammaDiag X F := by
  apply ImageTest.eq_of_integral_eq
  intro H
  rw [S.imageGamma_characterization, S.imageGammaDiag_characterization]

theorem imageGamma_symm (F G : S.imageDom X) : S.imageGamma X F G = S.imageGamma X G F := by
  apply ImageTest.eq_of_integral_eq
  intro H
  rw [S.imageGamma_characterization, S.imageGamma_characterization, S.Γ_symm]

theorem imageGamma_add_left (F G K : S.imageDom X) :
    S.imageGamma X (F + G) K = S.imageGamma X F K + S.imageGamma X G K := by
  apply ImageTest.eq_of_integral_eq
  intro H
  simp only [map_add, S.imageGamma_characterization, LinearMap.add_apply]

theorem imageGamma_smul_left (c : ℝ) (F G : S.imageDom X) :
    S.imageGamma X (c • F) G = c • S.imageGamma X F G := by
  apply ImageTest.eq_of_integral_eq
  intro H
  simp only [map_smul, S.imageGamma_characterization, LinearMap.smul_apply]

/-- The symmetric bilinear image carré du champ. -/
def imageGammaBilinear : S.imageDom X →ₗ[ℝ] S.imageDom X →ₗ[ℝ] Lp ℝ 1 (imageLaw X) where
  toFun F :=
    { toFun := S.imageGamma X F
      map_add' G K := by
        rw [S.imageGamma_symm X F, S.imageGamma_add_left, S.imageGamma_symm X G,
          S.imageGamma_symm X K]
      map_smul' c G := by
        change S.imageGamma X F (c • G) = c • S.imageGamma X F G
        rw [S.imageGamma_symm X F, S.imageGamma_smul_left, S.imageGamma_symm X G] }
  map_add' F G := by ext K : 1; exact S.imageGamma_add_left X F G K
  map_smul' c F := by ext G : 1; exact S.imageGamma_smul_left X c F G

end ErrorCalculus.ErrorData
