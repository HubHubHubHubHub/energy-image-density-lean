import ErrorCalculus.Dirichlet.OrnsteinUhlenbeckDMeasure
import ErrorCalculus.Dirichlet.ProductDensityGamma
import Mathlib.Probability.ProductMeasure

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace ErrorCalculus

/-- The Gaussian coordinate model of Wiener space. -/
def wienerCoord : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance wienerCoord_probability : IsProbabilityMeasure wienerCoord :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)))

/-- Restriction to the first N coordinates, also for N = 0. -/
def restrictN (N : ℕ) (x : ℕ → ℝ) (i : Fin N) : ℝ := x i.val

theorem restrictN_measurable (N : ℕ) : Measurable (restrictN N) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply i.val

/-- The restriction law is exactly OU density measure. -/
theorem restrictN_preserving (N : ℕ) :
    MeasurePreserving (restrictN N) wienerCoord (densityMeasureD (ouDensityD N)) := by
  rw [ouDensityD_measure]
  let e : (Finset.range N) ≃ Fin N :=
    { toFun := fun i => ⟨i.val, Finset.mem_range.mp i.property⟩
      invFun := fun i => ⟨i.val, Finset.mem_range.mpr i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hr : MeasurePreserving (Finset.range N).restrict wienerCoord
      (Measure.pi (fun _ : Finset.range N => gaussianReal 0 1)) :=
    ⟨measurable_pi_lambda _ fun i => measurable_pi_apply i.val,
      Measure.infinitePi_map_restrict _⟩
  exact (measurePreserving_piCongrLeft (fun _ : Fin N => gaussianReal 0 1) e).comp hr

variable {N M K : ℕ}

/-- Contractive projection between finite levels. -/
def projLE (h : N ≤ M) : (Fin M → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castLE h i)

@[simp] theorem projLE_apply (h : N ≤ M) (x : Fin M → ℝ) (i : Fin N) :
    projLE h x i = x (Fin.castLE h i) := rfl

theorem projLE_norm_le (h : N ≤ M) (x : Fin M → ℝ) : ‖projLE h x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun _ => norm_le_pi_norm x _

theorem projLE_opNorm_le (h : N ≤ M) : ‖projLE h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simpa using projLE_norm_le h x

theorem restrictN_eq_projLE_comp (h : N ≤ M) :
    restrictN N = projLE h ∘ restrictN M := rfl

theorem projLE_preserving (h : N ≤ M) :
    MeasurePreserving (projLE h) (densityMeasureD (ouDensityD M))
      (densityMeasureD (ouDensityD N)) := by
  have hp := (restrictN_preserving N).map_of_comp (projLE h).continuous.measurable
    (restrictN_measurable M) (g := projLE h) (f := restrictN M)
  rwa [(restrictN_preserving M).map_eq] at hp

/-- Isometric cylinder pullback, used at exponents 1 and 2. -/
def cylLp (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp ℝ p (densityMeasureD (ouDensityD N)) →ₗᵢ[ℝ] Lp ℝ p wienerCoord :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (restrictN_preserving N)

/-- Isometric lift between finite levels. -/
def liftLp (h : N ≤ M) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp ℝ p (densityMeasureD (ouDensityD N)) →ₗᵢ[ℝ]
      Lp ℝ p (densityMeasureD (ouDensityD M)) :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (projLE_preserving h)

theorem coeFn_cylLp (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Lp ℝ p (densityMeasureD (ouDensityD N))) :
    ⇑(cylLp N p u) =ᵐ[wienerCoord] u ∘ restrictN N :=
  Lp.coeFn_compMeasurePreserving _ _

theorem coeFn_liftLp (h : N ≤ M) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Lp ℝ p (densityMeasureD (ouDensityD N))) :
    ⇑(liftLp h p u) =ᵐ[densityMeasureD (ouDensityD M)] u ∘ projLE h :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Pullback compatibility holds for all normed Lp exponents. -/
theorem cylLp_comp (h : N ≤ M) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Lp ℝ p (densityMeasureD (ouDensityD N))) :
    cylLp M p (liftLp h p u) = cylLp N p u :=
  (Lp.compMeasurePreserving_comp_apply u (projLE_preserving h) (restrictN_preserving M)).symm

theorem liftLp_comp (h : N ≤ M) (h' : M ≤ K) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Lp ℝ p (densityMeasureD (ouDensityD N))) :
    liftLp h' p (liftLp h p u) = liftLp (h.trans h') p u :=
  (Lp.compMeasurePreserving_comp_apply u (projLE_preserving h) (projLE_preserving h')).symm

theorem integral_cylLp (N : ℕ) (u : Lp ℝ 1 (densityMeasureD (ouDensityD N))) :
    (∫ x, cylLp N 1 u x ∂wienerCoord) = ∫ x, u x ∂densityMeasureD (ouDensityD N) := by
  rw [integral_congr_ae (coeFn_cylLp N 1 u)]
  have hu : AEStronglyMeasurable (⇑u) (wienerCoord.map (restrictN N)) := by
    rw [(restrictN_preserving N).map_eq]
    exact Lp.aestronglyMeasurable u
  exact ((integral_map (restrictN_measurable N).aemeasurable hu).symm).trans
    (by rw [(restrictN_preserving N).map_eq])

theorem cylLp_const (N : ℕ) (c : ℝ) :
    cylLp N 2 (Lp.const 2 (densityMeasureD (ouDensityD N)) c) = Lp.const 2 wienerCoord c := by
  apply Lp.ext
  exact (coeFn_cylLp N 2 _).trans (((restrictN_preserving N).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_const _ _ c)).trans (Lp.coeFn_const _ _ c).symm)

end ErrorCalculus
