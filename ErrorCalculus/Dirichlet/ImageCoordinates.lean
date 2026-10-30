import ErrorCalculus.Dirichlet.ImageStructure

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {m : ℕ} (X : Fin m → Lp ℝ 2 μ)

/-- The i-th coordinate as an L² class for the image law. -/
def imageCoordinate (i : Fin m) : Lp ℝ 2 (imageLaw X) :=
  (imageFunction_memLp X (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).lipschitz).toLp _

theorem imageCoordinate_ae_eq (i : Fin m) :
    ⇑(imageCoordinate X i) =ᵐ[imageLaw X] fun x => x i := MemLp.coeFn_toLp _

/-- The coordinate class pulls back to the originally specified L² class. -/
theorem pullback_imageCoordinate (i : Fin m) : pullback X (imageCoordinate X i) = X i := by
  apply Lp.ext
  exact pullback_ofFunction X _ (imageCoordinate_ae_eq X i)

namespace ErrorStructure
variable (S : ErrorStructure Ω μ) (hX : ∀ i, X i ∈ S.dom)

theorem imageCoordinate_mem (i : Fin m) : imageCoordinate X i ∈ (S.image X hX).dom := by
  change pullback X (imageCoordinate X i) ∈ S.dom
  rw [pullback_imageCoordinate]
  exact hX i

/-- The canonical coordinate in the image error domain. -/
def imageCoord (i : Fin m) : (S.image X hX).dom :=
  ⟨imageCoordinate X i, S.imageCoordinate_mem X hX i⟩

@[simp] theorem imageLift_imageCoord (i : Fin m) :
    S.toErrorData.imageLift X (S.imageCoord X hX i) = ⟨X i, hX i⟩ := by
  apply Subtype.ext
  exact pullback_imageCoordinate X i

/-- The mean error covariance of the coordinates is preserved exactly. -/
theorem image_coordinate_variance (i j : Fin m) :
    (∫ x, (S.image X hX).Γ (S.imageCoord X hX i) (S.imageCoord X hX j) x ∂imageLaw X) =
      ∫ ω, S.Γ ⟨X i, hX i⟩ ⟨X j, hX j⟩ ω ∂μ := by
  have h := S.image_Γ_characterization X hX (S.imageCoord X hX i) (S.imageCoord X hX j)
    (fun _ => 1) measurable_const ⟨1, by simp⟩
  simpa only [one_mul, S.imageLift_imageCoord] using h

/-- scalar image calculus, without any extra assumption on the image law. -/
theorem image_scalar_variance (Y : Fin 1 → Lp ℝ 2 μ) (hY : ∀ i, Y i ∈ S.dom)
    {F : ℝ → ℝ} {L : ℝ≥0} (hC : ContDiff ℝ 1 F) (hL : LipschitzWith L F)
    (w : Lp ℝ 2 (imageLaw Y)) (hw : ⇑w =ᵐ[imageLaw Y] fun x => F (x 0)) :
    ∃ hd : w ∈ (S.image Y hY).dom,
      ⇑((S.image Y hY).Γ ⟨w, hd⟩ ⟨w, hd⟩) =ᵐ[imageLaw Y] fun x =>
        (deriv F (x 0))^2 * (S.image Y hY).Γ (S.imageCoord Y hY 0) (S.imageCoord Y hY 0) x := by
  let p : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hd : w ∈ (S.image Y hY).dom :=
    S.imageDom_of_contDiff_lipschitz Y hY (hC.comp p.contDiff) (hL.comp p.lipschitz) w hw
  have hcomp : ⇑w =ᵐ[imageLaw Y] fun x => F ((S.imageCoord Y hY 0 : Lp ℝ 2 (imageLaw Y)) x) := by
    filter_upwards [hw, imageCoordinate_ae_eq Y 0] with x hx hp
    change w x = F (imageCoordinate Y 0 x)
    rw [hx, hp]
  refine ⟨hd, ?_⟩
  have he := (S.image Y hY).chain_diagonal hC hL (S.imageCoord Y hY 0) ⟨w, hd⟩ hcomp
  filter_upwards [he, imageCoordinate_ae_eq Y 0] with x hx hp
  change _ = (deriv F (imageCoordinate Y 0 x))^2 * _ at hx
  rwa [hp] at hx

end ErrorStructure
end ErrorCalculus
