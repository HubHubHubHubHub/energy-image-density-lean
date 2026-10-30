import ErrorCalculus.Dirichlet.ErrorStructure

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The tuple of the chosen L² representatives. -/
def imageTuple {m : ℕ} (X : Fin m → Lp ℝ 2 μ) : Ω → (Fin m → ℝ) :=
  fun ω i => X i ω

theorem imageTuple_aemeasurable {m : ℕ} (X : Fin m → Lp ℝ 2 μ) :
    AEMeasurable (imageTuple X) μ :=
  (MemLp.of_eval (fun i => Lp.memLp (X i))).aestronglyMeasurable.aemeasurable

/-- a genuinely measurable representative, on an arbitrary source space. -/
def imageRepresentative {m : ℕ} (X : Fin m → Lp ℝ 2 μ) : Ω → (Fin m → ℝ) :=
  (imageTuple_aemeasurable X).mk (imageTuple X)

theorem measurable_imageRepresentative {m : ℕ} (X : Fin m → Lp ℝ 2 μ) :
    Measurable (imageRepresentative X) := (imageTuple_aemeasurable X).measurable_mk

theorem imageRepresentative_ae_eq {m : ℕ} (X : Fin m → Lp ℝ 2 μ) :
    imageRepresentative X =ᵐ[μ] imageTuple X := (imageTuple_aemeasurable X).ae_eq_mk.symm

/-- The image probability law. -/
def imageLaw {m : ℕ} (X : Fin m → Lp ℝ 2 μ) : Measure (Fin m → ℝ) :=
  μ.map (imageRepresentative X)

instance imageLaw_probability [IsProbabilityMeasure μ] {m : ℕ} (X : Fin m → Lp ℝ 2 μ) :
    IsProbabilityMeasure (imageLaw X) :=
  Measure.isProbabilityMeasure_map (measurable_imageRepresentative X).aemeasurable

theorem imageRepresentative_preserving {m : ℕ} (X : Fin m → Lp ℝ 2 μ) :
    MeasurePreserving (imageRepresentative X) μ (imageLaw X) :=
  ⟨measurable_imageRepresentative X, rfl⟩

/-- isometric linear pullback between the two L² spaces. -/
def pullback {m : ℕ} (X : Fin m → Lp ℝ 2 μ) :
    Lp ℝ 2 (imageLaw X) →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (imageRepresentative_preserving X)

theorem pullback_ae_eq {m : ℕ} (X : Fin m → Lp ℝ 2 μ) (F : Lp ℝ 2 (imageLaw X)) :
    ⇑(pullback X F) =ᵐ[μ] fun ω => F (imageRepresentative X ω) :=
  Lp.coeFn_compMeasurePreserving F (imageRepresentative_preserving X)

namespace ErrorData
variable [IsProbabilityMeasure μ]
variable (S : ErrorData Ω μ) {m : ℕ} (X : Fin m → Lp ℝ 2 μ)

/-- The full inverse-image domain. -/
def imageDom : Submodule ℝ (Lp ℝ 2 (imageLaw X)) := S.dom.comap (pullback X).toLinearMap

/-- Pullback restricted to the image domain. -/
def imageLift : S.imageDom X →ₗ[ℝ] S.dom :=
  { toFun := fun F => ⟨pullback X F, F.property⟩
    map_add' := by intro F G; apply Subtype.ext; exact map_add (pullback X) (F : Lp ℝ 2 (imageLaw X)) (G : Lp ℝ 2 (imageLaw X))
    map_smul' := by intro c F; apply Subtype.ext; exact map_smul (pullback X) c (F : Lp ℝ 2 (imageLaw X)) }

@[simp] theorem imageLift_coe (F : S.imageDom X) :
    (S.imageLift X F : Lp ℝ 2 μ) = pullback X F := rfl

end ErrorData
end ErrorCalculus
