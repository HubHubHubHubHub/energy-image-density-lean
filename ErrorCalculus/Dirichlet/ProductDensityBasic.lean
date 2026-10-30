import ErrorCalculus.Dirichlet.DensityDStructure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.MetricSpace.Isometry

noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace ErrorCalculus
variable {d₁ d₂ : ℕ}

/-- First coordinate block, with the finite-dimensional sup norm. -/
def prodProj₁ (d₁ d₂ : ℕ) : (Fin (d₁ + d₂) → ℝ) →L[ℝ] (Fin d₁ → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.castAdd d₂ j)

/-- Second coordinate block. -/
def prodProj₂ (d₁ d₂ : ℕ) : (Fin (d₁ + d₂) → ℝ) →L[ℝ] (Fin d₂ → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.natAdd d₁ j)

@[simp] theorem prodProj₁_apply (z : Fin (d₁ + d₂) → ℝ) (j : Fin d₁) :
    prodProj₁ d₁ d₂ z j = z (Fin.castAdd d₂ j) := rfl
@[simp] theorem prodProj₂_apply (z : Fin (d₁ + d₂) → ℝ) (j : Fin d₂) :
    prodProj₂ d₁ d₂ z j = z (Fin.natAdd d₁ j) := rfl

theorem prodProj₁_norm_le (z : Fin (d₁ + d₂) → ℝ) : ‖prodProj₁ d₁ d₂ z‖ ≤ ‖z‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun _ => norm_le_pi_norm z _
theorem prodProj₂_norm_le (z : Fin (d₁ + d₂) → ℝ) : ‖prodProj₂ d₁ d₂ z‖ ≤ ‖z‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun _ => norm_le_pi_norm z _

/-- Concatenation, expressed through the two canonical measurable equivalences. -/
def appendEquivM (d₁ d₂ : ℕ) :
    ((Fin d₁ → ℝ) × (Fin d₂ → ℝ)) ≃ᵐ (Fin (d₁ + d₂) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin d₁ ⊕ Fin d₂ => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (d₁ + d₂) => ℝ) finSumFinEquiv)

@[simp] theorem appendEquivM_apply (x : Fin d₁ → ℝ) (y : Fin d₂ → ℝ) :
    appendEquivM d₁ d₂ (x, y) = Fin.append x y := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [appendEquivM, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] <;> rfl

@[simp] theorem prodProj₁_append (x : Fin d₁ → ℝ) (y : Fin d₂ → ℝ) :
    prodProj₁ d₁ d₂ (Fin.append x y) = x := by ext j; simp
@[simp] theorem prodProj₂_append (x : Fin d₁ → ℝ) (y : Fin d₂ → ℝ) :
    prodProj₂ d₁ d₂ (Fin.append x y) = y := by ext j; simp

/-- The measurable equivalence has exactly Fin.appendEquiv as underlying equivalence. -/
theorem appendEquivM_toEquiv (d₁ d₂ : ℕ) :
    (appendEquivM d₁ d₂).toEquiv = Fin.appendEquiv d₁ d₂ := by
  apply Equiv.ext
  intro z
  exact appendEquivM_apply z.1 z.2

/-- Concatenation is also the canonical sup-norm isometry. -/
theorem appendEquivM_isometry (d₁ d₂ : ℕ) : Isometry (appendEquivM d₁ d₂) := by
  change Isometry (appendEquivM d₁ d₂).toEquiv
  rw [appendEquivM_toEquiv]
  exact (Fin.appendIsometry d₁ d₂).isometry

theorem prodProj₁_opNorm_le (d₁ d₂ : ℕ) : ‖prodProj₁ d₁ d₂‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by simpa using prodProj₁_norm_le z

theorem prodProj₂_opNorm_le (d₁ d₂ : ℕ) : ‖prodProj₂ d₁ d₂‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by simpa using prodProj₂_norm_le z

/-- Concatenation preserves Lebesgue volume, including empty coordinate blocks. -/
theorem appendEquivM_volume_preserving (d₁ d₂ : ℕ) :
    MeasurePreserving (appendEquivM d₁ d₂) (volume.prod volume) volume :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin (d₁ + d₂) => ℝ) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin d₁ ⊕ Fin d₂ => ℝ))

/-- The product density in concatenated coordinates. -/
def prodDensity (ρ₁ : (Fin d₁ → ℝ) → ℝ) (ρ₂ : (Fin d₂ → ℝ) → ℝ)
    (z : Fin (d₁ + d₂) → ℝ) : ℝ := ρ₁ (prodProj₁ d₁ d₂ z) * ρ₂ (prodProj₂ d₁ d₂ z)

/-- An elementary tensor of ordinary functions. -/
def tensorFun (g₁ : (Fin d₁ → ℝ) → ℝ) (g₂ : (Fin d₂ → ℝ) → ℝ) :
    (Fin (d₁ + d₂) → ℝ) → ℝ := prodDensity g₁ g₂

@[simp] theorem tensorFun_append (g₁ : (Fin d₁ → ℝ) → ℝ) (g₂ : (Fin d₂ → ℝ) → ℝ)
    (x : Fin d₁ → ℝ) (y : Fin d₂ → ℝ) : tensorFun g₁ g₂ (appendEquivM d₁ d₂ (x,y)) = g₁ x * g₂ y := by
  simp [tensorFun, prodDensity]

instance prodDensity_smooth (ρ₁ : (Fin d₁ → ℝ) → ℝ) (ρ₂ : (Fin d₂ → ℝ) → ℝ)
    [SmoothDensityD ρ₁] [SmoothDensityD ρ₂] : SmoothDensityD (prodDensity ρ₁ ρ₂) where
  contDiff := ((SmoothDensityD.contDiff (ρ := ρ₁)).comp (prodProj₁ d₁ d₂).contDiff).mul
    ((SmoothDensityD.contDiff (ρ := ρ₂)).comp (prodProj₂ d₁ d₂).contDiff)
  pos _ := mul_pos (SmoothDensityD.pos _) (SmoothDensityD.pos _)

/-- The first factor injects into ordinary tensors by g ↦ g ⊗ 1. -/
theorem tensorFun_one_injective (d₁ d₂ : ℕ) :
    Function.Injective (fun g : (Fin d₁ → ℝ) → ℝ => tensorFun g (fun _ : Fin d₂ → ℝ => 1)) := by
  intro g h he
  funext x
  have h := congrFun he (Fin.append x 0)
  simpa [tensorFun, prodDensity] using h

end ErrorCalculus
