import ErrorCalculus.Dirichlet.ErrorStructure
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ContDiff ENNReal
set_option linter.unusedSectionVars false
namespace ErrorCalculus
variable {d : ℕ}

/-- a strictly positive C¹ density; normalization is a separate instance. -/
class SmoothDensityD (ρ : (Fin d → ℝ) → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 ρ
  pos : ∀ x, 0 < ρ x

def densityMeasureD (ρ : (Fin d → ℝ) → ℝ) : Measure (Fin d → ℝ) :=
  volume.withDensity (fun x => ENNReal.ofReal (ρ x))

variable {ρ : (Fin d → ℝ) → ℝ}

theorem volume_absolutelyContinuous_densityD [SmoothDensityD ρ] :
    volume ≪ densityMeasureD ρ :=
  withDensity_absolutelyContinuous'
    (SmoothDensityD.contDiff (ρ := ρ)).continuous.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (SmoothDensityD.pos x)).ne')

instance densityMeasure_openPosD [SmoothDensityD ρ] : IsOpenPosMeasure (densityMeasureD ρ) :=
  volume_absolutelyContinuous_densityD.isOpenPosMeasure

/-- The bounded C¹ functions with bounded first derivative. -/
def IsC1BoundedD (g : (Fin d → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 1 g ∧ (∃ C, ∀ x, ‖g x‖ ≤ C) ∧ (∃ C, ∀ x, ‖fderiv ℝ g x‖ ≤ C)

namespace IsC1BoundedD
variable {g h : (Fin d → ℝ) → ℝ}

theorem differentiable (hg : IsC1BoundedD g) : Differentiable ℝ g :=
  hg.1.differentiable (by norm_num)

theorem continuous_fderiv (hg : IsC1BoundedD g) : Continuous (fderiv ℝ g) :=
  hg.1.continuous_fderiv (by norm_num)

theorem const (c : ℝ) : IsC1BoundedD (d := d) (fun _ => c) := by
  refine ⟨contDiff_const, ⟨‖c‖, fun _ => le_rfl⟩, ⟨0, ?_⟩⟩
  simp

theorem add (hg : IsC1BoundedD g) (hh : IsC1BoundedD h) : IsC1BoundedD (g + h) := by
  obtain ⟨C, hC⟩ := hg.2.1
  obtain ⟨D, hD⟩ := hh.2.1
  obtain ⟨C', hC'⟩ := hg.2.2
  obtain ⟨D', hD'⟩ := hh.2.2
  refine ⟨hg.1.add hh.1, ⟨C + D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩,
    ⟨C' + D', fun x => ?_⟩⟩
  rw [fderiv_add (hg.differentiable x) (hh.differentiable x)]
  exact (norm_add_le _ _).trans (add_le_add (hC' x) (hD' x))

theorem smul (hg : IsC1BoundedD g) (c : ℝ) : IsC1BoundedD (c • g) := by
  obtain ⟨C, hC⟩ := hg.2.1
  obtain ⟨D, hD⟩ := hg.2.2
  refine ⟨contDiff_const.smul hg.1, ⟨‖c‖ * C, fun x => ?_⟩, ⟨‖c‖ * D, fun x => ?_⟩⟩
  · exact (norm_smul c (g x)).le.trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c))
  · rw [fderiv_const_smul (hg.differentiable x) c, norm_smul]
    exact mul_le_mul_of_nonneg_left (hD x) (norm_nonneg c)

theorem memLp (hg : IsC1BoundedD g) (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp g p μ := by
  obtain ⟨C, hC⟩ := hg.2.1
  exact MemLp.of_bound hg.1.continuous.aestronglyMeasurable C (Eventually.of_forall hC)

theorem partial_memLp (hg : IsC1BoundedD g) (i : Fin d)
    (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (fun x => fderiv ℝ g x (Pi.single i 1)) p μ := by
  obtain ⟨C, hC⟩ := hg.2.2
  apply MemLp.of_bound (hg.continuous_fderiv.clm_apply continuous_const).aestronglyMeasurable C
  filter_upwards [] with x
  calc
    _ ≤ ‖fderiv ℝ g x‖ := by simpa only [Pi.norm_single, norm_one, mul_one] using (ContinuousLinearMap.le_opNorm (fderiv ℝ g x) (Pi.single i 1))
    _ ≤ C := hC x
end IsC1BoundedD

variable (ρ) [IsProbabilityMeasure (densityMeasureD ρ)]

/-- The actual subspace of L² classes having a bounded C¹ representative. -/
def protoDomD : Submodule ℝ (Lp ℝ 2 (densityMeasureD ρ)) where
  carrier := {u | ∃ g, IsC1BoundedD g ∧ ⇑u =ᵐ[densityMeasureD ρ] g}
  zero_mem' := ⟨fun _ => 0, IsC1BoundedD.const 0, Lp.coeFn_zero _ _ _⟩
  add_mem' := by
    rintro u v ⟨g, hg, hu⟩ ⟨h, hh, hv⟩
    exact ⟨g + h, hg.add hh, (Lp.coeFn_add u v).trans (hu.add hv)⟩
  smul_mem' := by
    rintro c u ⟨g, hg, hu⟩
    exact ⟨c • g, hg.smul c, (Lp.coeFn_smul c u).trans (hu.fun_comp (c • ·))⟩

/-- Choice is harmless because continuous representatives are unique. -/
def repD (u : protoDomD ρ) : (Fin d → ℝ) → ℝ := Classical.choose u.property

theorem rep_isC1BoundedD (u : protoDomD ρ) : IsC1BoundedD (repD ρ u) :=
  (Classical.choose_spec u.property).1

theorem coeFn_repD (u : protoDomD ρ) : ⇑(u : Lp ℝ 2 (densityMeasureD ρ)) =ᵐ[densityMeasureD ρ] repD ρ u :=
  (Classical.choose_spec u.property).2

variable [SmoothDensityD ρ]

theorem rep_uniqueD (u : protoDomD ρ) {g : (Fin d → ℝ) → ℝ} (hg : Continuous g)
    (he : ⇑(u : Lp ℝ 2 (densityMeasureD ρ)) =ᵐ[densityMeasureD ρ] g) : repD ρ u = g :=
  ((rep_isC1BoundedD ρ u).1.continuous.ae_eq_iff_eq (densityMeasureD ρ) hg).mp ((coeFn_repD ρ u).symm.trans he)

theorem rep_addD (u v : protoDomD ρ) : repD ρ (u + v) = repD ρ u + repD ρ v := by
  apply rep_uniqueD ρ _ ((rep_isC1BoundedD ρ u).1.continuous.add (rep_isC1BoundedD ρ v).1.continuous)
  exact (Lp.coeFn_add _ _).trans ((coeFn_repD ρ u).add (coeFn_repD ρ v))

theorem rep_smulD (c : ℝ) (u : protoDomD ρ) : repD ρ (c • u) = c • repD ρ u := by
  apply rep_uniqueD ρ _ (continuous_const.smul (rep_isC1BoundedD ρ u).1.continuous)
  exact (Lp.coeFn_smul _ _).trans ((coeFn_repD ρ u).fun_comp (c • ·))

/-- Coordinate derivative, with values in ordinary functions. -/
def partialRep (i : Fin d) : protoDomD ρ →ₗ[ℝ] ((Fin d → ℝ) → ℝ) where
  toFun u x := fderiv ℝ (repD ρ u) x (Pi.single i 1)
  map_add' u v := by
    rw [rep_addD]; funext x
    simp [fderiv_add ((rep_isC1BoundedD ρ u).differentiable x)
      ((rep_isC1BoundedD ρ v).differentiable x)]
  map_smul' c u := by
    rw [rep_smulD]; funext x
    simp [fderiv_const_smul ((rep_isC1BoundedD ρ u).differentiable x) c]

/-- A coordinate of the gradient as an L² class. -/
def gradD (i : Fin d) : protoDomD ρ →ₗ[ℝ] Lp ℝ 2 (densityMeasureD ρ) where
  toFun u := ((rep_isC1BoundedD ρ u).partial_memLp i (densityMeasureD ρ) 2).toLp (fun x => fderiv ℝ (repD ρ u) x (Pi.single i 1))
  map_add' u v := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((rep_isC1BoundedD ρ (u+v)).partial_memLp i (densityMeasureD ρ) 2),
      MemLp.coeFn_toLp ((rep_isC1BoundedD ρ u).partial_memLp i (densityMeasureD ρ) 2),
      MemLp.coeFn_toLp ((rep_isC1BoundedD ρ v).partial_memLp i (densityMeasureD ρ) 2), Lp.coeFn_add
        (((rep_isC1BoundedD ρ u).partial_memLp i (densityMeasureD ρ) 2).toLp _)
        (((rep_isC1BoundedD ρ v).partial_memLp i (densityMeasureD ρ) 2).toLp _)] with x ha hb hc hd
    simp only [Pi.add_apply] at hd
    rw [hd, ha, hb, hc]
    exact congrFun (map_add (partialRep ρ i) u v) x
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((rep_isC1BoundedD ρ (c • u)).partial_memLp i (densityMeasureD ρ) 2),
      MemLp.coeFn_toLp ((rep_isC1BoundedD ρ u).partial_memLp i (densityMeasureD ρ) 2),
      Lp.coeFn_smul c (((rep_isC1BoundedD ρ u).partial_memLp i (densityMeasureD ρ) 2).toLp _)] with x ha hb hc
    simp only [RingHom.id_apply, Pi.smul_apply] at hc ⊢
    rw [hc, ha, hb]
    exact congrFun (map_smul (partialRep ρ i) c u) x

theorem coeFn_gradD (i : Fin d) (u : protoDomD ρ) :
    ⇑(gradD ρ i u) =ᵐ[densityMeasureD ρ] partialRep ρ i u :=
  ((rep_isC1BoundedD ρ u).partial_memLp i (densityMeasureD ρ) 2).coeFn_toLp

end ErrorCalculus
