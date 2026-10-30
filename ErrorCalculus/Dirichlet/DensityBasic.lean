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

/-- a strictly positive C¹ density; normalization is a separate instance. -/
class SmoothDensity (ρ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 ρ
  pos : ∀ x, 0 < ρ x

def densityMeasure (ρ : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (ρ x))

variable {ρ : ℝ → ℝ}

theorem volume_absolutelyContinuous_density [SmoothDensity ρ] :
    volume ≪ densityMeasure ρ :=
  withDensity_absolutelyContinuous'
    (SmoothDensity.contDiff (ρ := ρ)).continuous.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (SmoothDensity.pos x)).ne')

instance densityMeasure_openPos [SmoothDensity ρ] : IsOpenPosMeasure (densityMeasure ρ) :=
  volume_absolutelyContinuous_density.isOpenPosMeasure

/-- The bounded C¹ functions with bounded first derivative. -/
def IsC1Bounded (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 g ∧ (∃ C, ∀ x, ‖g x‖ ≤ C) ∧ (∃ C, ∀ x, ‖deriv g x‖ ≤ C)

namespace IsC1Bounded
variable {g h : ℝ → ℝ}

theorem differentiable (hg : IsC1Bounded g) : Differentiable ℝ g :=
  hg.1.differentiable (by norm_num)

theorem continuous_deriv (hg : IsC1Bounded g) : Continuous (deriv g) :=
  hg.1.continuous_deriv (by norm_num)

theorem const (c : ℝ) : IsC1Bounded (fun _ => c) := by
  refine ⟨contDiff_const, ⟨‖c‖, fun _ => le_rfl⟩, ⟨0, ?_⟩⟩
  simp

theorem add (hg : IsC1Bounded g) (hh : IsC1Bounded h) : IsC1Bounded (g + h) := by
  obtain ⟨C, hC⟩ := hg.2.1
  obtain ⟨D, hD⟩ := hh.2.1
  obtain ⟨C', hC'⟩ := hg.2.2
  obtain ⟨D', hD'⟩ := hh.2.2
  refine ⟨hg.1.add hh.1, ⟨C + D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩,
    ⟨C' + D', fun x => ?_⟩⟩
  rw [deriv_add (hg.differentiable x) (hh.differentiable x)]
  exact (norm_add_le _ _).trans (add_le_add (hC' x) (hD' x))

theorem smul (hg : IsC1Bounded g) (c : ℝ) : IsC1Bounded (c • g) := by
  obtain ⟨C, hC⟩ := hg.2.1
  obtain ⟨D, hD⟩ := hg.2.2
  refine ⟨contDiff_const.smul hg.1, ⟨‖c‖ * C, fun x => ?_⟩, ⟨‖c‖ * D, fun x => ?_⟩⟩
  · exact (norm_smul c (g x)).le.trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c))
  · rw [deriv_const_smul c (hg.differentiable x), norm_smul]
    exact mul_le_mul_of_nonneg_left (hD x) (norm_nonneg c)

theorem memLp (hg : IsC1Bounded g) (μ : Measure ℝ) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp g p μ := by
  obtain ⟨C, hC⟩ := hg.2.1
  exact MemLp.of_bound hg.1.continuous.aestronglyMeasurable C (Eventually.of_forall hC)

theorem deriv_memLp (hg : IsC1Bounded g) (μ : Measure ℝ) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (deriv g) p μ := by
  obtain ⟨C, hC⟩ := hg.2.2
  exact MemLp.of_bound hg.continuous_deriv.aestronglyMeasurable C (Eventually.of_forall hC)
end IsC1Bounded

variable (ρ) [IsProbabilityMeasure (densityMeasure ρ)]

/-- The actual subspace of L² classes having a bounded C¹ representative. -/
def protoDom : Submodule ℝ (Lp ℝ 2 (densityMeasure ρ)) where
  carrier := {u | ∃ g, IsC1Bounded g ∧ ⇑u =ᵐ[densityMeasure ρ] g}
  zero_mem' := ⟨fun _ => 0, IsC1Bounded.const 0, Lp.coeFn_zero _ _ _⟩
  add_mem' := by
    rintro u v ⟨g, hg, hu⟩ ⟨h, hh, hv⟩
    exact ⟨g + h, hg.add hh, (Lp.coeFn_add u v).trans (hu.add hv)⟩
  smul_mem' := by
    rintro c u ⟨g, hg, hu⟩
    exact ⟨c • g, hg.smul c, (Lp.coeFn_smul c u).trans (hu.fun_comp (c • ·))⟩

/-- Choice is harmless because continuous representatives are unique. -/
def rep (u : protoDom ρ) : ℝ → ℝ := Classical.choose u.property

theorem rep_isC1Bounded (u : protoDom ρ) : IsC1Bounded (rep ρ u) :=
  (Classical.choose_spec u.property).1

theorem coeFn_rep (u : protoDom ρ) : ⇑(u : Lp ℝ 2 (densityMeasure ρ)) =ᵐ[densityMeasure ρ] rep ρ u :=
  (Classical.choose_spec u.property).2

variable [SmoothDensity ρ]

theorem rep_unique (u : protoDom ρ) {g : ℝ → ℝ} (hg : Continuous g)
    (he : ⇑(u : Lp ℝ 2 (densityMeasure ρ)) =ᵐ[densityMeasure ρ] g) : rep ρ u = g :=
  ((rep_isC1Bounded ρ u).1.continuous.ae_eq_iff_eq (densityMeasure ρ) hg).mp ((coeFn_rep ρ u).symm.trans he)

theorem rep_add (u v : protoDom ρ) : rep ρ (u + v) = rep ρ u + rep ρ v := by
  apply rep_unique ρ _ ((rep_isC1Bounded ρ u).1.continuous.add (rep_isC1Bounded ρ v).1.continuous)
  exact (Lp.coeFn_add _ _).trans ((coeFn_rep ρ u).add (coeFn_rep ρ v))

theorem rep_smul (c : ℝ) (u : protoDom ρ) : rep ρ (c • u) = c • rep ρ u := by
  apply rep_unique ρ _ (continuous_const.smul (rep_isC1Bounded ρ u).1.continuous)
  exact (Lp.coeFn_smul _ _).trans ((coeFn_rep ρ u).fun_comp (c • ·))

/-- Derivative evaluation, with values in ordinary functions. -/
def derivRep : protoDom ρ →ₗ[ℝ] (ℝ → ℝ) where
  toFun u := deriv (rep ρ u)
  map_add' u v := by
    rw [rep_add]; funext x
    exact deriv_add ((rep_isC1Bounded ρ u).differentiable x) ((rep_isC1Bounded ρ v).differentiable x)
  map_smul' c u := by
    rw [rep_smul]; funext x
    exact deriv_const_smul c ((rep_isC1Bounded ρ u).differentiable x)

/-- Gradient as an L² class. -/
def grad : protoDom ρ →ₗ[ℝ] Lp ℝ 2 (densityMeasure ρ) where
  toFun u := ((rep_isC1Bounded ρ u).deriv_memLp (densityMeasure ρ) 2).toLp (deriv (rep ρ u))
  map_add' u v := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((rep_isC1Bounded ρ (u+v)).deriv_memLp (densityMeasure ρ) 2),
      MemLp.coeFn_toLp ((rep_isC1Bounded ρ u).deriv_memLp (densityMeasure ρ) 2),
      MemLp.coeFn_toLp ((rep_isC1Bounded ρ v).deriv_memLp (densityMeasure ρ) 2), Lp.coeFn_add
        (((rep_isC1Bounded ρ u).deriv_memLp (densityMeasure ρ) 2).toLp _) (((rep_isC1Bounded ρ v).deriv_memLp (densityMeasure ρ) 2).toLp _)] with x ha hb hc hd
    simp only [Pi.add_apply] at hd
    rw [hd, ha, hb, hc]
    exact congrFun (map_add (derivRep ρ) u v) x
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((rep_isC1Bounded ρ (c • u)).deriv_memLp (densityMeasure ρ) 2),
      MemLp.coeFn_toLp ((rep_isC1Bounded ρ u).deriv_memLp (densityMeasure ρ) 2),
      Lp.coeFn_smul c (((rep_isC1Bounded ρ u).deriv_memLp (densityMeasure ρ) 2).toLp _)] with x ha hb hc
    simp only [RingHom.id_apply, Pi.smul_apply] at hc ⊢
    rw [hc, ha, hb]
    exact congrFun (map_smul (derivRep ρ) c u) x

theorem coeFn_grad (u : protoDom ρ) : ⇑(grad ρ u) =ᵐ[densityMeasure ρ] deriv (rep ρ u) :=
  ((rep_isC1Bounded ρ u).deriv_memLp (densityMeasure ρ) 2).coeFn_toLp

end ErrorCalculus
