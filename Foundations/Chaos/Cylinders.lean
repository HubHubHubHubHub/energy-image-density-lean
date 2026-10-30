import Foundations.HermiteD.Basis
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure

noncomputable section
open MeasureTheory Filter Topology Set
open scoped InnerProductSpace
namespace Foundations

abbrev gaussianInf : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => standardGaussian)

theorem measurable_gaussianRestrict (s : Finset ℕ) : Measurable ((s.restrict : (ℕ → ℝ) → (s → ℝ))) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ℕ))

theorem gaussianInf_restrict_preserving (s : Finset ℕ) :
    MeasurePreserving s.restrict gaussianInf (gaussianProduct s) :=
  ⟨measurable_gaussianRestrict s, Measure.infinitePi_map_restrict _⟩

/-- Isometric inclusion of the L² functions of finitely many coordinates. -/
def gaussianCylinderLp (s : Finset ℕ) :
    Lp ℝ 2 (gaussianProduct s) →ₗᵢ[ℝ] Lp ℝ 2 gaussianInf :=
  Lp.compMeasurePreservingₗᵢ ℝ s.restrict (gaussianInf_restrict_preserving s)

theorem coe_gaussianCylinderLp (s : Finset ℕ) (f : Lp ℝ 2 (gaussianProduct s)) :
    gaussianCylinderLp s f =ᵐ[gaussianInf] fun x => f (s.restrict x) :=
  Lp.coeFn_compMeasurePreserving f (gaussianInf_restrict_preserving s)

theorem gaussianCylinderLp_indicator (s : Finset ℕ) {t : Set (s → ℝ)}
    (ht : MeasurableSet t) (c : ℝ) :
    gaussianCylinderLp s (indicatorConstLp 2 ht (measure_ne_top _ _) c) =
      indicatorConstLp 2 (ht.preimage (measurable_gaussianRestrict s)) (measure_ne_top _ _) c := by
  exact Lp.indicatorConstLp_compMeasurePreserving ht (measure_ne_top _ _) c
    (gaussianInf_restrict_preserving s)

theorem gaussian_measurableCylinders_measureDense :
    gaussianInf.MeasureDense (measurableCylinders (fun _ : ℕ => ℝ)) :=
  Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite gaussianInf
    ⟨empty_mem_measurableCylinders _, fun {_} hs => compl_mem_measurableCylinders hs,
      fun {_ _} hs ht => union_mem_measurableCylinders hs ht⟩ generateFrom_measurableCylinders.symm

/-- The generating cylinder algebra is dense in L², via indicators and Bochner simple functions. -/
theorem gaussianCylinder_closed_submodule_eq_top (S : Submodule ℝ (Lp ℝ 2 gaussianInf))
    (hS : IsClosed (S : Set (Lp ℝ 2 gaussianInf)))
    (hcyl : ∀ (s : Finset ℕ) (u : Lp ℝ 2 (gaussianProduct s)), gaussianCylinderLp s u ∈ S) : S = ⊤ := by
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hind (c : ℝ) {s : Set (ℕ → ℝ)} (hs : MeasurableSet s) :
      indicatorConstLp 2 hs (measure_ne_top _ _) c ∈ S := by
    have hmem := gaussian_measurableCylinders_measureDense.indicatorConstLp_subset_closure
      (p := 2) c ⟨s, hs, measure_ne_top _ _, rfl⟩
    apply (closure_minimal (t := (S : Set (Lp ℝ 2 gaussianInf))) ?_ hS) hmem
    rintro _ ⟨t, ht, hμt, rfl⟩
    obtain ⟨I, a, ha, rfl⟩ := (mem_measurableCylinders t).mp ht
    have hi := hcyl I (indicatorConstLp 2 ha (measure_ne_top _ _) c)
    rw [gaussianCylinderLp_indicator] at hi
    exact hi
  apply top_unique
  intro f _
  apply Lp.induction (p := 2) (by norm_num) (fun f : Lp ℝ 2 gaussianInf => f ∈ S)
    (fun c s hs _ => ?_) (fun _ _ _ _ _ hf hg => S.add_mem hf hg) hS f
  exact hind c hs

end Foundations
