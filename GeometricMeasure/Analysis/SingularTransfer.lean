import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Singular Transfer

## Main results
Transfer from a negligible singular set to a dominated measure (pure measure theory, Mathlib only).
DPR arXiv p. 15, proof of Theorem 1.10: “since clearly μˢ ≪ |T|ˢ”; proof of Corollary 1.12:
“assumption (ii) hence gives that μˢ = 0”. The chosen form avoids any Lebesgue decomposition of the
dominated measure ν: neither finiteness nor σ-finiteness of ν is required. Dimension zero: on
ℝ⁰, only the empty set is Lebesgue-null.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set

namespace GeometricMeasure

/--
DPR arXiv p. 15 (“μˢ ≪ |T|ˢ”, proofs of Theorem 1.10 and Corollary 1.12). Assuming μ has a Lebesgue
decomposition relative to ρ, if ν ≪ μ, a property p holds μˢ-almost everywhere, and p is false
ν-almost everywhere, then ν ≪ ρ. No finiteness assumption on ν.
-/
theorem absolutelyContinuous_of_ae_singularPart {X : Type*} [MeasurableSpace X]
    {μ ν ρ : Measure X} [μ.HaveLebesgueDecomposition ρ] {p : X → Prop}
    (hνμ : ν ≪ μ) (hsing : ∀ᵐ x ∂μ.singularPart ρ, p x) (hν : ∀ᵐ x ∂ν, ¬ p x) :
    ν ≪ ρ := by
  intro s hs
  have hA : μ.singularPart ρ {x | ¬ p x} = 0 := ae_iff.mp hsing
  have hB : ν {x | ¬ ¬ p x} = 0 := ae_iff.mp hν
  have hμ : μ (s ∩ {x | ¬ p x}) = 0 := by
    have hdec := Measure.haveLebesgueDecomposition_add μ ρ
    have h1 : μ.singularPart ρ (s ∩ {x | ¬ p x}) = 0 :=
      measure_mono_null inter_subset_right hA
    have h2 : (ρ.withDensity (μ.rnDeriv ρ)) (s ∩ {x | ¬ p x}) = 0 :=
      withDensity_absolutelyContinuous _ _ (measure_mono_null inter_subset_left hs)
    rw [hdec, Measure.add_apply, h1, h2, add_zero]
  have h3 : ν (s ∩ {x | ¬ p x}) = 0 := hνμ hμ
  refine measure_mono_null (t := (s ∩ {x | ¬ p x}) ∪ {x | ¬ ¬ p x}) ?_
    (measure_union_null h3 hB)
  intro x hx
  by_cases h : p x
  · exact Or.inr (not_not_intro h)
  · exact Or.inl ⟨hx, h⟩

/--
Case d = 0 of Corollary 1.12 (DPR arXiv p. 4): on the singleton ℝ⁰, every measure is absolutely
continuous with respect to volume (only ∅ is null).
-/
theorem absolutelyContinuous_volume_of_dimension_zero
    (ν : Measure (EuclideanSpace ℝ (Fin 0))) : ν ≪ volume := by
  intro s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact measure_empty
  · exfalso
    have huniv : s = univ := eq_univ_of_forall (fun y => Subsingleton.elim x y ▸ hx)
    rw [huniv] at hs
    exact (isOpen_univ.measure_ne_zero volume univ_nonempty) hs

end GeometricMeasure
