import ErrorCalculus.Dirichlet.PolarCurrent

noncomputable section
open MeasureTheory
namespace ErrorCalculus

/--
De Philippis–Rindler, Annals of Mathematics (2016), Corollary
1.12, in the finite polar one-current formulation of Eriksson-Bique–Murugan,
arXiv:2510.13659, Theorem 1.8. This is a named hypothesis, not an axiom
and not a theorem proved in this library. Any application must supply it.
-/
def DePhilippisRindler (n : ℕ) : Prop :=
  ∀ T : Fin n → PolarCurrent n, (∀ i, (T i).IsNormal) →
    ∀ ν : Measure (Fin n → ℝ), IsFiniteMeasure ν →
      (∀ i, ν ≪ (T i).mass) →
      (∀ᵐ y ∂ν, Submodule.span ℝ (Set.range (fun i => (T i).direction y)) = ⊤) →
      ν ≪ volume

end ErrorCalculus
