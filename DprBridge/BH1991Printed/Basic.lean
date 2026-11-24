import DprBridge.Coordinate
import Mathlib.MeasureTheory.Measure.Count
import DprBridge.ChainRuleBridge.Basic
import ErrorCalculus.Dirichlet.EIDConditionalGeneral
import ErrorCalculus.Dirichlet.EntropyDecay.Basic
import ErrorCalculus.Dirichlet.ResolventMarkov.Basic
import ErrorCalculus.Dirichlet.SemigroupResolvent
import Foundations.Sections.Defs
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# The printed BH energy image density conjecture

This file contains the definitions and results of the development of `DprBridge.BH1991Printed` that
the main statements of the library (the head theorems listed in the README of the repository) use.
`DprBridge.BH1991Printed` imports it and continues the development.

## Main definitions

* `BH1991.DirichletForm`: A BH Dirichlet form on `L²(m)`: a densely defined closed nonnegative
  symmetric quadratic form such that `min f 1` has a domain representative with energy at most that
  of `f`.
* `BH1991.DirichletForm.Local`: Locality (L₂): `D.form.E f g = 0` whenever `(f + a) * g = 0` holds
  `m`-a.e. for some real constant `a`.
* `BH1991.DirichletForm.Bounded`: Essential boundedness of a domain representative.
* `BH1991.DirichletForm.AdmitsCarreDuChamp`: Property (R): a dense subspace of the form space of
  bounded `f`, each with `ft : Lp ℝ 1 m` such that `2 E(fh, f) - E(h, f²) = ∫ h * ft` for all
  bounded `h` (some representatives).
* `BH1991.DirichletForm.CarreDuChamp`: A carré du champ of `D`: a continuous symmetric bilinear map
  `Γ` into `L¹(m)` with `Γ f f ≥ 0` a.e. and `E(fh, g) + E(gh, f) - E(h, fg) = ∫ h * Γ f g` for
  bounded `f g h`.
* `BH1991.DirichletForm.gammaMatrix`: The `n × n` matrix whose `(i, j)` entry is `G.Γ` at the
  form-space elements of `f i` and `f j`, evaluated at `x`, with no extra factor of two.
* `BH1991.DirichletForm.eidMeasure`: The image under `x ↦ (f i x)ᵢ` of `m` weighted by
  `ENNReal.ofReal` of the determinant of `D.gammaMatrix G f x`, with no finite-mass assumption.
* `BH1991.DirichletForm.EID`: The energy image density property: `D.eidMeasure G f ≪ volume` for
  every `n > 0` and every `f : Fin n → D.form.dom`.
* `BH1991.DirichletForm.IsGeneratorPair`: The weak generator identity against all domain elements.
* `BH1991.DirichletForm.L1GeneratorCore`: The L¹ generator-core target: approximation in the form
  norm by generator pairs whose generator values are integrable.
* `BH1991.BH1991PrintedEIDConjecture`: Notes p. 302: the printed EID conjecture on sigma-finite
  measure spaces, without (P), (M), or topological regularity.
* `BH1991.NormalCurrentCertificate`: A geometric certificate consisting of normal currents whose
  masses dominate the given measure and whose directions span almost everywhere.
* `BH1991.CountableCurrentCertificate`: A countable family of finite measures carrying
  normal-current certificates, whose sum dominates the target measure.
* `BH1991.BHNormalCurrentReduction`: The normal-current reduction predicate: existence of countably
  many finite normal-current certificates dominating each BH determinant-weighted image measure.

## Main statements

* `BH1991.generator_pair_centered`: The generator identity for a centered composition, retaining the
  total-mass correction and both required integrability assumptions.
* `BH1991.bh1991_printed_eid_conjecture_of_normal_currents`: Conditional on
  BHNormalCurrentReduction, the printed BH EID conjecture holds.

## References

References: Bouleau–Hirsch (1991), definitions in ch. I; EID in ch. V, p. 185; Notes, p. 302.
Eriksson-Bique–Murugan, arXiv:2510.13659v1, Conjecture 1.6 and Theorem 1.7 provide the related
probability-space formulation.
-/
noncomputable section
open MeasureTheory Filter Topology ErrorCalculus
open scoped NNReal ENNReal
open scoped ContDiff
universe u

namespace DprBridge.BH1991

/-! Part A: BH definitions without (P) or (M). -/

/--
BH 1991, I.1.1.1 and I.3.1.1: a densely defined closed form with the contraction f ↦ min f 1.
-/
structure DirichletForm {X : Type u} [MeasurableSpace X] (m : Measure X) where
  /-- The underlying nonnegative symmetric quadratic form on `L²(m)`. -/
  form : QuadForm (Lp ℝ 2 m)
  dense : Dense (form.dom : Set (Lp ℝ 2 m))
  closed : form.IsClosed
  markov : ∀ f : form.dom, ∃ g : form.dom,
    (⇑(g : Lp ℝ 2 m) =ᵐ[m] fun x => min ((f : Lp ℝ 2 m) x) 1) ∧
      form.E g g ≤ form.E f f

namespace DirichletForm
variable {X : Type u} [MeasurableSpace X] {m : Measure X} (D : DirichletForm m)

/--
BH 1991, I.5.1.3 and ch. V, p. 185: locality (L₂), with arbitrary real shifts and no assumption
that constants belong to the domain.
-/
def Local : Prop :=
  ∀ f g : D.form.dom, ∀ a : ℝ,
    (∀ᵐ x ∂m, ((f : Lp ℝ 2 m) x + a) * (g : Lp ℝ 2 m) x = 0) →
      D.form.E f g = 0

/-- Essential boundedness of a domain representative. -/
def Bounded (f : D.form.dom) : Prop :=
  AEBounded (μ := m) ((f : Lp ℝ 2 m) : X → ℝ)

/--
BH 1991, I.4.1.2 and ch. V, p. 185: property (R), with a bounded subspace dense in the form norm and
explicit witnesses for the products in its integral identity.
-/
def AdmitsCarreDuChamp : Prop :=
  ∃ H : Submodule ℝ D.form.FormSpace,
    (∀ f ∈ H, D.Bounded (D.form.formToDomain f)) ∧
    Dense (H : Set D.form.FormSpace) ∧
    ∀ f ∈ H, ∃ ft : Lp ℝ 1 m, ∀ h : D.form.dom, D.Bounded h →
      ∃ p q : D.form.dom,
        (⇑(p : Lp ℝ 2 m) =ᵐ[m] fun x =>
          (D.form.formToDomain f : Lp ℝ 2 m) x * (h : Lp ℝ 2 m) x) ∧
        (⇑(q : Lp ℝ 2 m) =ᵐ[m] fun x => (D.form.formToDomain f : Lp ℝ 2 m) x ^ 2) ∧
        2 * D.form.E p (D.form.formToDomain f) - D.form.E h q =
          ∫ x, (h : Lp ℝ 2 m) x * ft x ∂m

/--
BH 1991, I.4.1.3: a continuous, symmetric, positive carré du champ satisfying the characteristic
product identity, with the BH normalization Γ = 2γ.
-/
structure CarreDuChamp where
  /-- The carré du champ, a continuous bilinear map from the form space to `L¹(m)`. -/
  Γ : D.form.FormSpace →L[ℝ] D.form.FormSpace →L[ℝ] Lp ℝ 1 m
  symm : ∀ f g, Γ f g = Γ g f
  nonneg : ∀ f, 0 ≤ᵐ[m] ⇑(Γ f f)
  product : ∀ f g h : D.form.FormSpace,
    D.Bounded (D.form.formToDomain f) → D.Bounded (D.form.formToDomain g) →
    D.Bounded (D.form.formToDomain h) → ∃ p q r : D.form.dom,
    (⇑(p : Lp ℝ 2 m) =ᵐ[m] fun x =>
      (D.form.formToDomain f : Lp ℝ 2 m) x * (D.form.formToDomain h : Lp ℝ 2 m) x) ∧
    (⇑(q : Lp ℝ 2 m) =ᵐ[m] fun x =>
      (D.form.formToDomain g : Lp ℝ 2 m) x * (D.form.formToDomain h : Lp ℝ 2 m) x) ∧
    (⇑(r : Lp ℝ 2 m) =ᵐ[m] fun x =>
      (D.form.formToDomain f : Lp ℝ 2 m) x * (D.form.formToDomain g : Lp ℝ 2 m) x) ∧
    D.form.E p (D.form.formToDomain g) + D.form.E q (D.form.formToDomain f) -
      D.form.E (D.form.formToDomain h) r =
        ∫ x, (D.form.formToDomain h : Lp ℝ 2 m) x * Γ f g x ∂m

/-- BH 1991, ch. V, p. 185: the matrix Γ(f, f*), with no extra factor of two. -/
def gammaMatrix (G : D.CarreDuChamp) {n : ℕ} (f : Fin n → D.form.dom) (x : X) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => G.Γ (D.form.formToDomain.symm (f i))
    (D.form.formToDomain.symm (f j)) x

/--
BH 1991, ch. V, p. 185: the image measure weighted by ENNReal.ofReal of the determinant of Γ(f,
f*), with no finite-mass assumption.
-/
def eidMeasure (G : D.CarreDuChamp) {n : ℕ} (f : Fin n → D.form.dom) :
    Measure (Fin n → ℝ) :=
  (m.withDensity fun x => ENNReal.ofReal (D.gammaMatrix G f x).det).map
    (fun x i => (f i : Lp ℝ 2 m) x)

/--
BH 1991, II.5.2.3 and ch. V, p. 185: absolute continuity of the determinant-weighted image
measure in
every strictly positive finite dimension.
-/
def EID (G : D.CarreDuChamp) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ f : Fin n → D.form.dom, D.eidMeasure G f ≪ volume

/--
The weak generator identity against all domain elements; L¹ integrability of the generator value is
not required.
-/
def IsGeneratorPair (g : D.form.dom) (a : Lp ℝ 2 m) : Prop :=
  ∀ v : D.form.dom, D.form.E v g = - ∫ x, (v : Lp ℝ 2 m) x * a x ∂m

/--
The L¹ generator-core target: approximation in the form norm by generator pairs whose generator
values are integrable.
-/
def L1GeneratorCore : Prop :=
  ∀ f : D.form.dom, ∃ g : ℕ → D.form.dom, ∃ a : ℕ → Lp ℝ 2 m,
    (∀ k, D.IsGeneratorPair (g k) (a k) ∧ Integrable (a k) m) ∧
    Tendsto (fun k => D.form.formToDomain.symm (g k)) atTop
      (𝓝 (D.form.formToDomain.symm f))

end DirichletForm

/--
BH 1991, definitions in ch. I; EID formulation in ch. V, p. 185; Notes p. 302: the printed EID
conjecture on sigma-finite measure
spaces, without (P), (M), or topological regularity. This is a proposition, not a proof of the
conjecture.
-/
def BH1991PrintedEIDConjecture : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (m : Measure X) [SigmaFinite m]
    (D : DirichletForm m), D.Local → D.AdmitsCarreDuChamp →
      ∀ G : D.CarreDuChamp, D.EID G

/-! Part B: the centered boundary identity and reduction to normal currents. -/

section Boundary
variable {X : Type u} [MeasurableSpace X] {m : Measure X}

/--
The centered boundary integral retains the constant times the total generator mass, assuming both
integrabilities.
-/
theorem neg_integral_centered_mul (a v : X → ℝ) (c : ℝ)
    (ha : Integrable a m) (hva : Integrable (fun x => v x * a x) m) :
    -(∫ x, (v x - c) * a x ∂m) =
      -(∫ x, v x * a x ∂m) + c * ∫ x, a x ∂m := by
  simp_rw [sub_mul]
  rw [integral_sub hva (ha.const_mul c), integral_const_mul]
  ring

/--
The generator identity for a centered composition, retaining the total-mass correction and both
required integrability assumptions.
-/
theorem generator_pair_centered (D : DirichletForm m) (g w : D.form.dom)
    (a : Lp ℝ 2 m) (hA : D.IsGeneratorPair g a) (v : X → ℝ) (c : ℝ)
    (hw : ⇑(w : Lp ℝ 2 m) =ᵐ[m] fun x => v x - c)
    (ha : Integrable a m) (hva : Integrable (fun x => v x * a x) m) :
    D.form.E w g = -(∫ x, v x * a x ∂m) + c * ∫ x, a x ∂m := by
  rw [hA w]
  have he : (∫ x, (w : Lp ℝ 2 m) x * a x ∂m) = ∫ x, (v x - c) * a x ∂m := by
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    rw [hx]
  rw [he]
  exact neg_integral_centered_mul a v c ha hva

end Boundary

/--
A geometric certificate consisting of normal currents whose masses dominate the given measure and
whose directions span almost everywhere.
-/
structure NormalCurrentCertificate {n : ℕ} (ν : Measure (Fin n → ℝ)) where
  /-- The `n` polar one-currents of the certificate. -/
  currents : Fin n → PolarCurrent n
  normal : ∀ i, (currents i).IsNormal
  dominated : ∀ i, ν ≪ (currents i).mass
  spans : ∀ᵐ y ∂ν, Submodule.span ℝ (Set.range fun i => (currents i).direction y) = ⊤

/--
A finite measure with a normal-current certificate is absolutely continuous with respect to
volume, by the existing DPR bridge.
-/
theorem absolutelyContinuous_of_certificate {n : ℕ} {ν : Measure (Fin n → ℝ)}
    [IsFiniteMeasure ν] (C : NormalCurrentCertificate ν) : ν ≪ volume :=
  DprBridge.dePhilippisRindler n C.currents C.normal ν inferInstance C.dominated C.spans

/--
Absolute continuity glues under countable domination, without a finite-mass assumption on the final
measure.
-/
theorem absolutelyContinuous_of_countable_domination {Y : Type*} [MeasurableSpace Y]
    {ν ρ : Measure Y} (νk : ℕ → Measure Y) (hdom : ν ≪ Measure.sum νk)
    (h : ∀ k, νk k ≪ ρ) : ν ≪ ρ := by
  apply hdom.trans
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hρ
  rw [Measure.sum_apply _ hs]
  have hz : ∀ k, νk k s = 0 := fun k => h k hρ
  simp only [hz, tsum_zero]

/--
A countable family of finite measures carrying normal-current certificates, whose sum dominates the
target measure.
-/
structure CountableCurrentCertificate {n : ℕ} (ν : Measure (Fin n → ℝ)) where
  /-- The countably many finite measures whose sum dominates `ν`: `ν ≪ Measure.sum pieces`. -/
  pieces : ℕ → Measure (Fin n → ℝ)
  finite : ∀ k, IsFiniteMeasure (pieces k)
  /-- A normal-current certificate for each piece. -/
  certificate : ∀ k, NormalCurrentCertificate (pieces k)
  dominated : ν ≪ Measure.sum pieces

/--
A measure with a countable normal-current certificate is absolutely continuous with respect to
volume, even if it has infinite mass.
-/
theorem absolutelyContinuous_of_countable_certificate {n : ℕ}
    {ν : Measure (Fin n → ℝ)} (C : CountableCurrentCertificate ν) : ν ≪ volume := by
  apply absolutelyContinuous_of_countable_domination C.pieces C.dominated
  intro k
  letI := C.finite k
  exact absolutelyContinuous_of_certificate (C.certificate k)

/--
The normal-current reduction predicate: existence of countably many finite normal-current
certificates dominating each BH determinant-weighted image measure.
-/
def BHNormalCurrentReduction : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (m : Measure X) [SigmaFinite m]
    (D : DirichletForm m), D.Local → D.AdmitsCarreDuChamp →
    ∀ G : D.CarreDuChamp, ∀ n : ℕ, 0 < n → ∀ f : Fin n → D.form.dom,
      Nonempty (CountableCurrentCertificate (D.eidMeasure G f))

/--
Conditional on BHNormalCurrentReduction, the printed BH EID conjecture holds. Sources: BH 1991,
definitions in ch. I; EID formulation in ch. V, p. 185; Notes p. 302. The hypothesis supplies the
geometric certificates; their construction is not proved here.
-/
theorem bh1991_printed_eid_conjecture_of_normal_currents
    (h : BHNormalCurrentReduction.{u}) : BH1991PrintedEIDConjecture.{u} := by
  intro X _ m _ D hL hR G n hn f
  obtain ⟨C⟩ := h X m D hL hR G n hn f
  exact absolutelyContinuous_of_countable_certificate C

/-!
Results outside this module:
* The unconditional printed BH EID conjecture and the normal-current reduction contract are
proved in `DprBridge.BH1991PrintedProof`.
* The L1 generator core and centered functional calculus from the raw BH assumptions are proved in
`DprBridge.BH1991ResolventCore`, `DprBridge.BH1991ChainRules` and `DprBridge.BH1991ChainCurrents`.
* The converse implication from LocalZero to Local is not supplied here.
-/


end DprBridge.BH1991
