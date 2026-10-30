import DprBridge.Coordinate
import DprBridge.ChainRuleBridge
import Mathlib.MeasureTheory.Measure.Count

/-!
# The printed BH energy image density conjecture

## Main results
The sigma-finite BH statement is reduced to normal-current certificates. Its proof in
`DprBridge.BH1991PrintedProof` follows the normal-current method of Eriksson-Bique–Murugan (Section
4.2, Remark 4.12) and the structure theorem of De Philippis–Rindler.

References: Bouleau–Hirsch (1991), definitions in ch. I; EID in ch. V, p. 185; Notes, p. 302.
Eriksson-Bique–Murugan, arXiv:2510.13659v1, Conjecture 1.6 and Theorem 1.7 provide the related
probability-space formulation. Infinite-measure examples record the scope of the sigma-finite
statement.
-/
noncomputable section
set_option autoImplicit false
-- Elaborating the zero-form and L² constructions requires this local budget.
set_option maxHeartbeats 1200000
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

/--
BH 1991, I.5.1.2: locality (L₀), for all domain representatives of centered smooth
compositions with disjoint compact supports.
-/
def LocalZero : Prop :=
  ∀ f : D.form.dom, ∀ F G : ℝ → ℝ, ContDiff ℝ ∞ F → ContDiff ℝ ∞ G →
    HasCompactSupport F → HasCompactSupport G → Disjoint (tsupport F) (tsupport G) →
    ∀ v w : D.form.dom,
    (⇑(v : Lp ℝ 2 m) =ᵐ[m] fun x => F ((f : Lp ℝ 2 m) x) - F 0) →
    (⇑(w : Lp ℝ 2 m) =ᵐ[m] fun x => G ((f : Lp ℝ 2 m) x) - G 0) →
      D.form.E v w = 0

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

/-- BH locality forces zero energy for a domain element equal to one almost everywhere. -/
theorem energy_one_eq_zero (hL : D.Local) (one : D.form.dom)
    (h : ⇑(one : Lp ℝ 2 m) =ᵐ[m] fun _ => (1 : ℝ)) : D.form.E one one = 0 := by
  apply hL one one (-1)
  filter_upwards [h] with x hx
  rw [hx]
  norm_num

/-- Functions with disjoint topological supports have pointwise zero product. -/
theorem mul_eq_zero_of_disjoint_tsupport {F G : ℝ → ℝ}
    (h : Disjoint (tsupport F) (tsupport G)) (t : ℝ) : F t * G t = 0 := by
  by_cases hF : F t = 0
  · simp [hF]
  by_cases hG : G t = 0
  · simp [hG]
  exact False.elim (Set.disjoint_left.1 h (subset_closure hF) (subset_closure hG))

/--
BH 1991, I.5.1.3: the implication (L₂) ⇒ (L₀), without probability, constants, or carré du
champ.
-/
theorem localZero_of_local (hL : D.Local) : D.LocalZero := by
  intro f F G _ _ _ _ hFG v w hv hw
  have hp := mul_eq_zero_of_disjoint_tsupport hFG
  rcases mul_eq_zero.1 (hp 0) with hF | hG
  · rw [D.form.symm]
    apply hL w v (G 0)
    filter_upwards [hv, hw] with x hx hy
    rw [hx, hy, hF, sub_zero, sub_add_cancel]
    rw [mul_comm]
    exact hp _
  · apply hL v w (F 0)
    filter_upwards [hv, hw] with x hx hy
    rw [hx, hy, hG, sub_zero, sub_add_cancel]
    exact hp _

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

/--
Eriksson-Bique–Murugan (EBM), arXiv:2510.13659v1, conjecture 1.6: the EID statement in an
arbitrary universe.
-/
def EBMConjecture_1_6_universe : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (m : Measure X) [IsProbabilityMeasure m]
    (D : TextStatements.EBMDirichletStructure m) (G : TextStatements.EBMCarreDuChamp D),
      TextStatements.EBMEIDProperty G

/--
Eriksson-Bique–Murugan (EBM), conjecture 1.6 and theorem 1.7: EID for every EBM structure in an
arbitrary universe, using the existing per-structure bridge.
-/
theorem ebm_conjecture_1_6_universe : EBMConjecture_1_6_universe.{u} := by
  intro X _ m _ D G
  exact TextStatements.ebm_theorem_1_7 G

/--
At universe zero the EBM proposition is equivalent to the existing EBMConjecture_1_6 by definitional
equality.
-/
theorem ebmConjecture_universe_zero_iff :
    EBMConjecture_1_6_universe.{0} ↔ TextStatements.EBMConjecture_1_6 := Iff.rfl

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

/--
The centering correction vanishes when the total generator mass is zero, assuming both
integrabilities.
-/
theorem neg_integral_centered_mul_of_integral_eq_zero (a v : X → ℝ) (c : ℝ)
    (ha : Integrable a m) (hva : Integrable (fun x => v x * a x) m)
    (h0 : ∫ x, a x ∂m = 0) :
    -(∫ x, (v x - c) * a x ∂m) = -(∫ x, v x * a x ∂m) := by
  rw [neg_integral_centered_mul a v c ha hva, h0, mul_zero, add_zero]

end Boundary

/--
A geometric certificate consisting of normal currents whose masses dominate the given measure and
whose directions span almost everywhere.
-/
structure NormalCurrentCertificate {n : ℕ} (ν : Measure (Fin n → ℝ)) where
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
  pieces : ℕ → Measure (Fin n → ℝ)
  finite : ∀ k, IsFiniteMeasure (pieces k)
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

section EquivalentMeasure
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {m p : Measure X} {f : X → Y} {ν : Measure Y}

/--
Transfer absolute continuity of image measures along equivalent source measures under a measurable
map.
-/
theorem map_absolutelyContinuous_iff_of_equivalent (hmp : m ≪ p) (hpm : p ≪ m)
    (hf : Measurable f) : m.map f ≪ ν ↔ p.map f ≪ ν :=
  ⟨fun h => (hpm.map hf).trans h, fun h => (hmp.map hf).trans h⟩

/--
An almost everywhere measurable, almost everywhere nonzero density gives equivalent measures without
a uniform positive lower bound.
-/
theorem withDensity_equivalent {h : X → ℝ≥0∞} (hh : AEMeasurable h m)
    (hp : ∀ᵐ x ∂m, h x ≠ 0) : m.withDensity h ≪ m ∧ m ≪ m.withDensity h :=
  ⟨withDensity_absolutelyContinuous m h, withDensity_absolutelyContinuous' hh hp⟩

end EquivalentMeasure

/-! Controls: an infinite measure and a domain without the constant one. -/

section ZeroModel
variable {X : Type u} [MeasurableSpace X] (m : Measure X)

/-- The zero form on the whole L² space of an arbitrary measure. -/
def zeroQuad : QuadForm (Lp ℝ 2 m) where
  dom := ⊤
  E := 0
  symm _ _ := rfl
  nonneg _ := le_rfl

/-- The zero form is closed without any assumption on the total mass. -/
theorem zeroQuad_closed : (zeroQuad m).IsClosed := by
  intro v _ w _
  refine ⟨Submodule.mem_top, ?_⟩
  exact tendsto_const_nhds

/-- The zero BH form on the whole L² space, with the printed contraction min f 1. -/
def zeroForm : DirichletForm m where
  form := zeroQuad m
  dense := by simp [zeroQuad]
  closed := zeroQuad_closed m
  markov f := by
    have hL : LipschitzWith 1 (fun t : ℝ => min t 1) := LipschitzWith.id.min_const 1
    have h0 : min (0 : ℝ) 1 = 0 := by norm_num
    have h := hL.comp_memLp h0 (Lp.memLp (f : Lp ℝ 2 m))
    exact ⟨⟨h.toLp _, Submodule.mem_top⟩, h.coeFn_toLp, le_rfl⟩

/--
The zero form as an existing normal-contraction structure, used for density of bounded elements.
-/
def zeroCapacityForm : ErrorCalculus.Capacity.DirichletForm m where
  form := zeroQuad m
  closed := zeroQuad_closed m
  contraction := by
    intro F hF h0 u w hw
    exact ⟨Submodule.mem_top, le_rfl⟩

/-- The zero form satisfies BH locality for every real shift. -/
theorem zeroForm_local : (zeroForm m).Local := by
  intro f g a h
  rfl

/-- A bounded factor ensures that a product belongs to the full L² domain of the zero form. -/
theorem zeroForm_bounded_product (f g : (zeroForm m).form.dom)
    (hf : (zeroForm m).Bounded f) : ∃ p : (zeroForm m).form.dom,
      ⇑(p : Lp ℝ 2 m) =ᵐ[m] fun x => (f : Lp ℝ 2 m) x * (g : Lp ℝ 2 m) x := by
  obtain ⟨C, hC⟩ := hf
  have hC' : ∀ᵐ x ∂m, |(f : Lp ℝ 2 m) x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC
  have hp := ErrorCalculus.Capacity.DirichletForm.memLp_mul_of_bdd hC' (g : Lp ℝ 2 m)
  exact ⟨⟨hp.toLp _, Submodule.mem_top⟩, hp.coeFn_toLp⟩

/--
The zero operator is a carré du champ for the zero form and satisfies the full characteristic
product identity.
-/
def zeroCarreDuChamp : (zeroForm m).CarreDuChamp where
  Γ := 0
  symm _ _ := rfl
  nonneg _ := by
    change 0 ≤ᵐ[m] ⇑(0 : Lp ℝ 1 m)
    filter_upwards [Lp.coeFn_zero ℝ 1 m] with x hx
    exact le_of_eq hx.symm
  product f g h hf hg hh := by
    obtain ⟨p, hp⟩ := zeroForm_bounded_product m ((zeroForm m).form.formToDomain f)
      ((zeroForm m).form.formToDomain h) hf
    obtain ⟨q, hq⟩ := zeroForm_bounded_product m ((zeroForm m).form.formToDomain g)
      ((zeroForm m).form.formToDomain h) hg
    obtain ⟨r, hr⟩ := zeroForm_bounded_product m ((zeroForm m).form.formToDomain f)
      ((zeroForm m).form.formToDomain g) hf
    refine ⟨p, q, r, hp, hq, hr, ?_⟩
    change 0 + 0 - 0 = ∫ x, _ * (0 : Lp ℝ 1 m) x ∂m
    rw [integral_congr_ae (show (fun x =>
        ((zeroForm m).form.formToDomain h : Lp ℝ 2 m) x * (0 : Lp ℝ 1 m) x) =ᵐ[m]
        fun _ => (0 : ℝ) from by
      filter_upwards [Lp.coeFn_zero ℝ 1 m] with x hx
      change (0 : Lp ℝ 1 m) x = 0 at hx
      rw [hx, mul_zero])]
    simp

/-- Property (R) holds for the zero form, using the bounded subspace dense in the form norm. -/
theorem zeroForm_admitsCarreDuChamp : (zeroForm m).AdmitsCarreDuChamp := by
  let C := zeroCapacityForm m
  refine ⟨C.bddSpace, ?_, C.dense_bddSpace, ?_⟩
  · intro f hf
    have he : C.toLp f = ((zeroForm m).form.formToDomain f : Lp ℝ 2 m) := rfl
    simpa only [DirichletForm.Bounded, AEBounded, Real.norm_eq_abs, he] using
      ((C.mem_bddSpace).1 hf)
  · intro f hf
    refine ⟨0, ?_⟩
    intro h hh
    have hf' : (zeroForm m).Bounded ((zeroForm m).form.formToDomain f) := by
      have he : C.toLp f = ((zeroForm m).form.formToDomain f : Lp ℝ 2 m) := rfl
      simpa only [DirichletForm.Bounded, AEBounded, Real.norm_eq_abs, he] using
        ((C.mem_bddSpace).1 hf)
    obtain ⟨p, hp⟩ := zeroForm_bounded_product m ((zeroForm m).form.formToDomain f) h hf'
    obtain ⟨q, hq⟩ := zeroForm_bounded_product m ((zeroForm m).form.formToDomain f)
      ((zeroForm m).form.formToDomain f) hf'
    refine ⟨p, q, hp, ?_, ?_⟩
    · simpa only [pow_two] using hq
    · change 2 * 0 - 0 = ∫ x, (h : Lp ℝ 2 m) x * (0 : Lp ℝ 1 m) x ∂m
      rw [integral_congr_ae (show (fun x => (h : Lp ℝ 2 m) x * (0 : Lp ℝ 1 m) x) =ᵐ[m]
          fun _ => (0 : ℝ) from by
        filter_upwards [Lp.coeFn_zero ℝ 1 m] with x hx
        change (0 : Lp ℝ 1 m) x = 0 at hx
        rw [hx, mul_zero])]
      simp

end ZeroModel

/-- Counting measure on the natural numbers has infinite total mass. -/
theorem count_univ_eq_top : (Measure.count : Measure ℕ) Set.univ = ⊤ :=
  Measure.count_apply_infinite Set.infinite_univ

/-- The constant one does not belong to L² of counting measure on the natural numbers. -/
theorem not_memLp_one_count : ¬ MemLp (fun _ : ℕ => (1 : ℝ)) 2 Measure.count := by
  intro h
  have hi : Integrable (fun _ : ℕ => (1 : ℝ)) Measure.count := by
    simpa using h.integrable_sq
  have hs : Summable (fun _ : ℕ => (1 : ℝ)) := by
    simpa [integrable_count_iff] using hi
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero)

/--
No element of the zero-form domain for counting measure on the natural numbers represents
the constant one.
-/
theorem zeroForm_count_no_one :
    ¬ ∃ f : (zeroForm (Measure.count : Measure ℕ)).form.dom,
      ⇑(f : Lp ℝ 2 (Measure.count : Measure ℕ)) =ᵐ[Measure.count] fun _ => (1 : ℝ) := by
  rintro ⟨f, hf⟩
  exact not_memLp_one_count
    ((memLp_congr_ae hf).mp (Lp.memLp (f : Lp ℝ 2 (Measure.count : Measure ℕ))))

/--
Counting measure and the zero form simultaneously give infinite mass, BH locality, property (R), a
carré du champ, and no domain representative of the constant one.
-/
theorem infinite_model :
    (Measure.count : Measure ℕ) Set.univ = ⊤ ∧
    (zeroForm (Measure.count : Measure ℕ)).Local ∧
    (zeroForm (Measure.count : Measure ℕ)).AdmitsCarreDuChamp ∧
    Nonempty ((zeroForm (Measure.count : Measure ℕ)).CarreDuChamp) ∧
    ¬ ∃ f : (zeroForm (Measure.count : Measure ℕ)).form.dom,
      ⇑(f : Lp ℝ 2 (Measure.count : Measure ℕ)) =ᵐ[Measure.count] fun _ => (1 : ℝ) :=
  ⟨count_univ_eq_top, zeroForm_local _, zeroForm_admitsCarreDuChamp _,
    ⟨zeroCarreDuChamp _⟩, zeroForm_count_no_one⟩

/-!
Results outside this module:
* The unconditional printed BH EID conjecture and the normal-current reduction contract are
proved in `DprBridge.BH1991PrintedProof`.
* The L1 generator core and centered functional calculus from the raw BH assumptions are proved in
`DprBridge.BH1991ResolventCore`, `DprBridge.BH1991ChainRules` and `DprBridge.BH1991ChainCurrents`.
* The converse implication from LocalZero to Local is not supplied here.
-/


end DprBridge.BH1991

/-! Standard transitive axiom reports for all 42 named declarations. -/
#print axioms DprBridge.BH1991.DirichletForm
#print axioms DprBridge.BH1991.DirichletForm.Local
#print axioms DprBridge.BH1991.DirichletForm.LocalZero
#print axioms DprBridge.BH1991.DirichletForm.Bounded
#print axioms DprBridge.BH1991.DirichletForm.AdmitsCarreDuChamp
#print axioms DprBridge.BH1991.DirichletForm.CarreDuChamp
#print axioms DprBridge.BH1991.DirichletForm.gammaMatrix
#print axioms DprBridge.BH1991.DirichletForm.eidMeasure
#print axioms DprBridge.BH1991.DirichletForm.EID
#print axioms DprBridge.BH1991.DirichletForm.energy_one_eq_zero
#print axioms DprBridge.BH1991.DirichletForm.mul_eq_zero_of_disjoint_tsupport
#print axioms DprBridge.BH1991.DirichletForm.localZero_of_local
#print axioms DprBridge.BH1991.DirichletForm.IsGeneratorPair
#print axioms DprBridge.BH1991.DirichletForm.L1GeneratorCore
#print axioms DprBridge.BH1991.BH1991PrintedEIDConjecture
#print axioms DprBridge.BH1991.EBMConjecture_1_6_universe
#print axioms DprBridge.BH1991.ebm_conjecture_1_6_universe
#print axioms DprBridge.BH1991.ebmConjecture_universe_zero_iff
#print axioms DprBridge.BH1991.neg_integral_centered_mul
#print axioms DprBridge.BH1991.generator_pair_centered
#print axioms DprBridge.BH1991.neg_integral_centered_mul_of_integral_eq_zero
#print axioms DprBridge.BH1991.NormalCurrentCertificate
#print axioms DprBridge.BH1991.absolutelyContinuous_of_certificate
#print axioms DprBridge.BH1991.absolutelyContinuous_of_countable_domination
#print axioms DprBridge.BH1991.CountableCurrentCertificate
#print axioms DprBridge.BH1991.absolutelyContinuous_of_countable_certificate
#print axioms DprBridge.BH1991.BHNormalCurrentReduction
#print axioms DprBridge.BH1991.bh1991_printed_eid_conjecture_of_normal_currents
#print axioms DprBridge.BH1991.map_absolutelyContinuous_iff_of_equivalent
#print axioms DprBridge.BH1991.withDensity_equivalent
#print axioms DprBridge.BH1991.zeroQuad
#print axioms DprBridge.BH1991.zeroQuad_closed
#print axioms DprBridge.BH1991.zeroForm
#print axioms DprBridge.BH1991.zeroCapacityForm
#print axioms DprBridge.BH1991.zeroForm_local
#print axioms DprBridge.BH1991.zeroForm_bounded_product
#print axioms DprBridge.BH1991.zeroCarreDuChamp
#print axioms DprBridge.BH1991.zeroForm_admitsCarreDuChamp
#print axioms DprBridge.BH1991.count_univ_eq_top
#print axioms DprBridge.BH1991.not_memLp_one_count
#print axioms DprBridge.BH1991.zeroForm_count_no_one
#print axioms DprBridge.BH1991.infinite_model
