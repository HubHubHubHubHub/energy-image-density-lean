import GeometricMeasure.Current.FiniteNormalFamily
import GeometricMeasure.VectorMeasure.Operations

/-!
# Local Mass

## Main results
Positive masses on open domains, finite interior pieces and integrable local tests.

Following the method of De Philippis–Rindler (2016), Theorem 1.1, Corollaries 1.12 and 1.13, and
Section 2.1. The local heads extend the printed finite vector-measure statements to locally finite
masses. The controls are compiled separately from the library aggregator.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

namespace GeometricMeasure.LocalStructureContracts

/-- Euclidean spatial and value coordinates in dimension d. -/
abbrev V (d : ℕ) := EuclideanSpace ℝ (Fin d)

/--
The real first order wave cone, with a frequency of norm one.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Section 2.1.
-/
def waveOne {d m n : ℕ} (A : Fin d → V m →L[ℝ] V n) : Set (V m) :=
  {v | ∃ ξ : V d, ‖ξ‖ = 1 ∧ (∑ j, ξ j • A j v) = 0}

/--
The first order equation on interior scalar tests, with a zeroth order term and signed sources.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Section 2.1.
-/
def EquationOneOn {d m n : ℕ} (M : VectorMeasure (V d) (V m))
    (A₀ : V m →L[ℝ] V n) (A : Fin d → V m →L[ℝ] V n)
    (σ : Fin n → SignedMeasure (V d)) (U : Set (V d)) : Prop :=
  ∀ a (φ : ScalarCurrentTest d), tsupport (φ : V d → ℝ) ⊆ U →
    (∫ x, φ x * A₀ (polarDensity M x) a ∂M.variation) -
      (∑ j, ∫ x, fderiv ℝ (φ : V d → ℝ) x
        (WithLp.toLp 2 (Pi.single j (1 : ℝ))) * A j (polarDensity M x) a ∂M.variation) =
      signedTestCurrent (σ a) φ

/--
The finite first order contract: the polar density lies in the unit-frequency wave cone almost
everywhere for the singular variation restricted to the open domain, in positive spatial dimension.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Section 2.1.
-/
def TargetA4 : Prop :=
  ∀ (d m n : ℕ), 0 < d → ∀ (M : VectorMeasure (V d) (V m))
    (A₀ : V m →L[ℝ] V n) (A : Fin d → V m →L[ℝ] V n)
    (σ : Fin n → SignedMeasure (V d)) (U : Set (V d)),
    IsOpen U → EquationOneOn M A₀ A σ U →
    ∀ᵐ x ∂(M.variation.singularPart volume).restrict U, polarDensity M x ∈ waveOne A

/--
The finite family contract: local divergence equations, domination by each variation and almost
everywhere spanning imply absolute continuity of the restricted arbitrary positive measure.

Following the method of De Philippis–Rindler (2016), Corollary 1.12 and Section 2.1.
-/
def TargetA5Finite : Prop :=
  ∀ (r d : ℕ) (R : Fin r → VectorMeasure (V d) (V d))
    (D : Fin r → SignedMeasure (V d)) (U : Set (V d)), IsOpen U →
    (∀ i, HasMeasureDivergenceOn (R i) (D i) U) →
    ∀ ν : Measure (V d), (∀ i, ν.restrict U ≪ (R i).variation) →
    (∀ᵐ x ∂ν.restrict U, Submodule.span ℝ (range fun i => polarDensity (R i) x) = ⊤) →
    ν.restrict U ≪ volume

/--
A positive mass concentrated on the domain and finite on every compact subset of it. The definition
imposes neither openness nor ambient local finiteness at boundary points.

The printed finite-measure convention is De Philippis–Rindler (2016), Section 2.1; this contract
permits infinite total mass.
-/
def LocalMass {d : ℕ} (Ω : Set (V d)) (ρ : Measure (V d)) : Prop :=
  ρ Ωᶜ = 0 ∧ ∀ K : Set (V d), IsCompact K → K ⊆ Ω → ρ K < ∞

/--
The row equations on interior tests, with source masses concentrated on the domain and finite on its
compact subsets, and measurable source densities bounded in absolute value by one almost everywhere.
-/
def LocalRows {r d : ℕ} (Ω : Set (V d)) (ρ : Measure (V d))
    (p : V d → EuclideanSpace ℝ (Fin r × Fin d))
    (β : Fin r → Measure (V d)) (q : Fin r → V d → ℝ) : Prop :=
  (∀ i, LocalMass Ω (β i)) ∧ (∀ i, Measurable (q i)) ∧
    (∀ i, ∀ᵐ x ∂β i, |q i x| ≤ 1) ∧
    ∀ i (φ : ScalarCurrentTest d), tsupport (φ : V d → ℝ) ⊆ Ω →
      (∫ x, φ x * q i x ∂β i) =
      -(∫ x, fderiv ℝ (φ : V d → ℝ) x (WithLp.toLp 2 (fun j => p x (i, j))) ∂ρ)

/--
The rectangular rank contract for a local mass and a measurable unit density satisfying the local
row equations: rank is at most d - 1 almost everywhere for the restricted singular mass.

This extends the printed Corollary 1.13 of De Philippis–Rindler (2016) to locally finite masses,
following the method of De Philippis–Rindler. The printed vector measures are finite under Section
2.1. The matrix values may be rectangular.

Source: De Philippis–Rindler (2016), Corollary 1.13 and Section 2.1.
-/
def TargetA3 : Prop :=
  ∀ (r d : ℕ) (Ω : Set (V d)), IsOpen Ω →
    ∀ (ρ : Measure (V d)) (p : V d → EuclideanSpace ℝ (Fin r × Fin d)),
    LocalMass Ω ρ → Measurable p → (∀ᵐ x ∂ρ, ‖p x‖ = 1) →
    ∀ (β : Fin r → Measure (V d)) (q : Fin r → V d → ℝ), LocalRows Ω ρ p β q →
    ∀ᵐ x ∂(ρ.singularPart volume).restrict Ω,
      Matrix.rank (fun i j => p x (i, j) : Matrix (Fin r) (Fin d) ℝ) ≤ d - 1

/--
The open-domain covering contract: countably many open sets lie inside compact interiors, the
compact sets lie in the domain, and the open sets cover it.
-/
def TargetCover : Prop :=
  ∀ (d : ℕ) (Ω : Set (V d)), IsOpen Ω → ∃ U K : ℕ → Set (V d),
    (∀ j, IsOpen (U j) ∧ IsCompact (K j) ∧ U j ⊆ interior (K j) ∧ K j ⊆ Ω) ∧
    (⋃ j, U j) = Ω

/--
The singular restriction contract: for a sigma-finite mass, the singular part relative to volume
commutes with measurable restriction.
-/
def TargetSingularRestriction : Prop :=
  ∀ (d : ℕ) (ρ : Measure (V d)), SigmaFinite ρ →
    ∀ U : Set (V d), MeasurableSet U →
      (ρ.restrict U).singularPart volume = (ρ.singularPart volume).restrict U

/--
The rectangular finite piece contract: a measurable unit density of a local mass is integrable on
each compact interior piece and its vector measure has exactly the restricted mass as variation.
-/
def TargetFinitePiece : Prop :=
  ∀ (r d : ℕ) (Ω : Set (V d)) (ρ : Measure (V d))
    (p : V d → EuclideanSpace ℝ (Fin r × Fin d)),
    LocalMass Ω ρ → Measurable p → (∀ᵐ x ∂ρ, ‖p x‖ = 1) →
    ∀ K : Set (V d), IsCompact K → K ⊆ Ω →
      Integrable p (ρ.restrict K) ∧
      ((ρ.restrict K).withDensityᵥ p).variation = ρ.restrict K

/--
The countable gluing contract for arbitrary positive masses and predicates, on a measurable domain
covered by measurable sets.
-/
def TargetGlue : Prop :=
  ∀ (d : ℕ) (ρ : Measure (V d)) (Ω : Set (V d)) (U : ℕ → Set (V d)) (P : V d → Prop),
    MeasurableSet Ω → (∀ j, MeasurableSet (U j)) → Ω ⊆ ⋃ j, U j →
    (∀ j, ∀ᵐ x ∂ρ.restrict (U j), P x) → ∀ᵐ x ∂ρ.restrict Ω, P x

/--
The local family contract: locally finite masses with measurable unit densities and local divergence
equations force absolute continuity of an arbitrary positive measure restricted to the domain, under
domination and almost everywhere spanning.

This extends the printed Corollary 1.12 of De Philippis–Rindler (2016) to locally finite masses,
following the method of De Philippis–Rindler. The printed vector measures are finite under Section
2.1. The dominated positive measure may be arbitrary.

Source: De Philippis–Rindler (2016), Corollary 1.12 and Section 2.1.
-/
def TargetA5Local : Prop :=
  ∀ (r d : ℕ) (Ω : Set (V d)), IsOpen Ω →
    ∀ (ρ : Fin r → Measure (V d)) (τ : Fin r → V d → V d),
    (∀ i, LocalMass Ω (ρ i)) → (∀ i, Measurable (τ i)) →
    (∀ i, ∀ᵐ x ∂ρ i, ‖τ i x‖ = 1) →
    ∀ (β : Fin r → Measure (V d)) (q : Fin r → V d → ℝ),
    (∀ i, LocalMass Ω (β i)) → (∀ i, Measurable (q i)) →
    (∀ i, ∀ᵐ x ∂β i, |q i x| ≤ 1) →
    (∀ i (φ : ScalarCurrentTest d), tsupport (φ : V d → ℝ) ⊆ Ω →
      (∫ x, φ x * q i x ∂β i) = -(∫ x, fderiv ℝ (φ : V d → ℝ) x (τ i x) ∂ρ i)) →
    ∀ ν : Measure (V d), (∀ i, ν.restrict Ω ≪ ρ i) →
    (∀ᵐ x ∂ν.restrict Ω, Submodule.span ℝ (range fun i => τ i x) = ⊤) →
    ν.restrict Ω ≪ volume


/--
The sigma-finiteness contract: concentration on an open domain and finiteness on its compact subsets
imply sigma-finiteness of the ambient positive measure.
-/
def TargetSigmaFinite : Prop :=
  ∀ (d : ℕ) (Ω : Set (V d)), IsOpen Ω → ∀ ρ : Measure (V d),
    LocalMass Ω ρ → SigmaFinite ρ

/--
The polar piece contract: a measurable unit density of a local mass is integrable on every compact
interior piece, gives exact variation, and agrees almost everywhere with both polar conventions.
-/
def TargetPolarFinitePiece : Prop :=
  ∀ (d m : ℕ) (Ω : Set (V d)) (ρ : Measure (V d)) (p : V d → V m),
    LocalMass Ω ρ → Measurable p → (∀ᵐ x ∂ρ, ‖p x‖ = 1) →
    ∀ K : Set (V d), IsCompact K → K ⊆ Ω →
      Integrable p (ρ.restrict K) ∧
      ((ρ.restrict K).withDensityᵥ p).variation = ρ.restrict K ∧
      VectorMeasure.polar ((ρ.restrict K).withDensityᵥ p) =ᵐ[ρ.restrict K] p ∧
      polarDensity ((ρ.restrict K).withDensityᵥ p) =ᵐ[ρ.restrict K] p

/--
The row transport contract: restricting the mass and sources to an interior compact set preserves
the rectangular divergence equation on an open subset of its interior.
-/
def TargetRowEquationFinitePiece : Prop :=
  ∀ (r d : ℕ) (Ω : Set (V d)) (ρ : Measure (V d)) (p : V d → RectMatrixSpace r d)
    (β : Fin r → Measure (V d)) (q : Fin r → V d → ℝ),
    IsOpen Ω → LocalMass Ω ρ → Measurable p → (∀ᵐ x ∂ρ, ‖p x‖ = 1) →
    LocalRows Ω ρ p β q → ∀ U K : Set (V d),
    IsOpen U → IsCompact K → U ⊆ interior K → K ⊆ Ω →
    HasRectMeasureDivergenceOn ((ρ.restrict K).withDensityᵥ p)
      (fun i => ((β i).restrict K).withDensityᵥ (q i)) U

/--
The full first order equation on interior tests, with a zeroth order term, locally finite source
masses concentrated on the domain, and measurable source densities bounded in absolute value by one
almost everywhere.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Section 2.1.
-/
def LocalFirstOrderEquation {d m n : ℕ} (Ω : Set (V d))
    (ρ : Measure (V d)) (p : V d → V m)
    (A₀ : V m →L[ℝ] V n) (A : Fin d → V m →L[ℝ] V n)
    (β : Fin n → Measure (V d)) (q : Fin n → V d → ℝ) : Prop :=
  (∀ a, LocalMass Ω (β a)) ∧ (∀ a, Measurable (q a)) ∧
    (∀ a, ∀ᵐ x ∂β a, |q a x| ≤ 1) ∧
    ∀ a (φ : ScalarCurrentTest d), tsupport (φ : V d → ℝ) ⊆ Ω →
      (∫ x, φ x * A₀ (p x) a ∂ρ) -
        (∑ j, ∫ x, fderiv ℝ (φ : V d → ℝ) x
          (WithLp.toLp 2 (Pi.single j (1 : ℝ))) * A j (p x) a ∂ρ) =
        ∫ x, φ x * q a x ∂β a

/--
The first order transport contract: restricting a local unit-density mass and its sources to an
interior compact set preserves the full equation on an open subset of its interior.
-/
def TargetFirstOrderEquationFinitePiece : Prop :=
  ∀ (d m n : ℕ) (Ω : Set (V d)) (ρ : Measure (V d)) (p : V d → V m)
    (A₀ : V m →L[ℝ] V n) (A : Fin d → V m →L[ℝ] V n)
    (β : Fin n → Measure (V d)) (q : Fin n → V d → ℝ),
    IsOpen Ω → LocalMass Ω ρ → Measurable p → (∀ᵐ x ∂ρ, ‖p x‖ = 1) →
    LocalFirstOrderEquation Ω ρ p A₀ A β q → ∀ U K : Set (V d),
    IsOpen U → IsCompact K → U ⊆ interior K → K ⊆ Ω →
    EquationOneOn ((ρ.restrict K).withDensityᵥ p) A₀ A
      (fun a => ((β a).restrict K).withDensityᵥ (q a)) U

/--
The local first order contract in positive spatial dimension: a measurable unit density lies in the
unit-frequency wave cone almost everywhere for the restricted singular mass, under the full local
equation.

This extends the printed Theorem 1.1 of De Philippis–Rindler (2016) to locally finite masses,
following the method of De Philippis–Rindler. The printed vector measures are finite under Section
2.1. The zeroth order term remains in the equation.

Source: De Philippis–Rindler (2016), Theorem 1.1 and Section 2.1.
-/
def TargetA4Local : Prop :=
  ∀ (d m n : ℕ), 0 < d → ∀ (Ω : Set (V d)), IsOpen Ω →
    ∀ (ρ : Measure (V d)) (p : V d → V m),
    LocalMass Ω ρ → Measurable p → (∀ᵐ x ∂ρ, ‖p x‖ = 1) →
    ∀ (A₀ : V m →L[ℝ] V n) (A : Fin d → V m →L[ℝ] V n)
      (β : Fin n → Measure (V d)) (q : Fin n → V d → ℝ),
    LocalFirstOrderEquation Ω ρ p A₀ A β q →
    ∀ᵐ x ∂(ρ.singularPart volume).restrict Ω, p x ∈ waveOne A

/--
The domination contract: domination on a domain restricts to nested measurable pieces without a
finiteness assumption on the dominated measure.
-/
def TargetDominationFinitePiece : Prop :=
  ∀ (d : ℕ) (ν ρ : Measure (V d)) (Ω U K : Set (V d)),
    MeasurableSet U → MeasurableSet K → U ⊆ K → K ⊆ Ω →
    ν.restrict Ω ≪ ρ → ν.restrict U ≪ ρ.restrict K


/-! The first part constructs the cover and derives sigma finiteness. -/

/--
Every open Euclidean domain has a countable open cover subordinate to compact interior pieces,
including the empty domain.
-/
theorem targetCover : TargetCover := by
  intro d Ω hΩ
  letI := hΩ.locallyCompactSpace
  let C : CompactExhaustion Ω := CompactExhaustion.choice Ω
  let K : ℕ → Set (V d) := fun j => Subtype.val '' C (j + 1)
  let U : ℕ → Set (V d) := fun j => Subtype.val '' interior (C (j + 1))
  have hU : ∀ j, IsOpen (U j) := fun j => hΩ.isOpenMap_subtype_val _ isOpen_interior
  have hUK : ∀ j, U j ⊆ K j := fun j => image_mono interior_subset
  have hKΩ : ∀ j, K j ⊆ Ω := by
    rintro j x ⟨y, _, rfl⟩
    exact y.property
  refine ⟨U, K, fun j => ⟨hU j, (C.isCompact _).image continuous_subtype_val,
    (hU j).subset_interior_iff.mpr (hUK j), hKΩ j⟩, ?_⟩
  apply Subset.antisymm
  · exact iUnion_subset (fun j => (hUK j).trans (hKΩ j))
  · intro x hx
    have hc : (⟨x, hx⟩ : Ω) ∈ ⋃ j, C j := by rw [C.iUnion_eq]; trivial
    obtain ⟨j, hj⟩ := mem_iUnion.mp hc
    exact mem_iUnion.mpr ⟨j, ⟨⟨x, hx⟩, C.subset_interior_succ j hj, rfl⟩⟩

/--
Concentration on an open domain and finiteness on its compact subsets imply sigma-finiteness of the
ambient mass.
-/
theorem targetSigmaFinite : TargetSigmaFinite := by
  intro d Ω hΩ ρ hρ
  obtain ⟨U, K, hK, hcover⟩ := targetCover d Ω hΩ
  let S : ℕ → Set (V d) := fun j => K j ∪ Ωᶜ
  apply Measure.sigmaFinite_of_countable (countable_range S)
  · rintro _ ⟨j, rfl⟩
    exact (measure_union_le _ _).trans_lt (by
      simpa only [hρ.1, add_zero] using hρ.2 (K j) (hK j).2.1 (hK j).2.2.2)
  · rw [sUnion_range]
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ Ω
    · have hxU : x ∈ ⋃ j, U j := hcover.symm ▸ hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxU
      exact mem_iUnion.mpr ⟨j, Or.inl (interior_subset ((hK j).2.2.1 hj))⟩
    · exact mem_iUnion.mpr ⟨0, Or.inr hx⟩

/-! The second part retains the original density on every finite piece. -/

/-- The restriction of a local mass to a compact subset of its domain is finite. -/
theorem LocalMass.isFiniteMeasure_restrict {d : ℕ} {Ω : Set (V d)}
    {ρ : Measure (V d)} (hρ : LocalMass Ω ρ) {K : Set (V d)}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) : IsFiniteMeasure (ρ.restrict K) :=
  MeasureTheory.isFiniteMeasure_restrict.mpr (hρ.2 K hK hKΩ).ne

/--
A measurable density bounded almost everywhere is integrable against the restriction of a local
mass to a compact interior piece.
-/
theorem LocalMass.integrable_restrict_of_bound {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Ω : Set (V d)} {ρ : Measure (V d)} (hρ : LocalMass Ω ρ)
    {p : V d → E} (hp : Measurable p) {C : ℝ} (hn : ∀ᵐ x ∂ρ, ‖p x‖ ≤ C)
    {K : Set (V d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    Integrable p (ρ.restrict K) := by
  letI := hρ.isFiniteMeasure_restrict hK hKΩ
  exact Integrable.of_bound hp.aestronglyMeasurable C
    ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le hn)

/--
A measurable unit density is integrable on compact interior pieces, gives exact variation, and
agrees with the vector-measure polar almost everywhere for the restricted mass.
-/
theorem LocalMass.finiteUnitPiece {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {Ω : Set (V d)} {ρ : Measure (V d)} (hρ : LocalMass Ω ρ)
    {p : V d → E} (hp : Measurable p) (hn : ∀ᵐ x ∂ρ, ‖p x‖ = 1)
    {K : Set (V d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    Integrable p (ρ.restrict K) ∧
      ((ρ.restrict K).withDensityᵥ p).variation = ρ.restrict K ∧
      VectorMeasure.polar ((ρ.restrict K).withDensityᵥ p) =ᵐ[ρ.restrict K] p := by
  have hi := hρ.integrable_restrict_of_bound hp (hn.mono fun _ hx => hx.le) hK hKΩ
  have hnK := (Measure.absolutelyContinuous_of_le
    (Measure.restrict_le_self (μ := ρ) (s := K))).ae_le hn
  have hv : ((ρ.restrict K).withDensityᵥ p).variation = ρ.restrict K := by
    rw [Measure.variation_withDensityᵥ hi]
    have he : (fun x => ‖p x‖ₑ) =ᵐ[ρ.restrict K] (fun _ => (1 : ℝ≥0∞)) := by
      filter_upwards [hnK] with x hx
      simp [← ofReal_norm, hx]
    simpa using withDensity_congr_ae he
  refine ⟨hi, hv, ?_⟩
  have hrep : ((ρ.restrict K).withDensityᵥ p).variation.withDensityᵥ p =
      (ρ.restrict K).withDensityᵥ p := by rw [hv]
  have hi' : Integrable p ((ρ.restrict K).withDensityᵥ p).variation := hv.symm ▸ hi
  simpa only [hv] using VectorMeasure.polar_ae_eq_of_withDensity_eq _ hi' hrep

/--
A rectangular measurable unit density of a local mass is integrable on each compact interior piece,
and its vector measure has exactly the restricted mass as variation.
-/
theorem targetFinitePiece : TargetFinitePiece := by
  intro r d Ω ρ p hρ hp hn K hK hKΩ
  obtain ⟨hi, hv, _⟩ := hρ.finiteUnitPiece hp hn hK hKΩ
  exact ⟨hi, hv⟩

/--
On each compact interior piece, a measurable unit density is integrable, gives exact variation, and
agrees almost everywhere with both polar conventions.
-/
theorem targetPolarFinitePiece : TargetPolarFinitePiece := by
  intro d m Ω ρ p hρ hp hn K hK hKΩ
  obtain ⟨hi, hv, hpol⟩ := hρ.finiteUnitPiece hp hn hK hKΩ
  refine ⟨hi, hv, hpol, ?_⟩
  have he := VectorMeasure.polar_ae_eq_polarDensity ((ρ.restrict K).withDensityᵥ p)
  rw [hv] at he
  exact he.symm.trans hpol

/--
A measurable density bounded almost everywhere and supported in an interior compact set is
integrable against the local mass.
-/
theorem LocalMass.integrable_of_support_subset {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Ω : Set (V d)} {ρ : Measure (V d)} (hρ : LocalMass Ω ρ)
    {f : V d → E} (hf : Measurable f) {C : ℝ} (hn : ∀ᵐ x ∂ρ, ‖f x‖ ≤ C)
    {K : Set (V d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hs : Function.support f ⊆ K) :
    Integrable f ρ :=
  (integrableOn_iff_integrable_of_support_subset hs).mp
    (hρ.integrable_restrict_of_bound hf hn hK hKΩ)

/--
The product of an interior scalar test and a measurable density bounded almost everywhere is
integrable against a local mass.
-/
theorem LocalMass.integrable_test_mul {d : ℕ} {Ω : Set (V d)} {ρ : Measure (V d)}
    (hρ : LocalMass Ω ρ) {q : V d → ℝ} (hq : Measurable q)
    {C : ℝ} (hn : ∀ᵐ x ∂ρ, ‖q x‖ ≤ C) (φ : ScalarCurrentTest d)
    (hφ : tsupport (φ : V d → ℝ) ⊆ Ω) : Integrable (fun x => φ x * q x) ρ := by
  let b : BoundedContinuousFunction (V d) ℝ := φ
  refine hρ.integrable_of_support_subset (b.continuous.measurable.mul hq)
    (C := ‖b‖ * C) ?_ φ.hasCompactSupport.isCompact hφ ?_
  · filter_upwards [hn] with x hx
    exact (norm_mul (φ x) (q x)).le.trans
      (mul_le_mul (b.norm_coe_le_norm x) hx (norm_nonneg _) (norm_nonneg _))
  · intro x hx
    by_contra h
    exact hx (by simp [image_eq_zero_of_notMem_tsupport h])

/--
The derivative of an interior scalar test paired with a measurable vector density bounded almost
everywhere is integrable against a local mass.
-/
theorem LocalMass.integrable_fderiv_apply {d : ℕ} {Ω : Set (V d)} {ρ : Measure (V d)}
    (hρ : LocalMass Ω ρ) {v : V d → V d} (hv : Measurable v)
    {C : ℝ} (hn : ∀ᵐ x ∂ρ, ‖v x‖ ≤ C) (φ : ScalarCurrentTest d)
    (hφ : tsupport (φ : V d → ℝ) ⊆ Ω) :
    Integrable (fun x => fderiv ℝ (φ : V d → ℝ) x (v x)) ρ := by
  let b : BoundedCovectorField d d := currentTestDerivative φ
  have hb (x : V d) : b x = fderiv ℝ (φ : V d → ℝ) x :=
    congrFun (currentTestDerivative_apply φ) x
  have hm : Measurable (fun x => b x (v x)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      (b.continuous.measurable.prodMk hv)
  simp_rw [hb] at hm
  refine hρ.integrable_of_support_subset hm (C := ‖b‖ * C) ?_
    φ.hasCompactSupport.isCompact hφ ?_
  · filter_upwards [hn] with x hx
    change ‖b x (v x)‖ ≤ _
    exact ((b x).le_opNorm (v x)).trans
      (mul_le_mul (b.norm_coe_le_norm x) hx (norm_nonneg _)
        ((norm_nonneg (b x)).trans (b.norm_coe_le_norm x)))
  · intro x hx
    by_contra h
    have hz : fderiv ℝ (φ : V d → ℝ) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => h (tsupport_fderiv_subset ℝ ht))
    exact hx (by simp [hz])

end GeometricMeasure.LocalStructureContracts
