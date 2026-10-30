import GeometricMeasure.Current.LocalMass

/-!
# Local Structure

## Main results
Local equations, singular restriction, gluing and the three locally finite conclusions.

Following the method of De Philippis–Rindler (2016), Theorem 1.1, Corollaries 1.12 and 1.13, and
Section 2.1. The local heads extend the printed finite vector-measure statements to locally finite
masses. The controls are compiled separately from the library aggregator.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

namespace GeometricMeasure.LocalStructureContracts

/-! Interior tests transport the equations without differentiating a characteristic function. -/

/--
A scalar test supported in the restriction set has the same density integral before and after
restriction, for an arbitrary density.
-/
theorem integral_restrict_test_mul {d : ℕ} (μ : Measure (V d))
    (φ : ScalarCurrentTest d) (q : V d → ℝ) {K : Set (V d)}
    (hφ : tsupport (φ : V d → ℝ) ⊆ K) :
    (∫ x, φ x * q x ∂μ.restrict K) = ∫ x, φ x * q x ∂μ := by
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards with x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ h)), zero_mul]

/-- The derivative of a scalar test vanishes outside any set containing its closed support. -/
theorem fderiv_test_eq_zero_off {d : ℕ} (φ : ScalarCurrentTest d)
    {K : Set (V d)} (hφ : tsupport (φ : V d → ℝ) ⊆ K) {x : V d}
    (hx : x ∉ K) : fderiv ℝ (φ : V d → ℝ) x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (hφ (tsupport_fderiv_subset ℝ h)))

/--
A derivative test against an arbitrary vector density has the same integral before and after
restriction to a set containing the closed support of the test.
-/
theorem integral_restrict_fderiv_apply {d : ℕ} (μ : Measure (V d))
    (φ : ScalarCurrentTest d) (v : V d → V d) {K : Set (V d)}
    (hφ : tsupport (φ : V d → ℝ) ⊆ K) :
    (∫ x, fderiv ℝ (φ : V d → ℝ) x (v x) ∂μ.restrict K) =
      ∫ x, fderiv ℝ (φ : V d → ℝ) x (v x) ∂μ := by
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards with x hx
  rw [fderiv_test_eq_zero_off φ hφ hx]
  rfl

/--
A derivative test in a fixed direction multiplied by an arbitrary scalar density has the same
integral before and after restriction to a set containing the closed support of the test.
-/
theorem integral_restrict_fderiv_mul {d : ℕ} (μ : Measure (V d))
    (φ : ScalarCurrentTest d) (e : V d) (q : V d → ℝ) {K : Set (V d)}
    (hφ : tsupport (φ : V d → ℝ) ⊆ K) :
    (∫ x, fderiv ℝ (φ : V d → ℝ) x e * q x ∂μ.restrict K) =
      ∫ x, fderiv ℝ (φ : V d → ℝ) x e * q x ∂μ := by
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards with x hx
  simp [fderiv_test_eq_zero_off φ hφ hx]

/-- An integrable signed density acts on scalar tests by the ordinary density integral. -/
theorem signedTestCurrent_withDensity {d : ℕ} (μ : Measure (V d))
    {q : V d → ℝ} (hq : Integrable q μ) (φ : ScalarCurrentTest d) :
    signedTestCurrent (μ.withDensityᵥ q) φ = ∫ x, φ x * q x ∂μ := by
  rw [← signedMeasurePairing_currentTest, signedMeasurePairing_density _ _ hq]
  rfl

/-- The boundary of the current of an integrable vector density is the derivative pairing. -/
theorem boundary_withDensity {d : ℕ} (μ : Measure (V d))
    {v : V d → V d} (hv : Integrable v μ) (φ : ScalarCurrentTest d) :
    oneCurrentBoundary (measureOneCurrent (μ.withDensityᵥ v)) φ =
      ∫ x, fderiv ℝ (φ : V d → ℝ) x (v x) ∂μ := by
  rw [oneCurrentBoundary_apply, ← vectorMeasurePairing_currentTest,
    vectorMeasurePairing_withDensityᵥ _ hv]
  rfl

/--
A local vector divergence equation restricts to a smaller domain inside the restriction set, when
both restricted densities are integrable.
-/
theorem hasMeasureDivergenceOn_finitePiece {d : ℕ} {Ω U K : Set (V d)}
    {ρ β : Measure (V d)} {v : V d → V d} {q : V d → ℝ}
    (hv : Integrable v (ρ.restrict K)) (hq : Integrable q (β.restrict K))
    (hUK : U ⊆ K) (hKΩ : K ⊆ Ω)
    (heq : ∀ φ : ScalarCurrentTest d, tsupport (φ : V d → ℝ) ⊆ Ω →
      (∫ x, φ x * q x ∂β) = -(∫ x, fderiv ℝ (φ : V d → ℝ) x (v x) ∂ρ)) :
    HasMeasureDivergenceOn ((ρ.restrict K).withDensityᵥ v)
      ((β.restrict K).withDensityᵥ q) U := by
  intro φ hφ
  rw [signedTestCurrent_withDensity _ hq, boundary_withDensity _ hv,
    integral_restrict_test_mul _ _ _ (hφ.trans hUK),
    integral_restrict_fderiv_apply _ _ _ (hφ.trans hUK)]
  exact heq φ (hφ.trans (hUK.trans hKΩ))

/-- Taking a rectangular row commutes with forming the vector measure of an integrable density. -/
theorem rectRow_withDensity {r d : ℕ} (μ : Measure (V d))
    {p : V d → RectMatrixSpace r d} (hp : Integrable p μ) (i : Fin r) :
    VectorMeasure.rectRow (μ.withDensityᵥ p) i =
      μ.withDensityᵥ (fun x => RectMatrixSpace.row i (p x)) := by
  unfold VectorMeasure.rectRow VectorMeasure.linearImage
  exact withDensityᵥ_mapRange μ hp (RectMatrixSpace.row i)

/--
The local row equations survive compact restriction on every open subset of the compact interior.
-/
theorem targetRowEquationFinitePiece : TargetRowEquationFinitePiece := by
  intro r d Ω ρ p β q _hΩ hρ hp hn hrows U K _hU hK hUK hKΩ i
  have hi := (hρ.finiteUnitPiece hp hn hK hKΩ).1
  have hq := (hrows.1 i).integrable_restrict_of_bound (hrows.2.1 i)
    (by simpa only [Real.norm_eq_abs] using hrows.2.2.1 i) hK hKΩ
  rw [rectRow_withDensity _ hi]
  exact hasMeasureDivergenceOn_finitePiece ((RectMatrixSpace.row i).integrable_comp hi)
    hq (hUK.trans interior_subset) hKΩ (hrows.2.2.2 i)

/--
The full local first order equation, including its zeroth order term, survives compact restriction
on every open subset of the compact interior.
-/
theorem targetFirstOrderEquationFinitePiece : TargetFirstOrderEquationFinitePiece := by
  intro d m n Ω ρ p A₀ A β q _hΩ hρ hp hn heq U K _hU hK hUK hKΩ
  obtain ⟨_, hv, _, hpol⟩ := targetPolarFinitePiece d m Ω ρ p hρ hp hn K hK hKΩ
  intro a φ hφ
  have hs : tsupport (φ : V d → ℝ) ⊆ K := hφ.trans (hUK.trans interior_subset)
  have hq := (heq.1 a).integrable_restrict_of_bound (heq.2.1 a)
    (by simpa only [Real.norm_eq_abs] using heq.2.2.1 a) hK hKΩ
  rw [hv, signedTestCurrent_withDensity _ hq,
    integral_restrict_test_mul (β a) φ (q a) hs]
  have hzero : (∫ x, φ x * A₀ (polarDensity ((ρ.restrict K).withDensityᵥ p) x) a
      ∂ρ.restrict K) = ∫ x, φ x * A₀ (p x) a ∂ρ := by
    rw [← integral_restrict_test_mul ρ φ (fun x => A₀ (p x) a) hs]
    apply integral_congr_ae
    filter_upwards [hpol] with x hx
    rw [hx]
  have hprincipal (j : Fin d) :
      (∫ x, fderiv ℝ (φ : V d → ℝ) x (WithLp.toLp 2 (Pi.single j (1 : ℝ))) *
        A j (polarDensity ((ρ.restrict K).withDensityᵥ p) x) a ∂ρ.restrict K) =
      ∫ x, fderiv ℝ (φ : V d → ℝ) x (WithLp.toLp 2 (Pi.single j (1 : ℝ))) *
        A j (p x) a ∂ρ := by
    rw [← integral_restrict_fderiv_mul ρ φ _ (fun x => A j (p x) a) hs]
    apply integral_congr_ae
    filter_upwards [hpol] with x hx
    rw [hx]
  rw [hzero]
  simp_rw [hprincipal]
  exact heq.2.2.2 a φ (hs.trans hKΩ)

/--
Domination on a domain restricts to nested measurable pieces without any finiteness assumption on
the dominated measure.
-/
theorem targetDominationFinitePiece : TargetDominationFinitePiece := by
  intro d ν ρ Ω U K _hU hK hUK hKΩ hν
  have hνU : ν.restrict U ≪ ρ :=
    (Measure.absolutelyContinuous_of_le (Measure.restrict_mono_set ν (hUK.trans hKΩ))).trans hν
  have hr := hνU.restrict K
  rw [Measure.restrict_restrict hK, inter_eq_right.mpr hUK] at hr
  exact hr

/-! Singular restriction and countable gluing complete the local infrastructure. -/

/--
For a sigma-finite mass, singular parts relative to volume commute with measurable restriction.
-/
theorem targetSingularRestriction : TargetSingularRestriction := by
  intro d ρ hρ U hU
  letI := hρ
  exact ρ.singularPart_restrict volume hU

/--
Countably many almost everywhere conclusions glue on a covered measurable domain for an arbitrary
positive measure and an arbitrary predicate.
-/
theorem targetGlue : TargetGlue := by
  intro d ρ Ω U P hΩ hU hcover hlocal
  apply (ae_restrict_iff' hΩ).mpr
  have hall : ∀ᵐ x ∂ρ, ∀ j, x ∈ U j → P x :=
    ae_all_iff.mpr (fun j => (ae_restrict_iff' (hU j)).mp (hlocal j))
  filter_upwards [hall] with x hx hxΩ
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hxΩ)
  exact hx j hj

/-! The final heads apply the finite theorems and glue their conclusions. -/

/-- The first order contract is equivalent to the finite local equation. -/
theorem equationOneOn_iff_hasEquationOn {d m n : ℕ}
    (M : VectorMeasure (V d) (V m)) (A₀ : V m →L[ℝ] V n)
    (A : Fin d → V m →L[ℝ] V n) (σ : Fin n → SignedMeasure (V d)) (U : Set (V d)) :
    EquationOneOn M A₀ A σ U ↔
      (⟨A, A₀⟩ : FirstOrderOperator d m n).HasEquationOn M σ U := Iff.rfl

/--
The finite first order equation implies that the polar density lies in the unit-frequency wave cone
almost everywhere for the restricted singular variation, in positive spatial dimension.

Following the method of De Philippis–Rindler (2016), Theorem 1.1 and Section 2.1.
-/
theorem targetA4 : TargetA4 := by
  intro d m n hd M A₀ A σ U hU heq
  letI : NeZero d := ⟨hd.ne'⟩
  exact FirstOrderOperator.HasEquationOn.ae_polarDensity_symbol_eq_zero
    (⟨A, A₀⟩ : FirstOrderOperator d m n) M hU heq

/--
A finite family with local divergences, domination by each variation and almost everywhere spanning
forces absolute continuity of the restricted arbitrary positive measure.

Following the method of De Philippis–Rindler (2016), Corollary 1.12 and Section 2.1.
-/
theorem targetA5Finite : TargetA5Finite := by
  intro r d R D U hU hdiv ν hν hspan
  exact restrict_absolutelyContinuous_volume_of_finite_span_polar_on R D hU hdiv ν hν hspan

/--
For a local mass on an open domain, taking the singular part after measurable restriction and then
restricting to a subset agrees with directly restricting the original singular part.
-/
theorem LocalMass.singularPart_restrict_restrict {d : ℕ} {Ω : Set (V d)}
    {ρ : Measure (V d)} (hρ : LocalMass Ω ρ) (hΩ : IsOpen Ω)
    {U K : Set (V d)} (hK : MeasurableSet K) (hUK : U ⊆ K) :
    ((ρ.restrict K).singularPart volume).restrict U =
      (ρ.singularPart volume).restrict U := by
  rw [targetSingularRestriction d ρ (targetSigmaFinite d Ω hΩ ρ hρ) K hK,
    Measure.restrict_restrict_of_subset hUK]

/--
A rectangular measurable unit density satisfying the local row equations has rank at most d - 1
almost everywhere for the singular mass restricted to the open domain.

This extends the printed Corollary 1.13 of De Philippis–Rindler (2016) to locally finite masses,
following the method of De Philippis–Rindler. The printed vector measures are finite under Section
2.1. The matrix values may be rectangular.

Source: De Philippis–Rindler (2016), Corollary 1.13 and Section 2.1.
-/
theorem targetA3 : TargetA3 := by
  intro r d Ω hΩ ρ p hρ hp hn β q hrows
  obtain ⟨U, K, hK, hcover⟩ := targetCover d Ω hΩ
  apply targetGlue d (ρ.singularPart volume) Ω U _ hΩ.measurableSet
    (fun j => (hK j).1.measurableSet) hcover.ge
  intro j
  have hdiv := targetRowEquationFinitePiece r d Ω ρ p β q hΩ hρ hp hn hrows
    (U j) (K j) (hK j).1 (hK j).2.1 (hK j).2.2.1 (hK j).2.2.2
  obtain ⟨_, hv, hpol⟩ := hρ.finiteUnitPiece hp hn (hK j).2.1 (hK j).2.2.2
  have hs := HasRectMeasureDivergenceOn.ae_rank_polar_le _ _ (hK j).1 hdiv
  rw [hv] at hs
  have he := (Measure.absolutelyContinuous_of_le
    ((Measure.restrict_le_self (s := U j)).trans
      ((ρ.restrict (K j)).singularPart_le volume))).ae_le hpol
  have ht : ∀ᵐ x ∂((ρ.restrict (K j)).singularPart volume).restrict (U j),
      Matrix.rank (fun i k => p x (i, k) : Matrix (Fin r) (Fin d) ℝ) ≤ d - 1 := by
    filter_upwards [hs, he] with x hx hpx
    rw [hpx] at hx
    exact hx
  rwa [hρ.singularPart_restrict_restrict hΩ (hK j).2.1.measurableSet
    ((hK j).2.2.1.trans interior_subset)] at ht

/--
For a local mass in positive spatial dimension, the full first order equation places its measurable
unit density in the unit-frequency wave cone almost everywhere for the restricted singular mass.

This extends the printed Theorem 1.1 of De Philippis–Rindler (2016) to locally finite masses,
following the method of De Philippis–Rindler. The printed vector measures are finite under Section
2.1. The zeroth order term remains in the equation.

Source: De Philippis–Rindler (2016), Theorem 1.1 and Section 2.1.
-/
theorem targetA4Local : TargetA4Local := by
  intro d m n hd Ω hΩ ρ p hρ hp hn A₀ A β q heq
  obtain ⟨U, K, hK, hcover⟩ := targetCover d Ω hΩ
  apply targetGlue d (ρ.singularPart volume) Ω U _ hΩ.measurableSet
    (fun j => (hK j).1.measurableSet) hcover.ge
  intro j
  have hfinite := targetFirstOrderEquationFinitePiece d m n Ω ρ p A₀ A β q
    hΩ hρ hp hn heq (U j) (K j) (hK j).1 (hK j).2.1 (hK j).2.2.1 (hK j).2.2.2
  obtain ⟨_, hv, _, hpol⟩ := targetPolarFinitePiece d m Ω ρ p hρ hp hn
    (K j) (hK j).2.1 (hK j).2.2.2
  have hs := targetA4 d m n hd _ A₀ A _ (U j) (hK j).1 hfinite
  rw [hv] at hs
  have he := (Measure.absolutelyContinuous_of_le
    ((Measure.restrict_le_self (s := U j)).trans
      ((ρ.restrict (K j)).singularPart_le volume))).ae_le hpol
  have ht : ∀ᵐ x ∂((ρ.restrict (K j)).singularPart volume).restrict (U j),
      p x ∈ waveOne A := by
    filter_upwards [hs, he] with x hx hpx
    simpa only [hpx] using hx
  rwa [hρ.singularPart_restrict_restrict hΩ (hK j).2.1.measurableSet
    ((hK j).2.2.1.trans interior_subset)] at ht

/--
Absolute continuity on a countable measurable cover glues on a measurable domain for arbitrary
positive measures.
-/
theorem absolutelyContinuous_restrict_of_cover {d : ℕ} (ν μ : Measure (V d))
    {Ω : Set (V d)} {U : ℕ → Set (V d)} (hΩ : MeasurableSet Ω)
    (hU : ∀ j, MeasurableSet (U j)) (hcover : Ω ⊆ ⋃ j, U j)
    (hlocal : ∀ j, ν.restrict (U j) ≪ μ) : ν.restrict Ω ≪ μ := by
  intro s hs
  have hnull : ∀ j, ∀ᵐ x ∂ν.restrict (U j), x ∉ s := by
    intro j
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using hlocal j hs
  have h := targetGlue d ν Ω U (fun x => x ∉ s) hΩ hU hcover hnull
  simpa only [ae_iff, not_not, Set.setOf_mem_eq] using h

/--
A finite family of locally finite masses with measurable unit densities and local divergences forces
absolute continuity of an arbitrary positive measure restricted to the open domain, under domination
and almost everywhere spanning.

This extends the printed Corollary 1.12 of De Philippis–Rindler (2016) to locally finite masses,
following the method of De Philippis–Rindler. The printed vector measures are finite under Section
2.1. The dominated positive measure may be arbitrary.

Source: De Philippis–Rindler (2016), Corollary 1.12 and Section 2.1.
-/
theorem targetA5Local : TargetA5Local := by
  intro r d Ω hΩ ρ τ hρ hτ hn β q hβ hq hqn heq ν hν hspan
  obtain ⟨U, K, hK, hcover⟩ := targetCover d Ω hΩ
  apply absolutelyContinuous_restrict_of_cover ν volume hΩ.measurableSet
    (fun j => (hK j).1.measurableSet) hcover.ge
  intro j
  let R : Fin r → VectorMeasure (V d) (V d) :=
    fun i => ((ρ i).restrict (K j)).withDensityᵥ (τ i)
  let D : Fin r → SignedMeasure (V d) :=
    fun i => ((β i).restrict (K j)).withDensityᵥ (q i)
  have hpieces (i : Fin r) := targetPolarFinitePiece d d Ω (ρ i) (τ i)
    (hρ i) (hτ i) (hn i) (K j) (hK j).2.1 (hK j).2.2.2
  have hUK : U j ⊆ K j := (hK j).2.2.1.trans interior_subset
  have hνj : ∀ i, ν.restrict (U j) ≪ (R i).variation := by
    intro i
    change ν.restrict (U j) ≪ (((ρ i).restrict (K j)).withDensityᵥ (τ i)).variation
    rw [(hpieces i).2.1]
    exact targetDominationFinitePiece d ν (ρ i) Ω (U j) (K j)
      (hK j).1.measurableSet (hK j).2.1.measurableSet hUK (hK j).2.2.2 (hν i)
  have hdiv : ∀ i, HasMeasureDivergenceOn (R i) (D i) (U j) := by
    intro i
    have hqi := (hβ i).integrable_restrict_of_bound (hq i)
      (by simpa only [Real.norm_eq_abs] using hqn i) (hK j).2.1 (hK j).2.2.2
    exact hasMeasureDivergenceOn_finitePiece (hpieces i).1 hqi hUK (hK j).2.2.2 (heq i)
  have hpν : ∀ᵐ x ∂ν.restrict (U j), ∀ i, polarDensity (R i) x = τ i x := by
    apply ae_all_iff.mpr
    intro i
    apply (hνj i).ae_le
    change polarDensity (((ρ i).restrict (K j)).withDensityᵥ (τ i)) =ᵐ[
      (((ρ i).restrict (K j)).withDensityᵥ (τ i)).variation] τ i
    rw [(hpieces i).2.1]
    exact (hpieces i).2.2.2
  have hspanj := (Measure.absolutelyContinuous_of_le
    (Measure.restrict_mono_set ν (hUK.trans (hK j).2.2.2))).ae_le hspan
  apply restrict_absolutelyContinuous_volume_of_finite_span_polar_on R D (hK j).1 hdiv ν hνj
  filter_upwards [hspanj, hpν] with x hx hpx
  simpa only [hpx] using hx

end GeometricMeasure.LocalStructureContracts
