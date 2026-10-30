import ErrorCalculus.Dirichlet.WienerEnergy
import ErrorCalculus.Dirichlet.ProductDensityOU

noncomputable section
open MeasureTheory Filter Topology

namespace ErrorCalculus

/-- Compatibility of the initial-segment and product-block projections. -/
theorem projLE_eq_prodProj₁ (K L : ℕ) : projLE (Nat.le_add_right K L) = prodProj₁ K L := by
  ext x i
  rfl

/-- Linear insertion into the first block. -/
def appendLeft (K L : ℕ) : (Fin K → ℝ) →L[ℝ] (Fin (K+L) → ℝ) :=
  ContinuousLinearMap.pi fun j => Fin.addCases
    (fun i => ContinuousLinearMap.proj i) (fun _ => 0) j

@[simp] theorem appendLeft_apply (K L : ℕ) (x : Fin K → ℝ) :
    appendLeft K L x = Fin.append x 0 := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [appendLeft]

theorem appendLeft_single {K L : ℕ} (i : Fin K) :
    appendLeft K L (Pi.single i 1) = Pi.single (Fin.castAdd L i) 1 := by
  ext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [Pi.single_apply]
  · have hne : Fin.natAdd K j ≠ Fin.castAdd L i := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    simp [hne]

theorem append_section_eq {K L : ℕ} (x : Fin K → ℝ) (y : Fin L → ℝ) :
    Fin.append x y = appendLeft K L x + Fin.append 0 y := by
  ext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

theorem contDiff_append_section {K L : ℕ} (y : Fin L → ℝ) :
    ContDiff ℝ 1 (fun x : Fin K → ℝ => Fin.append x y) := by
  have he : (fun x : Fin K → ℝ => Fin.append x y) =
      fun x => appendLeft K L x + Fin.append 0 y := funext fun x => append_section_eq x y
  rw [he]
  exact (appendLeft K L).contDiff.add contDiff_const

/-- The derivative of a section is the corresponding derivative before slicing. -/
theorem partial_append_section {K L : ℕ} {f : (Fin (K+L) → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin K) (x : Fin K → ℝ) (y : Fin L → ℝ) :
    fderiv ℝ (fun x => f (Fin.append x y)) x (Pi.single i 1) =
      fderiv ℝ f (Fin.append x y) (Pi.single (Fin.castAdd L i) 1) := by
  have hd : HasFDerivAt (fun x : Fin K → ℝ => Fin.append x y) (appendLeft K L) x := by
    simpa only [← append_section_eq] using (appendLeft K L).hasFDerivAt.add_const (Fin.append 0 y)
  change fderiv ℝ (f ∘ fun x => Fin.append x y) x _ = _
  rw [((hf.differentiable (by norm_num) _).hasFDerivAt.comp x hd).fderiv]
  simp only [ContinuousLinearMap.comp_apply, appendLeft_single]

/-- Finite-dimensional integration by parts written directly against the density measure. -/
theorem integral_partial_mul_testD {K : ℕ} (ρ : (Fin K → ℝ) → ℝ) [SmoothDensityD ρ]
    {f ψ : (Fin K → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (i : Fin K) :
    (∫ x, fderiv ℝ f x (Pi.single i 1) * ψ x ∂densityMeasureD ρ) =
      -(∫ x, f x * testChiD ρ i ψ x ∂densityMeasureD ρ) := by
  rw [integral_densityD, integral_densityD]
  convert integral_fderiv_mul_test i hf hψ hc (SmoothDensityD.contDiff (ρ := ρ)) using 1
  · congr 1; funext x; ring
  · congr 1; congr 1; funext x
    dsimp [testChiD]
    field_simp [(SmoothDensityD.pos (ρ := ρ) x).ne']

/-- Fubini with the test coordinates integrated first. -/
theorem integral_ou_add_symm {K L : ℕ} (f : (Fin (K+L) → ℝ) → ℝ)
    (hf : Integrable f (densityMeasureD (ouDensityD (K+L)))) :
    (∫ z, f z ∂densityMeasureD (ouDensityD (K+L))) =
      ∫ y, ∫ x, f (Fin.append x y) ∂densityMeasureD (ouDensityD K)
        ∂densityMeasureD (ouDensityD L) := by
  have hp : MeasurePreserving (appendEquivM K L)
      ((densityMeasureD (ouDensityD K)).prod (densityMeasureD (ouDensityD L)))
      (densityMeasureD (ouDensityD (K+L))) :=
    ⟨(appendEquivM K L).measurable, (ouDensityD_measure_add K L).symm⟩
  rw [← hp.integral_comp']
  simpa only [Function.comp_apply, appendEquivM_apply] using integral_prod_symm _
    ((hp.integrable_comp_emb (appendEquivM K L).measurableEmbedding).mpr hf)

/-- Product-level IBP; the lifted test need not have compact support in the unused coordinates. -/
theorem integral_ou_partial_test {K L : ℕ} {f : (Fin (K+L) → ℝ) → ℝ}
    (hf : IsC1BoundedD f) {ψ : (Fin K → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (i : Fin K) :
    (∫ z, fderiv ℝ f z (Pi.single (Fin.castAdd L i) 1) * ψ (prodProj₁ K L z)
      ∂densityMeasureD (ouDensityD (K+L))) =
    -(∫ z, f z * testChiD (ouDensityD K) i ψ (prodProj₁ K L z)
      ∂densityMeasureD (ouDensityD (K+L))) := by
  have hp : MeasurePreserving (prodProj₁ K L) (densityMeasureD (ouDensityD (K+L)))
      (densityMeasureD (ouDensityD K)) := by
    rw [← projLE_eq_prodProj₁]
    exact projLE_preserving _
  have ht : MemLp ψ 2 (densityMeasureD (ouDensityD K)) :=
    (isC1Bounded_of_hasCompactSupportD hψ hc).memLp _ _
  have hχ : MemLp (testChiD (ouDensityD K) i ψ) 2 (densityMeasureD (ouDensityD K)) :=
    (continuous_testChiD _ i hψ).memLp_of_hasCompactSupport (hasCompactSupport_testChiD _ i hc)
  have hl : Integrable (fun z => fderiv ℝ f z (Pi.single (Fin.castAdd L i) 1) *
      ψ (prodProj₁ K L z)) (densityMeasureD (ouDensityD (K+L))) :=
    (hf.partial_memLp (Fin.castAdd L i) _ 2).integrable_mul (ht.comp_measurePreserving hp)
  have hr : Integrable (fun z => f z * testChiD (ouDensityD K) i ψ (prodProj₁ K L z))
      (densityMeasureD (ouDensityD (K+L))) :=
    (hf.memLp _ 2).integrable_mul (hχ.comp_measurePreserving hp)
  rw [integral_ou_add_symm _ hl, integral_ou_add_symm _ hr,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [prodProj₁_append]
  simp_rw [← partial_append_section hf.1 i]
  exact integral_partial_mul_testD _ (hf.1.comp (contDiff_append_section y)) hψ hc i

/-- The L² realization of an ordinary compactly supported test. -/
def wienerTest {K : ℕ} (ψ : (Fin K → ℝ) → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) : Lp ℝ 2 wienerCoord :=
  cylLp K 2 (protoOfFunctionD (ouDensityD K) ψ (isC1Bounded_of_hasCompactSupportD hψ hc) : Lp ℝ 2 _)

/-- IBP at level K+L, after pulling both pairings to that level. -/
theorem inner_wienerPartial_test_add {K L : ℕ} (u : protoDomD (ouDensityD (K+L)))
    (i : Fin K) {ψ : (Fin K → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    inner ℝ (wienerPartial i.val (cylProto (K+L) u)) (wienerTest ψ hψ hc) =
      - inner ℝ (cylProto (K+L) u : Lp ℝ 2 wienerCoord)
        (cylLp K 2 (testChiLpD (ouDensityD K) i ψ hψ hc)) := by
  let h : K ≤ K+L := Nat.le_add_right K L
  rw [show i.val = (Fin.castAdd L i).val from rfl, wienerPartial_cyl]
  change inner ℝ (cylLp (K+L) 2 _) (cylLp K 2 _) =
    - inner ℝ (cylLp (K+L) 2 _) (cylLp K 2 _)
  rw [← cylLp_comp h 2, ← cylLp_comp h 2,
    (cylLp (K+L) 2).inner_map_map, (cylLp (K+L) 2).inner_map_map]
  have ht := (isC1Bounded_of_hasCompactSupportD hψ hc).memLp (densityMeasureD (ouDensityD K)) 2
  have hχ := (continuous_testChiD (ouDensityD K) i hψ).memLp_of_hasCompactSupport
    (μ := densityMeasureD (ouDensityD K)) (p := 2) (hasCompactSupport_testChiD _ i hc)
  have hl : inner ℝ (gradD _ (Fin.castAdd L i) u)
      (liftLp h 2 (protoOfFunctionD (ouDensityD K) ψ (isC1Bounded_of_hasCompactSupportD hψ hc) : Lp ℝ 2 _)) =
      ∫ z, fderiv ℝ (repD _ u) z (Pi.single (Fin.castAdd L i) 1) * ψ (prodProj₁ K L z)
        ∂densityMeasureD (ouDensityD (K+L)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_gradD _ (Fin.castAdd L i) u, coeFn_liftLp h 2 _,
      (projLE_preserving h).quasiMeasurePreserving.ae_eq_comp ht.coeFn_toLp] with z ha hb hd
    rw [ha, hb]
    change inner ℝ (fderiv ℝ (repD _ u) z (Pi.single (Fin.castAdd L i) 1))
      (ht.toLp ψ (projLE h z)) = _
    change ht.toLp ψ (projLE h z) = ψ (projLE h z) at hd
    rw [hd, real_inner_comm]
    rfl
  have hr : inner ℝ (u : Lp ℝ 2 _) (liftLp h 2 (testChiLpD (ouDensityD K) i ψ hψ hc)) =
      ∫ z, repD _ u z * testChiD (ouDensityD K) i ψ (prodProj₁ K L z)
        ∂densityMeasureD (ouDensityD (K+L)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_repD _ u, coeFn_liftLp h 2 _,
      (projLE_preserving h).quasiMeasurePreserving.ae_eq_comp hχ.coeFn_toLp] with z ha hb hd
    rw [ha, hb]
    change inner ℝ (repD _ u z) (hχ.toLp _ (projLE h z)) = _
    change hχ.toLp _ (projLE h z) = testChiD (ouDensityD K) i ψ (projLE h z) at hd
    rw [hd, real_inner_comm]
    rfl
  rw [hl, hr]
  exact integral_ou_partial_test (rep_isC1BoundedD _ u) hψ hc i

/-- IBP against any compact cylindrical test, independently of F's level. -/
theorem inner_wienerPartial_test (F : wienerDom) {K : ℕ} (i : Fin K)
    {ψ : (Fin K → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    inner ℝ (wienerPartial i.val F) (wienerTest ψ hψ hc) =
      - inner ℝ (F : Lp ℝ 2 wienerCoord) (cylLp K 2 (testChiLpD (ouDensityD K) i ψ hψ hc)) := by
  have h : level F ≤ K + level F := Nat.le_add_left _ _
  rw [← cylRepAt_spec F h]
  exact inner_wienerPartial_test_add _ i hψ hc

end ErrorCalculus
