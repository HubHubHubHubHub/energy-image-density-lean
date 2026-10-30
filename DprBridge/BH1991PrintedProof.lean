import DprBridge.BH1991ChainCurrents

/-!
# Energy image density on the original BH measure

## Main results
The printed Bouleau–Hirsch EID conjecture is proved following the normal-current method of
Eriksson-Bique–Murugan (Section 4.2, Remark 4.12) and the structure theorem of De Philippis–Rindler.
The mathematical method is due to Eriksson-Bique–Murugan. The proof constructs the normal-current
reduction directly on the original sigma-finite measure.

The source form and its energy remain on that measure. The unweighted image measure need not be
finite or sigma-finite. Bounded measurable tests and the measurable kernel projection provide the
matrix argument.

References: Bouleau–Hirsch (1991), definitions in ch. I; EID formulation in ch. V, p. 185; Notes, p.
302; Eriksson-Bique–Murugan, Section 4.2 and Remark 4.12. Their Theorem 1.7 is the related
probability-space result.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology ErrorCalculus Matrix
open scoped NNReal ENNReal
universe u v

namespace DprBridge.BH1991
variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
variable {m : Measure X}

/-- A nonzero sigma-finite measure has a bounded, everywhere positive probability density. -/
theorem exists_finite_reference [SigmaFinite m] (hm : m ≠ 0) :
    ∃ h : X → ℝ, Measurable h ∧ (∀ x, 0 < h x) ∧
      (∃ C : ℝ, ∀ x, h x ≤ C) ∧ Integrable h m ∧ (∫ x, h x ∂m) = 1 ∧
      IsProbabilityMeasure (m.withDensity (fun x => ENNReal.ofReal (h x))) ∧
      m ≪ m.withDensity (fun x => ENNReal.ofReal (h x)) ∧
      m.withDensity (fun x => ENNReal.ofReal (h x)) ≪ m := by
  obtain ⟨g, hgpos, hgm, hgi⟩ := exists_pos_lintegral_lt_of_sigmaFinite m (ε := ∞) (by simp)
  have hg : Integrable (fun x => (g x : ℝ)) m := by
    simpa using integrable_toReal_of_lintegral_ne_top
      (ENNReal.continuous_coe.measurable.comp hgm).aemeasurable hgi.ne
  let a : X → ℝ := fun x => min (g x : ℝ) 1
  have ham : Measurable a := (NNReal.continuous_coe.measurable.comp hgm).min measurable_const
  have hap (x : X) : 0 < a x := lt_min (hgpos x) zero_lt_one
  have hai : Integrable a m := hg.mono' ham.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_pos (hap x)]; exact min_le_left _ _)
  have ha_support : Function.support a = Set.univ := by
    ext x; simp [Function.mem_support, (hap x).ne']
  have hZ : 0 < ∫ x, a x ∂m :=
    (integral_pos_iff_support_of_nonneg (fun x => (hap x).le) hai).2
      (by rw [ha_support]; exact bot_lt_iff_ne_bot.mpr (Measure.measure_univ_ne_zero.mpr hm))
  let h : X → ℝ := fun x => (∫ x, a x ∂m)⁻¹ * a x
  have hhm : Measurable h := ham.const_mul _
  have hhp (x : X) : 0 < h x := mul_pos (inv_pos.mpr hZ) (hap x)
  have hhi : Integrable h m := hai.const_mul _
  have hh1 : (∫ x, h x ∂m) = 1 := by
    rw [show h = fun x => (∫ x, a x ∂m)⁻¹ * a x from rfl, integral_const_mul,
      inv_mul_cancel₀ hZ.ne']
  refine ⟨h, hhm, hhp, ⟨(∫ x, a x ∂m)⁻¹, fun x => ?_⟩, hhi, hh1, ?_, ?_,
    withDensity_absolutelyContinuous _ _⟩
  · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (inv_nonneg.mpr hZ.le)).trans_eq
      (mul_one _)
  · constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hhi (ae_of_all _ fun x => (hhp x).le), hh1]
    norm_num
  · exact withDensity_absolutelyContinuous' hhm.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hhp x)).ne')

/-- Bounded tests also multiply arbitrary integrable representatives. -/
theorem integrable_test_mul {μ : Measure X} (H : ImageTest X) {b : X → ℝ}
    (hb : Integrable b μ) : Integrable (fun x => H x * b x) μ := by
  obtain ⟨C, hC⟩ := H.bound
  exact hb.bdd_mul H.measurable.aestronglyMeasurable (ae_of_all _ hC)

/-- Integrable nonnegative source densities have finite pushforwards under any map. -/
theorem finite_weighted_image (f : X → Y) (b : X → ℝ) (hb : Integrable b m)
    (hp : ∀ x, 0 ≤ b x) :
    IsFiniteMeasure ((m.withDensity (fun x => ENNReal.ofReal (b x))).map f) := by
  haveI : IsFiniteMeasure (m.withDensity (fun x => ENNReal.ofReal (b x))) :=
    isFiniteMeasure_withDensity
      ((hasFiniteIntegral_iff_ofReal (ae_of_all _ hp)).mp hb.hasFiniteIntegral).ne
  infer_instance

/-- The weighted image identity uses the original density and the original measure. -/
theorem integral_weighted_image (f : X → Y) (hf : Measurable f) (b : X → ℝ)
    (hb : Measurable b) (hp : ∀ x, 0 ≤ b x) (H : ImageTest Y) :
    (∫ y, H y ∂(m.withDensity (fun x => ENNReal.ofReal (b x))).map f) =
      ∫ x, H (f x) * b x ∂m := by
  rw [integral_map hf.aemeasurable H.measurable.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hb.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hp x), smul_eq_mul, mul_comm]

/-- RN construction for a signed L1 source, with a prescribed sigma-finite image reference. -/
theorem exists_imageL1_class (ν : Measure Y) [SigmaFinite ν] (f : X → Y)
    (hf : Measurable f) (hdom : m.map f ≪ ν) (b : Lp ℝ 1 m) :
    ∃ c : Lp ℝ 1 ν, ∀ H : ImageTest Y,
      H.integral c = (H.comp f hf).integral b := by
  let bp : X → ℝ := fun x => max (b x) 0
  let bm : X → ℝ := fun x => max (-b x) 0
  have hbp : Integrable bp m := (L1.integrable_coeFn b).sup (integrable_zero _ _ _)
  have hbm : Integrable bm m := (L1.integrable_coeFn b).neg.sup (integrable_zero _ _ _)
  have hbpm : Measurable bp := (Lp.stronglyMeasurable b).measurable.max measurable_const
  have hbmm : Measurable bm := (Lp.stronglyMeasurable b).measurable.neg.max measurable_const
  let μp := (m.withDensity (fun x => ENNReal.ofReal (bp x))).map f
  let μm := (m.withDensity (fun x => ENNReal.ofReal (bm x))).map f
  haveI : IsFiniteMeasure μp := finite_weighted_image f bp hbp (fun x => le_max_right _ _)
  haveI : IsFiniteMeasure μm := finite_weighted_image f bm hbm (fun x => le_max_right _ _)
  have hpac : μp ≪ ν := ((withDensity_absolutelyContinuous _ _).map hf).trans hdom
  have hmac : μm ≪ ν := ((withDensity_absolutelyContinuous _ _).map hf).trans hdom
  let cp : Y → ℝ := fun y => (μp.rnDeriv ν y).toReal
  let cm : Y → ℝ := fun y => (μm.rnDeriv ν y).toReal
  have hcp : Integrable cp ν := Measure.integrable_toReal_rnDeriv
  have hcm : Integrable cm ν := Measure.integrable_toReal_rnDeriv
  let c := (hcp.sub hcm).toL1 (fun y => cp y - cm y)
  refine ⟨c, fun H => ?_⟩
  change (∫ y, H y * c y ∂ν) = ∫ x, H (f x) * b x ∂m
  calc
    _ = ∫ y, H y * (cp y - cm y) ∂ν :=
      integral_congr_ae ((MemLp.coeFn_toLp _).mono fun y hy => congrArg (H y * ·) hy)
    _ = (∫ y, H y * cp y ∂ν) - ∫ y, H y * cm y ∂ν := by
      simp_rw [mul_sub]
      exact integral_sub (integrable_test_mul H hcp) (integrable_test_mul H hcm)
    _ = (∫ y, H y ∂μp) - ∫ y, H y ∂μm := by
      congr 1
      · simpa only [cp, mul_comm] using (integral_toReal_rnDeriv_mul (f := H) hpac)
      · simpa only [cm, mul_comm] using (integral_toReal_rnDeriv_mul (f := H) hmac)
    _ = (∫ x, H (f x) * bp x ∂m) - ∫ x, H (f x) * bm x ∂m := by
      rw [integral_weighted_image f hf bp hbpm (fun _ => le_max_right _ _) H,
        integral_weighted_image f hf bm hbmm (fun _ => le_max_right _ _) H]
    _ = ∫ x, H (f x) * b x ∂m := by
      have hip : Integrable (fun x => H (f x) * bp x) m :=
        integrable_test_mul (H.comp f hf) hbp
      have him : Integrable (fun x => H (f x) * bm x) m :=
        integrable_test_mul (H.comp f hf) hbm
      rw [← integral_sub hip him]
      apply integral_congr_ae
      apply ae_of_all
      intro x
      dsimp only [bp, bm]
      rcases le_total 0 (b x) with hx | hx
      · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]; ring
      · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]; ring

/-- The sign of a measurable function is an admissible bounded test, including at zero. -/
def signTest (b : Y → ℝ) (hb : Measurable b) : ImageTest Y where
  toFun y := if 0 ≤ b y then 1 else -1
  measurable := Measurable.ite (measurableSet_le measurable_const hb)
    measurable_const measurable_const
  bound := ⟨1, fun y => by dsimp; split_ifs <;> norm_num⟩

/-- The chosen sign realizes the absolute value pointwise. -/
theorem signTest_mul (b : Y → ℝ) (hb : Measurable b) (y : Y) :
    signTest b hb y * b y = |b y| := by
  dsimp [signTest]
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

/-- Any bounded-test transport is an L1 contraction. -/
theorem imageL1_norm_le {ν : Measure Y} (f : X → Y) (hf : Measurable f)
    (b : Lp ℝ 1 m) (c : Lp ℝ 1 ν)
    (hc : ∀ H : ImageTest Y, H.integral c = (H.comp f hf).integral b) : ‖c‖ ≤ ‖b‖ := by
  let H := signTest c (Lp.stronglyMeasurable c).measurable
  have hH (y : Y) : |H y| ≤ 1 := by dsimp [H, signTest]; split_ifs <;> norm_num
  calc
    ‖c‖ = ∫ y, H y * c y ∂ν := by
      rw [L1.norm_eq_integral_norm]
      apply integral_congr_ae
      exact ae_of_all _ fun y => (signTest_mul _ _ y).symm
    _ = ∫ x, H (f x) * b x ∂m := hc H
    _ ≤ ∫ x, |b x| ∂m := by
      apply integral_mono ((H.comp f hf).integrable_mul b) (L1.integrable_coeFn b).abs
      intro x
      change H (f x) * b x ≤ |b x|
      exact (le_abs_self _).trans (by rw [abs_mul]; nlinarith [hH (f x), abs_nonneg (b x)])
    _ = ‖b‖ := by simpa only [Real.norm_eq_abs] using (L1.norm_eq_integral_norm b).symm

/-- A prescribed sigma-finite image reference yields the general continuous linear transfer. -/
theorem exists_imageL1_general (ν : Measure Y) [SigmaFinite ν] (f : X → Y)
    (hf : Measurable f) (hdom : m.map f ≪ ν) :
    ∃ R : Lp ℝ 1 m →L[ℝ] Lp ℝ 1 ν, ‖R‖ ≤ 1 ∧
      ∀ (b : Lp ℝ 1 m) (H : ImageTest Y),
        H.integral (R b) = (H.comp f hf).integral b := by
  classical
  choose c hc using exists_imageL1_class ν f hf hdom
  let L : Lp ℝ 1 m →ₗ[ℝ] Lp ℝ 1 ν :=
    { toFun := c
      map_add' := fun a b => ImageTest.eq_of_integral_eq _ _ (fun H => by
        rw [map_add, hc, hc, hc, map_add])
      map_smul' := fun r b => ImageTest.eq_of_integral_eq _ _ (fun H => by
        rw [map_smul, hc, hc, map_smul]; rfl) }
  let R : Lp ℝ 1 m →L[ℝ] Lp ℝ 1 ν := L.mkContinuous 1 (fun b => by
    change ‖c b‖ ≤ 1 * ‖b‖
    simpa using imageL1_norm_le f hf b (c b) (hc b))
  refine ⟨R, R.opNorm_le_bound zero_le_one (fun b => ?_), fun b H => hc b H⟩
  change ‖c b‖ ≤ 1 * ‖b‖
  simpa using imageL1_norm_le f hf b (c b) (hc b)

/-- The finite-reference version needs only source domination, with no integrability of the map. -/
theorem exists_imageL1 (p : Measure X) [IsFiniteMeasure p] (f : X → Y)
    (hmp : m ≪ p) (hf : Measurable f) :
    ∃ R : Lp ℝ 1 m →L[ℝ] Lp ℝ 1 (p.map f), ‖R‖ ≤ 1 ∧
      ∀ (b : Lp ℝ 1 m) (φ : Y → ℝ), Measurable φ →
        (∃ C : ℝ, ∀ y, |φ y| ≤ C) →
        (∫ y, φ y * R b y ∂p.map f) = ∫ x, φ (f x) * b x ∂m := by
  obtain ⟨R, hR, htest⟩ := exists_imageL1_general (p.map f) f hf (hmp.map hf)
  refine ⟨R, hR, fun b φ hφ hC => ?_⟩
  exact htest b ⟨φ, hφ, by simpa only [Real.norm_eq_abs] using hC⟩

end DprBridge.BH1991

namespace DprBridge.BH1991
variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
variable {m : Measure X} {ν : Measure Y} {n : ℕ}

/-- Integrable scalar functions are determined by their bounded measurable pairings. -/
theorem ae_eq_of_test_integrals {a b : Y → ℝ} (ha : Integrable a ν) (hb : Integrable b ν)
    (h : ∀ H : ImageTest Y, (∫ y, H y * a y ∂ν) = ∫ y, H y * b y ∂ν) : a =ᵐ[ν] b := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq a b ha hb
  intro s hs _
  have he := h (ImageTest.indicator s hs)
  change (∫ y, s.indicator (fun _ => (1 : ℝ)) y * a y ∂ν) =
    ∫ y, s.indicator (fun _ => (1 : ℝ)) y * b y ∂ν at he
  simpa only [← Set.indicator_mul_left, one_mul, integral_indicator hs] using he

/-- Positivity is detected by nonnegative bounded measurable tests. -/
theorem ae_nonneg_of_test_integrals {a : Y → ℝ} (ha : Integrable a ν)
    (h : ∀ H : ImageTest Y, (∀ y, 0 ≤ H y) → 0 ≤ ∫ y, H y * a y ∂ν) :
    ∀ᵐ y ∂ν, 0 ≤ a y := by
  apply ae_nonneg_of_forall_setIntegral_nonneg ha
  intro s hs _
  have he := h (ImageTest.indicator s hs) (fun y => by
    by_cases hy : y ∈ s <;> simp [ImageTest.indicator, Set.indicator, hy])
  change 0 ≤ ∫ y, s.indicator (fun _ => (1 : ℝ)) y * a y ∂ν at he
  simpa only [← Set.indicator_mul_left, one_mul, integral_indicator hs] using he

/-- Scalar constants supply bounded tests on an arbitrary measurable space. -/
def constantTest (a : ℝ) : ImageTest Y :=
  ⟨fun _ => a, measurable_const, ‖a‖, fun _ => le_rfl⟩

section MatrixTransfer
variable (f : X → Y) (M : X → Matrix (Fin n) (Fin n) ℝ)
  (N : Y → Matrix (Fin n) (Fin n) ℝ) (hf : Measurable f)
  (hMi : ∀ i j, Integrable (fun x => M x i j) m)
  (hNi : ∀ i j, Integrable (fun y => N y i j) ν)
  (hRN : ∀ i j (H : ImageTest Y),
    (∫ y, H y * N y i j ∂ν) = ∫ x, H (f x) * M x i j ∂m)

include hf hMi hNi hRN

/-- Finite matrix pairings commute with transfer, including variable bounded coefficients. -/
theorem integral_matrix_pairing (w : Fin n → Fin n → ImageTest Y) :
    (∫ y, ∑ i, ∑ j, w i j y * N y i j ∂ν) =
      ∫ x, ∑ i, ∑ j, w i j (f x) * M x i j ∂m := by
  have hi (i j : Fin n) := integrable_test_mul (w i j) (hNi i j)
  have hj (i j : Fin n) : Integrable (fun x => w i j (f x) * M x i j) m :=
    integrable_test_mul ((w i j).comp f hf) (hMi i j)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hj i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j), integral_finsetSum _ (fun j _ => hj i j)]
  exact Finset.sum_congr rfl (fun j _ => hRN i j (w i j))

/-- A positive source matrix transfers to a positive matrix on one common full-measure set. -/
theorem image_matrix_posSemidef (hMpos : ∀ᵐ x ∂m, (M x).PosSemidef) :
    ∀ᵐ y ∂ν, (N y).PosSemidef := by
  classical
  have hsym (i j : Fin n) : (fun y => N y i j) =ᵐ[ν] (fun y => N y j i) := by
    apply ae_eq_of_test_integrals (hNi i j) (hNi j i)
    intro H
    rw [hRN, hRN]
    apply integral_congr_ae
    filter_upwards [hMpos] with x hx
    have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j i)
      (Matrix.isHermitian_iff_isSymm.mp hx.isHermitian)
    change H (f x) * M x i j = H (f x) * M x j i
    change M x i j = M x j i at he
    rw [he]
  have hq (q : Fin n → ℚ) : ∀ᵐ y ∂ν,
      0 ≤ ∑ i, ∑ j, (q i : ℝ) * (q j : ℝ) * N y i j := by
    apply ae_nonneg_of_test_integrals
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hNi i j).const_mul ((q i : ℝ) * (q j : ℝ)))
    intro H hH
    have he := integral_matrix_pairing f M N hf hMi hNi hRN
      (fun i j => H.mul (constantTest ((q i : ℝ) * (q j : ℝ))))
    have he' : (∫ y, H y * (∑ i, ∑ j, (q i : ℝ) * (q j : ℝ) * N y i j) ∂ν) =
        ∫ x, H (f x) * (∑ i, ∑ j, (q i : ℝ) * (q j : ℝ) * M x i j) ∂m := by
      simpa only [ImageTest.mul, constantTest, Finset.mul_sum, mul_assoc] using he
    rw [he']
    apply integral_nonneg_of_ae
    filter_upwards [hMpos] with x hx
    apply mul_nonneg (hH _)
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      using hx.dotProduct_mulVec_nonneg (fun i => (q i : ℝ))
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hsym i)), ae_all_iff.mpr hq]
    with y hs hq
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact hs j i
  · intro a
    have hd : DenseRange (fun q : Fin n → ℚ => fun i => (q i : ℝ)) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    have hr : 0 ≤ ∑ i, ∑ j, a i * a j * N y i j :=
      hd.induction_on a (isClosed_le continuous_const (by fun_prop)) hq
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hr

end MatrixTransfer

end DprBridge.BH1991

namespace DprBridge.BH1991
variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
variable {m : Measure X} {ν : Measure Y} {n : ℕ}

/-- The positive semidefinite cone of real finite matrices is closed. -/
theorem isClosed_positive_matrices :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} := by
  have he : {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} =
      {A | Aᵀ = A} ∩ ⋂ a : Fin n → ℝ, {A | 0 ≤ a ⬝ᵥ A.mulVec a} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro h
      exact ⟨Matrix.isHermitian_iff_isSymm.mp h.isHermitian, h.dotProduct_mulVec_nonneg⟩
    · rintro ⟨hs, hp⟩
      exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (Matrix.isHermitian_iff_isSymm.mpr hs) hp
  rw [he]
  exact (isClosed_eq (by fun_prop) continuous_id).inter
    (isClosed_iInter fun a => isClosed_le continuous_const (by
      simp only [dotProduct, Matrix.mulVec]; fun_prop))

/-- A measurable almost everywhere positive matrix has an everywhere positive modification. -/
theorem exists_positive_matrix_version (N : Y → Matrix (Fin n) (Fin n) ℝ)
    (hN : Measurable N) (hp : ∀ᵐ y ∂ν, (N y).PosSemidef) :
    ∃ P : Y → Matrix (Fin n) (Fin n) ℝ,
      Measurable P ∧ (∀ y, (P y).PosSemidef) ∧ P =ᵐ[ν] N := by
  classical
  let s : Set Y := {y | (N y).PosSemidef}
  have hs : MeasurableSet s := isClosed_positive_matrices.measurableSet.preimage hN
  refine ⟨s.indicator N, hN.indicator hs, fun y => ?_, ?_⟩
  · by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy]
      exact hy
    · simp only [Set.indicator_of_notMem hy]
      exact Matrix.PosSemidef.zero
  · filter_upwards [hp] with y hy
    have hy' : y ∈ s := hy
    exact Set.indicator_of_mem hy' N

/-- Matrix RN representatives can be chosen measurably and positive everywhere. -/
theorem exists_positive_image_matrix [SigmaFinite ν] (f : X → Y) (hf : Measurable f)
    (hdom : m.map f ≪ ν) (M : X → Matrix (Fin n) (Fin n) ℝ)
    (hMi : ∀ i j, Integrable (fun x => M x i j) m)
    (hMp : ∀ᵐ x ∂m, (M x).PosSemidef) :
    ∃ N : Y → Matrix (Fin n) (Fin n) ℝ,
      Measurable N ∧ (∀ y, (N y).PosSemidef) ∧
      (∀ i j, Integrable (fun y => N y i j) ν) ∧
      ∀ i j (H : ImageTest Y),
        (∫ y, H y * N y i j ∂ν) = ∫ x, H (f x) * M x i j ∂m := by
  classical
  obtain ⟨R, -, hR⟩ := exists_imageL1_general ν f hf hdom
  let b (i j : Fin n) : Lp ℝ 1 m := (hMi i j).toL1 (fun x => M x i j)
  let N₀ : Y → Matrix (Fin n) (Fin n) ℝ := fun y i j => R (b i j) y
  have hm : Measurable N₀ := measurable_pi_lambda _ fun i =>
    measurable_pi_lambda _ fun j => (Lp.stronglyMeasurable _).measurable
  have hi (i j : Fin n) : Integrable (fun y => N₀ y i j) ν := L1.integrable_coeFn _
  have htest (i j : Fin n) (H : ImageTest Y) :
      (∫ y, H y * N₀ y i j ∂ν) = ∫ x, H (f x) * M x i j ∂m := by
    calc
      _ = ∫ x, H (f x) * b i j x ∂m := hR _ H
      _ = _ := integral_congr_ae ((MemLp.coeFn_toLp _).mono
        fun x hx => congrArg (H (f x) * ·) hx)
  have hp := image_matrix_posSemidef f M N₀ hf hMi hi htest hMp
  obtain ⟨N, hN, hNp, he⟩ := exists_positive_matrix_version N₀ hm hp
  refine ⟨N, hN, hNp, fun i j => (hi i j).congr ?_, fun i j H => ?_⟩
  · exact he.symm.mono fun y hy => congrArg (fun A => A i j) hy
  · calc
      _ = ∫ y, H y * N₀ y i j ∂ν := integral_congr_ae
        (he.mono fun y hy => congrArg (fun A => H y * A i j) hy)
      _ = _ := htest i j H

/-- A finite nonnegative reference density transfers to one, fixing the weight convention. -/
theorem image_density_normalization (f : X → Y) (hf : Measurable f)
    (h : X → ℝ) (hm : Measurable h) (hp : ∀ x, 0 ≤ h x)
    [IsFiniteMeasure (m.withDensity (fun x => ENNReal.ofReal (h x)))]
    (c : Y → ℝ) (hc : Integrable c ((m.withDensity (fun x => ENNReal.ofReal (h x))).map f))
    (hRN : ∀ H : ImageTest Y,
      (∫ y, H y * c y ∂(m.withDensity (fun x => ENNReal.ofReal (h x))).map f) =
        ∫ x, H (f x) * h x ∂m) :
    c =ᵐ[(m.withDensity (fun x => ENNReal.ofReal (h x))).map f] fun _ => 1 := by
  apply ae_eq_of_test_integrals hc (integrable_const 1)
  intro H
  rw [hRN, ← integral_weighted_image f hf h hm hp H]
  simp only [mul_one]

end DprBridge.BH1991

namespace DprBridge.BH1991
variable {n : ℕ}

/-- The measurable kernel projection is symmetric. -/
theorem kernelProjection_symm (A : Matrix (Fin n) (Fin n) ℝ) :
    (kernelProjection A).IsSymm := by
  change (1 - rangeProjection A)ᵀ = 1 - rangeProjection A
  rw [Matrix.transpose_sub, Matrix.transpose_one, rangeProjection_isSymm A]

/-- The measurable kernel projection is idempotent. -/
theorem kernelProjection_idem (A : Matrix (Fin n) (Fin n) ℝ) :
    kernelProjection A * kernelProjection A = kernelProjection A := by
  dsimp only [kernelProjection]
  simp only [sub_mul, mul_sub, one_mul, mul_one, rangeProjection_idempotent]
  abel

/-- Every entry of an orthogonal projection has absolute value at most one. -/
theorem projection_entry_bound (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) (i j : Fin n) : |Q i j| ≤ 1 := by
  classical
  have hs (k l : Fin n) : Q k l = Q l k := congrArg (fun A => A l k) hQ
  have hd (k : Fin n) : ∑ l, (Q k l)^2 = Q k k := by
    have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A k k) hQQ
    simpa only [Matrix.mul_apply, ← hs k, ← sq] using he
  have hb (k l : Fin n) : (Q k l)^2 ≤ Q k k := by
    rw [← hd]
    exact Finset.single_le_sum (fun l _ => sq_nonneg _) (Finset.mem_univ l)
  have hdiag : Q i i ≤ 1 := by nlinarith [hb i i]
  have hij : (Q i j)^2 ≤ 1 := (hb i j).trans hdiag
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- The trace of a projection times a matrix is the sum of its column quadratic forms. -/
theorem trace_projection_mul (Q A : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) :
    (Q * A).trace = ∑ k, (fun i => Q i k) ⬝ᵥ (A.mulVec (fun i => Q i k)) := by
  have he : (Q * A).trace = (Q * A * Q).trace := by
    rw [Matrix.trace_mul_cycle, hQQ]
  rw [he]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.diag, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : Q k i = Q i k := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B i k) hQ
  rw [hs]
  ring

/-- The trace pairing with a positive matrix is nonnegative. -/
theorem trace_projection_nonneg (Q A : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) (hA : A.PosSemidef) : 0 ≤ (Q * A).trace := by
  rw [trace_projection_mul Q A hQ hQQ]
  exact Finset.sum_nonneg fun k _ => hA.dotProduct_mulVec_nonneg _

/-- A zero trace against a positive definite matrix forces the projection to vanish. -/
theorem projection_eq_zero_of_trace (Q A : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) (hA : A.PosSemidef) (hdet : 0 < A.det)
    (hz : (Q * A).trace = 0) : Q = 0 := by
  classical
  rw [trace_projection_mul Q A hQ hQQ] at hz
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => hA.dotProduct_mulVec_nonneg (fun i => Q i k))).mp hz
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet.ne'))
  ext i j
  have hcol : (fun i => Q i j) = 0 := by
    apply hinj
    simpa only [Matrix.mulVec_zero] using
      (hA.dotProduct_mulVec_zero_iff _).mp (hall j (Finset.mem_univ j))
  exact congrFun hcol i

end DprBridge.BH1991

namespace DprBridge.BH1991
variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
variable {m p : Measure X} {ν : Measure Y} {n : ℕ}

/-- A kernel projection annihilates its symmetric matrix on the left as well. -/
theorem kernelProjection_mul {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    kernelProjection A * A = 0 := by
  rw [kernelProjection, sub_mul, one_mul, rangeProjection_mul hA, sub_self]

/-- The entrywise trace formula is oriented for a common RN transfer of matrix entries. -/
theorem trace_mul_entries (Q A : Matrix (Fin n) (Fin n) ℝ) :
    (Q * A).trace = ∑ i, ∑ j, Q j i * A i j := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]

/--
The positive source determinant forces a positive image determinant on the restricted image. The
source may have infinite mass. Only the displayed absolute continuities are used.
-/
theorem positive_det_image (f : X → Y) (M : X → Matrix (Fin n) (Fin n) ℝ)
    (N : Y → Matrix (Fin n) (Fin n) ℝ) (hpm : p ≪ m) (hmap : p.map f ≪ ν)
    (hf : Measurable f) (hM : Measurable M) (hN : Measurable N)
    (hMpos : ∀ᵐ x ∂m, (M x).PosSemidef) (hNpos : ∀ᵐ y ∂ν, (N y).PosSemidef)
    (hMi : ∀ i j, Integrable (fun x => M x i j) m)
    (hNi : ∀ i j, Integrable (fun y => N y i j) ν)
    (hRN : ∀ i j (H : ImageTest Y),
      (∫ y, H y * N y i j ∂ν) = ∫ x, H (f x) * M x i j ∂m) :
    ∀ᵐ y ∂(p.restrict {x | 0 < (M x).det}).map f, 0 < (N y).det := by
  classical
  let Q : Y → Matrix (Fin n) (Fin n) ℝ := fun y => kernelProjection (N y)
  have hQ : Measurable Q := measurable_kernelProjection.comp hN
  let w : Fin n → Fin n → ImageTest Y := fun i j =>
    ⟨fun y => Q y j i, (measurable_pi_apply i).comp ((measurable_pi_apply j).comp hQ),
      1, fun y => by simpa only [Real.norm_eq_abs] using
        projection_entry_bound (Q y) (kernelProjection_symm _) (kernelProjection_idem _) j i⟩
  have htracei : Integrable (fun x => (Q (f x) * M x).trace) m := by
    simp_rw [trace_mul_entries]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_test_mul ((w i j).comp f hf) (hMi i j)
  have htrace : (∫ x, (Q (f x) * M x).trace ∂m) = ∫ y, (Q y * N y).trace ∂ν := by
    simp_rw [trace_mul_entries]
    exact (integral_matrix_pairing f M N hf hMi hNi hRN w).symm
  have hz : (∫ x, (Q (f x) * M x).trace ∂m) = 0 := by
    rw [htrace]
    apply integral_eq_zero_of_ae
    filter_upwards [hNpos] with y hy
    change (Q y * N y).trace = 0
    rw [show Q y * N y = 0 from kernelProjection_mul hy.isHermitian, Matrix.trace_zero]
  have hnonneg : ∀ᵐ x ∂m, 0 ≤ (Q (f x) * M x).trace := by
    filter_upwards [hMpos] with x hx
    exact trace_projection_nonneg _ _ (kernelProjection_symm _) (kernelProjection_idem _) hx
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg htracei).mp hz
  have hkernel : ∀ᵐ x ∂m, 0 < (M x).det → Q (f x) = 0 := by
    filter_upwards [hae, hMpos] with x hx hp hd
    exact projection_eq_zero_of_trace _ _ (kernelProjection_symm _)
      (kernelProjection_idem _) hp hd hx
  have hndet : Measurable (fun y => (N y).det) := continuous_id.matrix_det.measurable.comp hN
  have hAdet : MeasurableSet {x | 0 < (M x).det} :=
    measurableSet_lt measurable_const (continuous_id.matrix_det.measurable.comp hM)
  apply (ae_map_iff hf.aemeasurable (measurableSet_lt measurable_const hndet)).mpr
  apply (ae_restrict_iff' hAdet).mpr
  have hNp : ∀ᵐ x ∂p, (N (f x)).PosSemidef := by
    exact ae_of_ae_map hf.aemeasurable (hmap.ae_le hNpos)
  filter_upwards [hpm.ae_le hkernel, hNp] with x hx hnx hAx
  apply (hnx.posDef_iff_det_ne_zero.mpr ?_).det_pos
  apply det_ne_zero_of_boundedKernelColumn_eq_zero hnx.isHermitian
  intro j
  unfold boundedKernelColumn
  rw [show kernelProjection (N (f x)) = 0 from hx hAx]
  change _ • (0 : Fin n → ℝ) = 0
  exact smul_zero _

end DprBridge.BH1991


namespace DprBridge.BH1991
variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
variable {m p : Measure X}

/-- The positive part of a measurable real weight has the null sets of its positive locus. -/
theorem weighted_restrict_equivalent (d : X → ℝ) (hd : Measurable d) :
    m.withDensity (fun x => ENNReal.ofReal (d x)) ≪ m.restrict {x | 0 < d x} ∧
    m.restrict {x | 0 < d x} ≪ m.withDensity (fun x => ENNReal.ofReal (d x)) := by
  have hA : MeasurableSet {x | 0 < d x} := measurableSet_lt measurable_const hd
  have he : m.withDensity (fun x => ENNReal.ofReal (d x)) =
      (m.restrict {x | 0 < d x}).withDensity (fun x => ENNReal.ofReal (d x)) := by
    rw [← withDensity_indicator hA]
    congr 1
    funext x
    by_cases hx : 0 < d x
    · simp [Set.indicator, hx]
    · simp [Set.indicator, hx, ENNReal.ofReal_eq_zero.mpr (not_lt.mp hx)]
  rw [he]
  refine ⟨withDensity_absolutelyContinuous _ _, withDensity_absolutelyContinuous'
    hd.ennreal_ofReal.aemeasurable ?_⟩
  filter_upwards [ae_restrict_mem hA] with x hx
  exact (ENNReal.ofReal_pos.mpr hx).ne'

/-- Measurable real weights need no integrability assumption to compare their image null sets. -/
theorem weighted_image_equivalent (f : X → Y) (hf : Measurable f) (d : X → ℝ)
    (hd : Measurable d) (hmp : m ≪ p) (hpm : p ≪ m) :
    (m.withDensity (fun x => ENNReal.ofReal (d x))).map f ≪
      (p.restrict {x | 0 < d x}).map f ∧
    (p.restrict {x | 0 < d x}).map f ≪
      (m.withDensity (fun x => ENNReal.ofReal (d x))).map f := by
  obtain ⟨h1, h2⟩ := weighted_restrict_equivalent (m := m) d hd
  exact ⟨(h1.trans (hmp.restrict _)).map hf, ((hpm.restrict _).trans h2).map hf⟩

/-- A common L1 subsequence yields a common matrix determinant limit. -/
theorem exists_subseq_matrix_det {ν : Measure Y} {n : ℕ}
    (a : ℕ → Fin n → Fin n → Lp ℝ 1 ν) (b : Fin n → Fin n → Lp ℝ 1 ν)
    (h : ∀ i j, Tendsto (fun k => a k i j) atTop (𝓝 (b i j))) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ᵐ y ∂ν,
      Tendsto (fun k => Matrix.det (fun i j => a (s k) i j y)) atTop
        (𝓝 (Matrix.det (fun i j => b i j y))) := by
  obtain ⟨s, hs, ht⟩ := exists_subseq_L1_finite_ae
    (fun k (ij : Fin n × Fin n) => a k ij.1 ij.2)
    (fun ij => b ij.1 ij.2) (fun ij => h ij.1 ij.2)
  refine ⟨s, hs, ht.mono fun y hy => ?_⟩
  exact continuous_id.matrix_det.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hy (i, j))

/-- Disjoint restrictions along an almost everywhere cover sum exactly to the original measure. -/
theorem sum_disjoint_restrictions {ν : Measure Y} (U : ℕ → Set Y)
    (hU : ∀ k, MeasurableSet (U k)) (hcover : ∀ᵐ y ∂ν, ∃ k, y ∈ U k) :
    Measure.sum (fun k => ν.restrict (disjointed U k)) = ν := by
  rw [← Measure.restrict_iUnion (disjoint_disjointed U) (MeasurableSet.disjointed hU),
    iUnion_disjointed]
  have he : (⋃ k, U k) =ᵐ[ν] Set.univ := by
    filter_upwards [hcover] with y hy
    change (y ∈ ⋃ k, U k) = (y ∈ Set.univ)
    apply propext
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hy
  rw [Measure.restrict_congr_set he, Measure.restrict_univ]

/-- Restricting a certificate only requires domination of the new measure. -/
def NormalCurrentCertificate.mono {n : ℕ} {ρ σ : Measure (Fin n → ℝ)}
    (C : NormalCurrentCertificate σ) (h : ρ ≪ σ) : NormalCurrentCertificate ρ where
  currents := C.currents
  normal := C.normal
  dominated j := h.trans (C.dominated j)
  spans := h.ae_le C.spans

/-- An invertible column matrix gives the mass domination and spanning directions needed by DPR. -/
def certificateOfDensityColumns {n : ℕ} {ν ρ : Measure (Fin n → ℝ)}
    (A : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (hA : Measurable A)
    (hi : ∀ j, Integrable (fun y => polarNorm (fun i => A y i j)) ν)
    (hn : ∀ j, (PolarCurrent.ofDensity ν (fun y i => A y i j)
      (measurable_pi_lambda _ fun i => (measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp hA)) (hi j) j).IsNormal)
    (hρ : ρ ≪ ν) (hdet : ∀ᵐ y ∂ρ, 0 < (A y).det) : NormalCurrentCertificate ρ where
  currents j := PolarCurrent.ofDensity ν (fun y i => A y i j)
    (measurable_pi_lambda _ fun i => (measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp hA)) (hi j) j
  normal := hn
  dominated j := by
    apply absolutelyContinuous_withDensity_of_ae_ne_zero hρ
      (((continuous_polarNorm n).measurable.comp (measurable_pi_lambda _ fun i =>
        (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA))).ennreal_ofReal)
    filter_upwards [hdet] with y hy
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    apply lt_of_le_of_ne (polarNorm_nonneg _) (Ne.symm ?_)
    intro hz
    have hr := polarNorm_eq_zero.mp hz
    exact hy.ne' (Matrix.det_eq_zero_of_column_eq_zero j (fun i => congrFun hr i))
  spans := by
    filter_upwards [hdet] with y hy
    exact span_polarDirections_of_det_ne_zero (A y).transpose
      (by simpa using hy.ne') (fun j y i => A y i j) y (fun _ => rfl)

/-- Disjoint finite pieces assemble a countable certificate without an infinite multiplicity sum. -/
theorem countable_certificate_of_cover {n : ℕ} {ν η : Measure (Fin n → ℝ)}
    [IsFiniteMeasure ν] (U : ℕ → Set (Fin n → ℝ)) (hU : ∀ k, MeasurableSet (U k))
    (hcover : ∀ᵐ y ∂ν, ∃ k, y ∈ U k)
    (C : ∀ k, NormalCurrentCertificate (ν.restrict (U k))) (hη : η ≪ ν) :
    Nonempty (CountableCurrentCertificate η) := by
  refine ⟨{ pieces := fun k => ν.restrict (disjointed U k)
            finite := fun k => inferInstance
            certificate := fun k => (C k).mono ?_
            dominated := ?_ }⟩
  · exact Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono (disjointed_subset U k) le_rfl)
  · rwa [sum_disjoint_restrictions U hU hcover]

/-- The zero measure has a normal-current certificate, including in dimension zero. -/
def zeroNormalCurrentCertificate (n : ℕ) : NormalCurrentCertificate (0 : Measure (Fin n → ℝ)) where
  currents j := PolarCurrent.ofDensity 0 (fun _ => 0) measurable_const
    (by simp) j
  normal j := by
    refine ⟨0, 0, inferInstance, inferInstance, fun φ _ _ => ?_⟩
    simp [PolarCurrent.boundary, PolarCurrent.ofDensity_action]
  dominated _ := Measure.AbsolutelyContinuous.zero _
  spans := by simp

/-- The zero target has a countable normal-current certificate. -/
def zeroCountableCurrentCertificate (n : ℕ) :
    CountableCurrentCertificate (0 : Measure (Fin n → ℝ)) where
  pieces _ := 0
  finite _ := inferInstance
  certificate _ := zeroNormalCurrentCertificate n
  dominated := Measure.AbsolutelyContinuous.zero _

end DprBridge.BH1991

namespace DprBridge.BH1991.DirichletForm
variable {X : Type u} [MeasurableSpace X] {m : Measure X} (D : DirichletForm m)

/-- The L1 class of the EBM-normalized BH density remains on the original measure. -/
def halfGamma (G : D.CarreDuChamp) (u v : D.form.dom) : Lp ℝ 1 m :=
  (1 / 2 : ℝ) • G.Γ (D.form.formToDomain.symm u) (D.form.formToDomain.symm v)

/-- The source matrix uses the pointwise half-Gamma normalization. -/
def halfGammaMatrix (G : D.CarreDuChamp) {n : ℕ} (f : Fin n → D.form.dom) (x : X) :
    Matrix (Fin n) (Fin n) ℝ := (1 / 2 : ℝ) • D.gammaMatrix G f x

/-- The half-Gamma matrix is measurable. -/
theorem measurable_halfGammaMatrix (G : D.CarreDuChamp) {n : ℕ} (f : Fin n → D.form.dom) :
    Measurable (D.halfGammaMatrix G f) := by
  exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    (Lp.stronglyMeasurable _).measurable.const_mul (1 / 2 : ℝ)

/-- The half-Gamma source matrix has integrable entries. -/
theorem integrable_halfGammaMatrix (G : D.CarreDuChamp) {n : ℕ}
    (f : Fin n → D.form.dom) (i j : Fin n) :
    Integrable (fun x => D.halfGammaMatrix G f x i j) m :=
  (D.gammaMatrix_integrable G f i j).const_mul _

/-- Positive semidefiniteness survives the half-Gamma normalization. -/
theorem halfGammaMatrix_posSemidef (G : D.CarreDuChamp) {n : ℕ} (f : Fin n → D.form.dom) :
    ∀ᵐ x ∂m, (D.halfGammaMatrix G f x).PosSemidef := by
  filter_upwards [D.gammaMatrix_posSemidef G f] with x hx
  exact hx.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- The BH determinant weight and the half-Gamma positive locus have identical image null sets. -/
theorem eidMeasure_equivalent_reference (G : D.CarreDuChamp) {n : ℕ}
    (f : Fin n → D.form.dom) (p : Measure X) (hmp : m ≪ p) (hpm : p ≪ m) :
    D.eidMeasure G f ≪ (p.restrict {x | 0 < (D.halfGammaMatrix G f x).det}).map
      (fun x i => (f i : Lp ℝ 2 m) x) ∧
    (p.restrict {x | 0 < (D.halfGammaMatrix G f x).det}).map
      (fun x i => (f i : Lp ℝ 2 m) x) ≪ D.eidMeasure G f := by
  have hf : Measurable (fun x i => (f i : Lp ℝ 2 m) x) :=
    measurable_pi_lambda _ fun i => (Lp.stronglyMeasurable _).measurable
  have hg : Measurable (D.gammaMatrix G f) := measurable_pi_lambda _ fun _ =>
    measurable_pi_lambda _ fun _ => (Lp.stronglyMeasurable _).measurable
  have hs : {x | 0 < (D.halfGammaMatrix G f x).det} =
      {x | 0 < (D.gammaMatrix G f x).det} := by
    ext x
    simp only [Set.mem_setOf_eq, halfGammaMatrix, Matrix.det_smul, Fintype.card_fin]
    exact mul_pos_iff_of_pos_left (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
  rw [hs]
  exact weighted_image_equivalent _ hf _ (continuous_id.matrix_det.measurable.comp hg) hmp hpm

section Transfer
variable {n : ℕ} {ν : Measure (Fin n → ℝ)} (G : D.CarreDuChamp)
  (R : Lp ℝ 1 m →L[ℝ] Lp ℝ 1 ν)

/-- Mixed matrices use the same reference and the same continuous transfer for every column. -/
def transferredMatrix (f g : Fin n → D.form.dom) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => R (D.halfGamma G (f i) (g j)) y

/-- The simultaneous L1 representatives form a measurable mixed matrix. -/
theorem measurable_transferredMatrix (f g : Fin n → D.form.dom) :
    Measurable (D.transferredMatrix G R f g) :=
  measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ =>
    (Lp.stronglyMeasurable _).measurable

/-- Mixed transferred entries are integrable. -/
theorem integrable_transferredMatrix (f g : Fin n → D.form.dom) (i j : Fin n) :
    Integrable (fun y => D.transferredMatrix G R f g y i j) ν := L1.integrable_coeFn _

/-- Form convergence yields L1 convergence after half-Gamma and the common transfer. -/
theorem transferredMatrix_tendsto (f : Fin n → D.form.dom) (g : ℕ → Fin n → D.form.dom)
    (hg : ∀ j, Tendsto (fun k => D.form.formToDomain.symm (g k j)) atTop
      (𝓝 (D.form.formToDomain.symm (f j)))) (i j : Fin n) :
    Tendsto (fun k => R (D.halfGamma G (f i) (g k j))) atTop
      (𝓝 (R (D.halfGamma G (f i) (f j)))) := by
  apply R.continuous.continuousAt.tendsto.comp
  exact (((G.Γ (D.form.formToDomain.symm (f i))).continuous.continuousAt.tendsto).comp
    (hg j)).const_smul (1 / 2 : ℝ)

variable (f : Fin n → D.form.dom)
  (hR : ∀ (b : Lp ℝ 1 m) (H : ImageTest (Fin n → ℝ)),
    (∫ y, H y * R b y ∂ν) = ∫ x, H (fun i => (f i : Lp ℝ 2 m) x) * b x ∂m)
include hR

/-- The mixed RN identity transfers the half-Gamma density under the original source measure. -/
theorem transferredMatrix_test (g : Fin n → D.form.dom) (i j : Fin n)
    (H : ImageTest (Fin n → ℝ)) :
    (∫ y, H y * D.transferredMatrix G R f g y i j ∂ν) =
      ∫ x, H (fun k => (f k : Lp ℝ 2 m) x) *
        ((1 / 2 : ℝ) * G.Γ (D.form.formToDomain.symm (f i))
          (D.form.formToDomain.symm (g j)) x) ∂m := by
  change (∫ y, H y * R (D.halfGamma G (f i) (g j)) y ∂ν) = _
  rw [hR]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ)
    (G.Γ (D.form.formToDomain.symm (f i)) (D.form.formToDomain.symm (g j)))] with x hx
  change _ = _ at hx
  exact congrArg (H (fun k => (f k : Lp ℝ 2 m) x) * ·) hx

omit hR in
/-- Columns are integrable in the Euclidean norm used by polar currents. -/
theorem transferredMatrix_column_integrable (g : Fin n → D.form.dom) (j : Fin n) :
    Integrable (fun y => polarNorm (fun i => D.transferredMatrix G R f g y i j)) ν :=
  ((ErrorStructure.euclideanEquiv n).toContinuousLinearMap.integrable_comp
    (integrable_pi_iff.mpr (fun i => D.integrable_transferredMatrix G R f g i j))).norm

/--
Eriksson-Bique--Murugan, Section 4.2 and Remark 4.12; Bouleau--Hirsch 1991, I.6.1.1--3. Every
prescribed RN column is normal by the centered chain rule and its actual generator pair.
-/
theorem transferredMatrix_column_normal (hL : D.Local) (g : Fin n → D.form.dom)
    (a : Fin n → Lp ℝ 2 m) (hga : ∀ j, D.IsGeneratorPair (g j) (a j))
    (ha : ∀ j, Integrable (a j) m) (j : Fin n) :
    (PolarCurrent.ofDensity ν (fun y i => D.transferredMatrix G R f g y i j)
      (measurable_pi_lambda _ fun _ => (Lp.stronglyMeasurable _).measurable)
      (D.transferredMatrix_column_integrable G R f g j) j).IsNormal := by
  apply (D.normalCurrent_of_RN_density hL G j f (g j) (a j) (hga j) (ha j) ν _ _ _ ?_).1
  intro h hh hb
  obtain ⟨C, hC⟩ := hb
  let H : Fin n → ImageTest (Fin n → ℝ) := fun i =>
    ⟨h i, hh i, C, fun y => by simpa only [Real.norm_eq_abs] using hC i y⟩
  have hip (i : Fin n) : Integrable (fun y => h i y * D.transferredMatrix G R f g y i j) ν :=
    (H i).integrable_mul _
  have his (i : Fin n) : Integrable (fun x => h i (fun k => (f k : Lp ℝ 2 m) x) *
      ((1 / 2 : ℝ) * G.Γ (D.form.formToDomain.symm (f i))
        (D.form.formToDomain.symm (g j)) x)) m :=
    integrable_test_mul ((H i).comp _ (measurable_pi_lambda _ fun k =>
      (Lp.stronglyMeasurable _).measurable)) ((L1.integrable_coeFn _).const_mul _)
  rw [integral_finsetSum _ (fun i _ => hip i), integral_finsetSum _ (fun i _ => his i)]
  exact Finset.sum_congr rfl (fun i _ => D.transferredMatrix_test G R f hR g i j (H i))

end Transfer
end DprBridge.BH1991.DirichletForm

namespace DprBridge.BH1991.DirichletForm
variable {X : Type u} [MeasurableSpace X] {m : Measure X} (D : DirichletForm m)

/--
The BH determinant image admits countably many finite normal-current certificates. The construction
uses the original form, a finite equivalent reference, signed L1 transfer, one common subsequence,
and disjoint restrictions. No constant in the form domain is needed.
-/
theorem exists_countableCurrentCertificate [SigmaFinite m] (hL : D.Local)
    (G : D.CarreDuChamp) (n : ℕ) (_hn : 0 < n) (f : Fin n → D.form.dom) :
    Nonempty (CountableCurrentCertificate (D.eidMeasure G f)) := by
  classical
  by_cases hm : m = 0
  · have he : D.eidMeasure G f = 0 := by simp [eidMeasure, hm]
    rw [he]
    exact ⟨zeroCountableCurrentCertificate n⟩
  obtain ⟨h, hhm, hhp, -, -, -, hp, hmp, hpm⟩ := exists_finite_reference hm
  let p := m.withDensity (fun x => ENNReal.ofReal (h x))
  haveI : IsProbabilityMeasure p := hp
  let F : X → (Fin n → ℝ) := fun x i => (f i : Lp ℝ 2 m) x
  have hF : Measurable F := measurable_pi_lambda _ fun i => (Lp.stronglyMeasurable _).measurable
  obtain ⟨R, -, hR⟩ := exists_imageL1_general (p.map F) F hF (hmp.map hF)
  have hR' : ∀ (b : Lp ℝ 1 m) (H : ImageTest (Fin n → ℝ)),
      (∫ y, H y * R b y ∂p.map F) = ∫ x, H (F x) * b x ∂m := hR
  let M := D.halfGammaMatrix G f
  let N := D.transferredMatrix G R f f
  have hMm : Measurable M := D.measurable_halfGammaMatrix G f
  have hNm : Measurable N := D.measurable_transferredMatrix G R f f
  have hMi := D.integrable_halfGammaMatrix G f
  have hNi := D.integrable_transferredMatrix G R f f
  have hMp := D.halfGammaMatrix_posSemidef G f
  have hRN : ∀ i j (H : ImageTest (Fin n → ℝ)),
      (∫ y, H y * N y i j ∂p.map F) = ∫ x, H (F x) * M x i j ∂m :=
    D.transferredMatrix_test G R f hR' f
  have hNp := image_matrix_posSemidef F M N hF hMi hNi hRN hMp
  let ν₀ := (p.restrict {x | 0 < (M x).det}).map F
  have hν : ν₀ ≪ p.map F :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).map hF
  have hpos : ∀ᵐ y ∂ν₀, 0 < (N y).det :=
    positive_det_image F M N hpm Measure.AbsolutelyContinuous.rfl hF hMm hNm hMp hNp hMi hNi hRN
  have hη : D.eidMeasure G f ≪ ν₀ := (D.eidMeasure_equivalent_reference G f p hmp hpm).1
  choose g a hga hgt using fun j : Fin n => D.l1GeneratorCore (f j)
  let gseq : ℕ → Fin n → D.form.dom := fun k j => g j k
  have ht (i j : Fin n) :
      Tendsto (fun k => R (D.halfGamma G (f i) (gseq k j))) atTop
        (𝓝 (R (D.halfGamma G (f i) (f j)))) :=
    D.transferredMatrix_tendsto G R f gseq hgt i j
  obtain ⟨s, hs, hae⟩ := exists_subseq_matrix_det
    (fun k i j => R (D.halfGamma G (f i) (gseq k j)))
    (fun i j => R (D.halfGamma G (f i) (f j))) ht
  let A : ℕ → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
    fun k => D.transferredMatrix G R f (gseq (s k))
  let U : ℕ → Set (Fin n → ℝ) := fun k => {y | 0 < (A k y).det}
  have hA (k : ℕ) : Measurable (A k) := D.measurable_transferredMatrix G R f _
  have hU (k : ℕ) : MeasurableSet (U k) :=
    measurableSet_lt measurable_const (continuous_id.matrix_det.measurable.comp (hA k))
  have hcover : ∀ᵐ y ∂ν₀, ∃ k, y ∈ U k := by
    filter_upwards [hν.ae_le hae, hpos] with y hy hp
    exact (hy.eventually (eventually_gt_nhds hp)).exists
  apply countable_certificate_of_cover U hU hcover _ hη
  intro k
  apply certificateOfDensityColumns (A k) (hA k)
    (D.transferredMatrix_column_integrable G R f (gseq (s k)))
  · intro j
    exact D.transferredMatrix_column_normal G R f hR' hL (gseq (s k))
      (fun j => a j (s k)) (fun j => (hga j (s k)).1) (fun j => (hga j (s k)).2) j
  · exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hν
  · exact ae_restrict_mem (hU k)

end DprBridge.BH1991.DirichletForm

namespace DprBridge.BH1991

/--
Bouleau--Hirsch 1991, definitions in ch. I; EID formulation in ch. V, p. 185; Notes p. 302;
Eriksson-Bique--Murugan, Section 4.2 and Remark
4.12. The original sigma-finite BH hypotheses construct the normal-current reduction.
-/
theorem bh_normal_current_reduction : BHNormalCurrentReduction.{u} := by
  intro X _ m _ D hL _ G n hn f
  exact D.exists_countableCurrentCertificate hL G n hn f

/--
The printed Bouleau–Hirsch EID conjecture holds under its original sigma-finite hypotheses,
following the normal-current method of Eriksson-Bique–Murugan (Section 4.2, Remark 4.12) and
the structure theorem of De Philippis–Rindler. The mathematical method is due to
Eriksson-Bique–Murugan;
the proof uses the normal-current reduction constructed on the original measure.

References: Bouleau–Hirsch (1991), definitions in ch. I; EID formulation in ch. V, p. 185; Notes, p.
302. Eriksson-Bique–Murugan's Theorem 1.7 is the related probability-space statement.
-/
theorem bh1991_printed_eid_conjecture : BH1991PrintedEIDConjecture.{u} :=
  bh1991_printed_eid_conjecture_of_normal_currents bh_normal_current_reduction

end DprBridge.BH1991

namespace DprBridge.BH1991.PrintedProofControls

/-- An infinite source may have a pushforward that is not sigma-finite, even on the real line. -/
theorem constant_count_image_not_sigmaFinite :
    ¬ SigmaFinite ((Measure.count : Measure ℕ).map (fun _ => (0 : ℝ))) := by
  intro h
  let μ := (Measure.count : Measure ℕ).map (fun _ => (0 : ℝ))
  haveI : SigmaFinite μ := h
  have hmem : (0 : ℝ) ∈ ⋃ k, spanningSets μ k := by rw [iUnion_spanningSets]; trivial
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
  have he : (fun _ : ℕ => (0 : ℝ)) ⁻¹' spanningSets μ k = Set.univ := by
    ext x; simp [hk]
  have hb := measure_spanningSets_lt_top μ k
  change ((Measure.count : Measure ℕ).map (fun _ => (0 : ℝ))) (spanningSets μ k) < ∞ at hb
  rw [Measure.map_apply measurable_const (measurableSet_spanningSets μ k), he,
    count_univ_eq_top] at hb
  exact (lt_irrefl _) hb

/-- The general transfer still exists for the constant map of that infinite counting source. -/
theorem infinite_source_constant_transfer :
    ∃ p : Measure ℕ, IsProbabilityMeasure p ∧ Measure.count ≪ p ∧ p ≪ Measure.count ∧
      ∃ R : Lp ℝ 1 (Measure.count : Measure ℕ) →L[ℝ]
          Lp ℝ 1 (p.map (fun _ => (0 : ℝ))), ‖R‖ ≤ 1 ∧
        ∀ b : Lp ℝ 1 (Measure.count : Measure ℕ),
          (∫ y, R b y ∂p.map (fun _ => (0 : ℝ))) = ∫ x, b x ∂Measure.count := by
  have hm : (Measure.count : Measure ℕ) ≠ 0 := by
    intro he
    have ht := count_univ_eq_top
    rw [he] at ht
    simp at ht
  obtain ⟨h, -, -, -, -, -, hp, hmp, hpm⟩ := exists_finite_reference hm
  let p := (Measure.count : Measure ℕ).withDensity (fun x => ENNReal.ofReal (h x))
  haveI : IsProbabilityMeasure p := hp
  obtain ⟨R, hR, htest⟩ := exists_imageL1_general (p.map (fun _ => (0 : ℝ)))
    (fun _ => (0 : ℝ)) measurable_const (hmp.map measurable_const)
  refine ⟨p, hp, hmp, hpm, R, hR, fun b => ?_⟩
  simpa [ImageTest.integral, ImageTest.one, ImageTest.comp] using htest b ImageTest.one

/-- The unconditional result applies on an infinite original space with no domain constant one. -/
theorem infinite_zero_form_eid {n : ℕ} (hn : 0 < n)
    (f : Fin n → (zeroForm (Measure.count : Measure ℕ)).form.dom) :
    (Measure.count : Measure ℕ) Set.univ = ∞ ∧
      (¬ ∃ g : (zeroForm (Measure.count : Measure ℕ)).form.dom,
        ⇑(g : Lp ℝ 2 (Measure.count : Measure ℕ)) =ᵐ[Measure.count] fun _ => (1 : ℝ)) ∧
      (zeroForm Measure.count).eidMeasure (zeroCarreDuChamp Measure.count) f ≪ volume :=
  ⟨count_univ_eq_top, zeroForm_count_no_one,
    bh1991_printed_eid_conjecture ℕ Measure.count (zeroForm Measure.count)
      (zeroForm_local _) (zeroForm_admitsCarreDuChamp _) (zeroCarreDuChamp _) n hn f⟩

end DprBridge.BH1991.PrintedProofControls

