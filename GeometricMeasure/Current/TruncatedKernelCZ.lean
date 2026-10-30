import GeometricMeasure.Current.EllipticEnergy

/-!
# L² and Hörmander bounds for the truncated second kernel

## Main results
The truncated second kernel has an L² bound on every L¹ ∩ L² input and an integral Hörmander bound
uniform in η > 0, with constant 72·4^{d/2} + 6e. These supply the hypotheses of the abstract weak
convolution criterion.

Bibliographic context: De Philippis–Rindler, pp. 9–10, (2.9)–(2.12).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped Topology RealInnerProductSpace Convolution ContDiff
namespace GeometricMeasure
variable {d : ℕ}

/--
For η > 0 and every f ∈ L¹ ∩ L², the convolution Kη ∗ f satisfies ‖Kη ∗ f‖₂ ≤ e^{−η}‖f‖₂,
expressed in squares of real integrals. Smoothness of f is unnecessary. Bibliographic context: De
Philippis–Rindler, pp. 9–10.
-/
theorem truncatedSecondKernel_L2_sq {η : ℝ} (hη : 0 < η) (a b : Fin d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Integrable f) (hf2 : MemLp f 2) :
    MemLp (scalarConvolution (truncatedSecondKernel η a b) f) 2 ∧
      (∫ x, scalarConvolution (truncatedSecondKernel η a b) f x ^ 2) ≤
        Real.exp (-η) ^ 2 * ∫ x, f x ^ 2 := by
  set K := truncatedSecondKernel (d := d) η a b with hKdef
  have hK : Integrable K := integrable_truncatedSecondKernel hη a b
  set N := ∫ x, ‖K x‖ with hN
  have hN0 : 0 ≤ N := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨(scalarConvolution_L2_bound hK hf hf2).1, ?_⟩
  have hE : 0 < Real.exp (-η) := Real.exp_pos _
  have hfnn : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have key : Real.sqrt (∫ x, scalarConvolution K f x ^ 2) ≤
      Real.exp (-η) * Real.sqrt (∫ x, f x ^ 2) := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    set ε := δ / (Real.exp (-η) + N + 1) with hεdef
    have hε : 0 < ε := by positivity
    obtain ⟨u, hu⟩ := exists_test_sq_sub_le hf2 hε
    set r : EuclideanSpace ℝ (Fin d) → ℝ := fun x => f x - u x with hr
    have hr1 : Integrable r := hf.sub (scalarTest_integrable u)
    have hr2 : MemLp r 2 := hf2.sub (scalarTest_memLp_two u)
    have hdec : ∀ᵐ x, scalarConvolution K f x =
        scalarConvolution K u x + scalarConvolution K r x := by
      filter_upwards [hK.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hr1] with x hx
      have hfr : f = (u : EuclideanSpace ℝ (Fin d) → ℝ) + r := by
        funext y
        simp only [Pi.add_apply, hr]
        ring
      rw [hfr]
      exact (scalarConvolution_exists K hK u x).distrib_add hx
    have hint : (∫ x, scalarConvolution K f x ^ 2) =
        ∫ x, (scalarConvolution K u x + scalarConvolution K r x) ^ 2 :=
      integral_congr_ae (hdec.mono fun x hx => by simp only [hx])
    have hKu : MemLp (scalarConvolution K u) 2 := scalarConvolution_test_memLp_two hK u
    have hYr := scalarConvolution_L2_bound hK hr1 hr2
    have hm1 := sqrt_integral_sq_add_le hKu hYr.1
    have hT : Real.sqrt (∫ x, scalarConvolution K u x ^ 2) ≤
        Real.exp (-η) * Real.sqrt (∫ x, u x ^ 2) := by
      rw [hKdef, truncatedSecondKernel_convolution_test_eq hη]
      exact truncatedSecondTest_L2 hη a b u
    have hR : Real.sqrt (∫ x, scalarConvolution K r x ^ 2) ≤ N * ε := by
      calc _ ≤ Real.sqrt (N ^ 2 * ε ^ 2) :=
            Real.sqrt_le_sqrt (hYr.2.trans (mul_le_mul_of_nonneg_left hu (sq_nonneg _)))
        _ = N * ε := by rw [← mul_pow, Real.sqrt_sq (by positivity)]
    have hU : Real.sqrt (∫ x, u x ^ 2) ≤ Real.sqrt (∫ x, f x ^ 2) + ε := by
      have hm := sqrt_integral_sq_add_le hf2 hr2.neg
      have e1 : (∫ x, (f x + (-r) x) ^ 2) = ∫ x, u x ^ 2 := by
        congr 1
        ext x
        simp only [Pi.neg_apply, hr]
        ring
      have e2 : (∫ x, (-r) x ^ 2) = ∫ x, r x ^ 2 := by
        congr 1
        ext x
        simp only [Pi.neg_apply, neg_sq]
      rw [e1, e2] at hm
      have hs : Real.sqrt (∫ x, r x ^ 2) ≤ ε := by
        calc _ ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hu
          _ = ε := Real.sqrt_sq hε.le
      linarith
    have h1 : (Real.exp (-η) + N + 1) * ε = δ := by
      rw [hεdef]
      field_simp
    have h2 : (Real.exp (-η) + N) * ε + ε = δ := by rw [← h1]; ring
    have hEU := mul_le_mul_of_nonneg_left hU hE.le
    rw [hint]
    calc _ ≤ _ := hm1
      _ ≤ Real.exp (-η) * (Real.sqrt (∫ x, f x ^ 2) + ε) + N * ε := by linarith
      _ = Real.exp (-η) * Real.sqrt (∫ x, f x ^ 2) + (Real.exp (-η) + N) * ε := by ring
      _ ≤ _ := by linarith
  have hnn : 0 ≤ ∫ x, scalarConvolution K f x ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  calc (∫ x, scalarConvolution K f x ^ 2) =
      Real.sqrt (∫ x, scalarConvolution K f x ^ 2) ^ 2 := (Real.sq_sqrt hnn).symm
    _ ≤ (Real.exp (-η) * Real.sqrt (∫ x, f x ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) key 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hfnn]

/--
Form used by the weak criterion (38) with A = 1. Source: DPR context, transcription pp. 9–10. Exact
scope: parameters, assumptions and conclusion below.
-/
theorem truncatedSecondKernel_L2_le {η : ℝ} (hη : 0 < η) (a b : Fin d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (∫ x, scalarConvolution (truncatedSecondKernel η a b) f x ^ 2) ≤ ∫ x, f x ^ 2 := by
  have h := (truncatedSecondKernel_L2_sq hη a b hf hf2).2
  have hE : Real.exp (-η) ^ 2 ≤ 1 :=
    pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
  exact h.trans (mul_le_of_le_one_left (integral_nonneg (fun _ => sq_nonneg _)) hE)

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
private theorem inv_mul_exp_neg_le {t ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ) :
    t⁻¹ * Real.exp (-(ρ ^ 2 / (8 * t))) ≤ 8 / ρ ^ 2 := by
  set u := ρ ^ 2 / (8 * t) with hu
  have hu0 : 0 < u := by positivity
  have k1 : u * Real.exp (-u) ≤ 1 := by
    have h1 := Real.add_one_le_exp u
    have h2 := Real.exp_pos (-u)
    have h3 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have ht' : t⁻¹ = 8 * u / ρ ^ 2 := by rw [hu]; field_simp
  rw [ht']
  have hρ2 : 0 < ρ ^ 2 := by positivity
  calc 8 * u / ρ ^ 2 * Real.exp (-u) = 8 / ρ ^ 2 * (u * Real.exp (-u)) := by ring
    _ ≤ 8 / ρ ^ 2 * 1 := mul_le_mul_of_nonneg_left k1 (by positivity)
    _ = 8 / ρ ^ 2 := mul_one _

/--
Obtained Hörmander constant: 72·4^{d/2} + 6e (= 72·2^d + 6e). Source: DPR context, transcription pp.
9–10. Exact scope: parameters, assumptions and conclusion below.
-/
def hormanderConstant (d : ℕ) : ℝ := 72 * (4 : ℝ) ^ ((d : ℝ) / 2) + 6 * Real.exp 1

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem heatSecond_time_integrable {η : ℝ} (hη : 0 < η) (a b : Fin d)
    (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun t => Real.exp (-t) * heatSecondDirectional d t
      (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) y) (Ioi η) := by
  apply ((integrableOn_exp_neg_Ioi η).mul_const
    (3 / (2 * η) * ((4 * Real.pi * η) ^ ((d : ℝ) / 2))⁻¹)).mono'
  · exact ((Real.measurable_exp.comp measurable_id.neg).mul
      ((measurable_heatSecondDirectional _ _).comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (norm_heatSecondDirectional_le_sup hη ht.le
      (by simp : ‖EuclideanSpace.single a (1 : ℝ)‖ = 1) (by simp : ‖EuclideanSpace.single b (1 : ℝ)‖ = 1) y) (Real.exp_pos _).le

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integrable_weighted_heatSecond_tail_translate {η : ℝ} (hη : 0 < η) (a b : Fin d)
    (h : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      Real.exp (-p.1) * heatSecondDirectional d p.1 (EuclideanSpace.single a 1)
        (EuclideanSpace.single b 1) (p.2 - h))
      ((volume.restrict (Ioi η)).prod volume) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      Real.exp (-p.1) * heatSecondDirectional d p.1 (EuclideanSpace.single a 1)
        (EuclideanSpace.single b 1) (p.2 - h)) ((volume.restrict (Ioi η)).prod volume) :=
    ((Real.measurable_exp.comp measurable_fst.neg).mul
      ((measurable_heatSecondDirectional _ _).comp
        (measurable_fst.prodMk (measurable_snd.sub_const h)))).aestronglyMeasurable
  apply (integrable_prod_iff hm).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ((integrable_heatSecondDirectional (hη.trans ht) (by simp : ‖EuclideanSpace.single a (1 : ℝ)‖ = 1)
      (by simp : ‖EuclideanSpace.single b (1 : ℝ)‖ = 1)).comp_sub_right h).const_mul _
  · have h0 := (integrable_weighted_heatSecond_tail hη a b).norm.integral_prod_left
    refine h0.congr (ae_of_all _ (fun t => ?_))
    exact (integral_sub_right_eq_self (fun x => ‖Real.exp (-t) * heatSecondDirectional d t
      (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) x‖) h).symm

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
private theorem sqrt_mul_self_rpow {t : ℝ} (ht : 0 < t) :
    (t * Real.sqrt t)⁻¹ = t ^ (-(3 / 2 : ℝ)) := by
  rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add ht, Real.rpow_one]

/--
For η > 0, the integral of |Kη(x − h) − Kη(x)| over |x| > 2|h| is bounded by 72·4^(d/2) + 6e,
independently of η and h. Bibliographic context: De Philippis–Rindler, pp. 9–10.
-/
theorem truncatedSecondKernel_hormander {η : ℝ} (hη : 0 < η) (a b : Fin d)
    (h : EuclideanSpace ℝ (Fin d)) :
    (∫ x in {x : EuclideanSpace ℝ (Fin d) | 2 * ‖h‖ < ‖x‖},
      ‖truncatedSecondKernel η a b (x - h) - truncatedSecondKernel η a b x‖) ≤
      hormanderConstant d := by
  have hH0 : 0 ≤ hormanderConstant d := by unfold hormanderConstant; positivity
  rcases eq_or_ne h 0 with rfl | hh
  · simp only [sub_zero, sub_self, norm_zero, integral_zero]
    exact hH0
  set ρ := ‖h‖ with hρdef
  have hρ : 0 < ρ := norm_pos_iff.2 hh
  set A := {x : EuclideanSpace ℝ (Fin d) | 2 * ‖h‖ < ‖x‖} with hA
  set ea := EuclideanSpace.single a (1 : ℝ)
  set eb := EuclideanSpace.single b (1 : ℝ)
  -- F(t, x) = e^{-t} ‖S_t(x-h) - S_t(x)‖
  set F : ℝ × EuclideanSpace ℝ (Fin d) → ℝ := fun p =>
    Real.exp (-p.1) * ‖heatSecondDirectional d p.1 ea eb (p.2 - h) -
      heatSecondDirectional d p.1 ea eb p.2‖ with hF
  have hFi : Integrable F ((volume.restrict (Ioi η)).prod (volume.restrict A)) := by
    have h1 := ((integrable_weighted_heatSecond_tail_translate hη a b h).sub
      (integrable_weighted_heatSecond_tail hη a b)).norm
    have h2 : Integrable F ((volume.restrict (Ioi η)).prod volume) := by
      refine h1.congr (ae_of_all _ (fun p => ?_))
      simp only [hF, Pi.sub_apply, ← mul_sub, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      rfl
    exact h2.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  -- representation and pointwise bound
  have hpt : ∀ x, ‖truncatedSecondKernel η a b (x - h) - truncatedSecondKernel η a b x‖ ≤
      ∫ t in Ioi η, F (t, x) := by
    intro x
    unfold truncatedSecondKernel
    rw [← integral_sub (heatSecond_time_integrable hη a b (x - h))
      (heatSecond_time_integrable hη a b x)]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext t
    simp only [hF, ← mul_sub, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    rfl
  -- The two estimates of D(t)
  set c1 : ℝ := 9 * (4 : ℝ) ^ ((d : ℝ) / 2) * (8 / ρ ^ 2) with hc1
  set c2 : ℝ := ρ * (3 * Real.exp 1) with hc2
  set g : ℝ → ℝ := fun t => (Ioc 0 (ρ ^ 2)).indicator (fun _ => c1) t +
    (Ioi (ρ ^ 2)).indicator (fun t => c2 * t ^ (-(3 / 2 : ℝ))) t with hg
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hc1n : 0 ≤ c1 := by positivity
  have hc2n : 0 ≤ c2 := by positivity
  have hgi : Integrable g := by
    apply Integrable.add
    · exact (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp) (by simp))
    · exact (integrable_indicator_iff measurableSet_Ioi).2
        ((integrableOn_Ioi_rpow_of_lt (by norm_num) hρ2).const_mul c2)
  have hgn : ∀ t, 0 ≤ g t := by
    intro t
    apply add_nonneg
    · exact Set.indicator_nonneg (fun _ _ => hc1n) t
    · exact Set.indicator_nonneg (fun s hs => mul_nonneg hc2n
        (Real.rpow_nonneg (le_of_lt (hρ2.trans hs)) _)) t
  have hgint : (∫ t, g t) = hormanderConstant d := by
    rw [hg, integral_add ((integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const (by simp) (by simp)))
      ((integrable_indicator_iff measurableSet_Ioi).2
        ((integrableOn_Ioi_rpow_of_lt (by norm_num) hρ2).const_mul c2)),
      integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioi,
      setIntegral_const, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hρ2]
    have hv : volume.real (Ioc (0 : ℝ) (ρ ^ 2)) = ρ ^ 2 := by
      simp [Measure.real, Real.volume_Ioc, hρ2.le]
    have hr : (ρ ^ 2) ^ (-(3 / 2 : ℝ) + 1) = ρ⁻¹ := by
      rw [show (-(3 / 2 : ℝ) + 1) = -(1 / 2) by norm_num, Real.rpow_neg (sq_nonneg ρ),
        ← Real.sqrt_eq_rpow, Real.sqrt_sq hρ.le]
    rw [hv, hr, smul_eq_mul, hc1, hc2]
    unfold hormanderConstant
    field_simp
    ring
  have hD : ∀ t ∈ Ioi η, (∫ x in A, F (t, x)) ≤ g t := by
    intro t ht
    have ht0 : 0 < t := hη.trans ht
    have hS := integrable_heatSecondDirectional ht0 (by simp : ‖EuclideanSpace.single a (1 : ℝ)‖ = 1) (by simp : ‖EuclideanSpace.single b (1 : ℝ)‖ = 1)
    have hDi : Integrable (fun x =>
        ‖heatSecondDirectional d t ea eb (x - h) - heatSecondDirectional d t ea eb x‖) :=
      ((hS.comp_sub_right h).sub hS).norm
    have hDle : (∫ x in A, F (t, x)) ≤ ∫ x in A,
        ‖heatSecondDirectional d t ea eb (x - h) - heatSecondDirectional d t ea eb x‖ := by
      simp only [hF]
      rw [integral_const_mul]
      have hn : 0 ≤ ∫ x in A,
          ‖heatSecondDirectional d t ea eb (x - h) - heatSecondDirectional d t ea eb x‖ :=
        integral_nonneg (fun _ => norm_nonneg _)
      exact mul_le_of_le_one_left hn (Real.exp_le_one_iff.mpr (by linarith))
    have hout := integral_norm_heatSecond_outer_le ht0 (by simp : ‖EuclideanSpace.single a (1 : ℝ)‖ = 1) (by simp : ‖EuclideanSpace.single b (1 : ℝ)‖ = 1) h
    have htr := integral_norm_heatSecond_translate_le ht0 (by simp : ‖EuclideanSpace.single a (1 : ℝ)‖ = 1)
      (by simp : ‖EuclideanSpace.single b (1 : ℝ)‖ = 1) h
    have hsub : (∫ x in A,
        ‖heatSecondDirectional d t ea eb (x - h) - heatSecondDirectional d t ea eb x‖) ≤
        ∫ x, ‖heatSecondDirectional d t ea eb (x - h) - heatSecondDirectional d t ea eb x‖ :=
      setIntegral_le_integral hDi (ae_of_all _ (fun _ => norm_nonneg _))
    rcases le_or_gt t (ρ ^ 2) with hts | hts
    · have hgt : g t = c1 := by
        simp only [hg, Set.indicator_of_mem (show t ∈ Ioc 0 (ρ ^ 2) from ⟨ht0, hts⟩),
          Set.indicator_of_notMem (show t ∉ Ioi (ρ ^ 2) from fun h' => absurd h' (not_lt.2 hts)),
          add_zero]
      rw [hgt]
      have hexp := inv_mul_exp_neg_le ht0 hρ
      have hc : 9 * (4 : ℝ) ^ ((d : ℝ) / 2) * (t⁻¹ * Real.exp (-(ρ ^ 2 / (8 * t)))) ≤ c1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      linarith
    · have hgt : g t = c2 * t ^ (-(3 / 2 : ℝ)) := by
        simp only [hg, Set.indicator_of_notMem (show t ∉ Ioc 0 (ρ ^ 2) from
            fun h' => absurd h'.2 (not_le.2 hts)),
          Set.indicator_of_mem (show t ∈ Ioi (ρ ^ 2) from hts), zero_add]
      rw [hgt, ← sqrt_mul_self_rpow ht0]
      have he : ρ * (3 * Real.exp 1 / (t * Real.sqrt t)) = c2 * (t * Real.sqrt t)⁻¹ := by
        rw [hc2]; ring
      linarith
  -- assembly
  have hR : Integrable (fun x => ∫ t in Ioi η, F (t, x)) (volume.restrict A) :=
    hFi.integral_prod_right
  calc (∫ x in A, ‖truncatedSecondKernel η a b (x - h) - truncatedSecondKernel η a b x‖) ≤
      ∫ x in A, ∫ t in Ioi η, F (t, x) :=
        integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _)) hR (ae_of_all _ hpt)
    _ = ∫ t in Ioi η, ∫ x in A, F (t, x) :=
        (integral_integral_swap (f := fun t x => F (t, x)) hFi).symm
    _ ≤ ∫ t in Ioi η, g t := by
        apply integral_mono_ae hFi.integral_prod_left hgi.integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hD t ht
    _ ≤ ∫ t, g t := setIntegral_le_integral hgi (ae_of_all _ hgn)
    _ = hormanderConstant d := hgint


/--
For η > 0, the truncated second kernel is measurable, integrable and bounded, with L² operator bound
A = 1 on L¹ ∩ L² and Hörmander constant 72·4^{d/2} + 6e. Bibliographic context: De
Philippis–Rindler, pp. 9–10.
-/
theorem truncatedSecondKernel_cz_hypotheses {η : ℝ} (hη : 0 < η) (a b : Fin d) :
    StronglyMeasurable (truncatedSecondKernel (d := d) η a b) ∧
    Integrable (truncatedSecondKernel (d := d) η a b) ∧
    (∃ M : ℝ, ∀ x, ‖truncatedSecondKernel η a b x‖ ≤ M) ∧
    (∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Integrable f → MemLp f 2 →
      MemLp (scalarConvolution (truncatedSecondKernel η a b) f) 2 ∧
      (∫ x, scalarConvolution (truncatedSecondKernel η a b) f x ^ 2) ≤ ∫ x, f x ^ 2) ∧
    (∀ h : EuclideanSpace ℝ (Fin d),
      (∫ x in {x : EuclideanSpace ℝ (Fin d) | 2 * ‖h‖ < ‖x‖},
        ‖truncatedSecondKernel η a b (x - h) - truncatedSecondKernel η a b x‖) ≤
        hormanderConstant d) :=
  ⟨stronglyMeasurable_truncatedSecondKernel η a b, integrable_truncatedSecondKernel hη a b,
    ⟨_, norm_truncatedSecondKernel_le hη a b⟩,
    fun _ hf hf2 => ⟨(truncatedSecondKernel_L2_sq hη a b hf hf2).1,
      truncatedSecondKernel_L2_le hη a b hf hf2⟩,
    truncatedSecondKernel_hormander hη a b⟩

/--
Nonsmooth instance: in dimension 1, the (discontinuous) indicator of the unit ball satisfies the
assumptions of (38); the bound applies to an input that is not a test. Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem truncatedSecondKernel_indicator_L2_le {η : ℝ} (hη : 0 < η) :
    let f : EuclideanSpace ℝ (Fin 1) → ℝ := (ball (0 : EuclideanSpace ℝ (Fin 1)) 1).indicator
      (fun _ => (1 : ℝ))
    Integrable f ∧ MemLp f 2 ∧
      (∫ x, scalarConvolution (truncatedSecondKernel η 0 0) f x ^ 2) ≤ ∫ x, f x ^ 2 := by
  intro f
  have hm : MemLp f 2 := memLp_indicator_const 2 measurableSet_ball (1 : ℝ)
    (Or.inr measure_ball_lt_top.ne)
  have hi : Integrable f := by
    simpa only [memLp_one_iff_integrable] using
      (memLp_indicator_const 1 measurableSet_ball (1 : ℝ) (Or.inr measure_ball_lt_top.ne))
  exact ⟨hi, hm, truncatedSecondKernel_L2_le hη 0 0 hi hm⟩

/--
Degenerate case h = 0 of (39): the integrand is zero. Source: DPR context, transcription pp. 9–10.
Exact scope: parameters, assumptions and conclusion below.
-/
theorem truncatedSecondKernel_hormander_zero (η : ℝ) (a b : Fin d) :
    (∫ x in {x : EuclideanSpace ℝ (Fin d) | 2 * ‖(0 : EuclideanSpace ℝ (Fin d))‖ < ‖x‖},
      ‖truncatedSecondKernel η a b (x - 0) - truncatedSecondKernel η a b x‖) = 0 := by
  simp only [sub_zero, sub_self, norm_zero, integral_zero]

end GeometricMeasure
