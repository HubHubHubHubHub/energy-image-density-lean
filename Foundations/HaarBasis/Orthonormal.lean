import Foundations.HaarBasis.Basic

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace NNReal
namespace Foundations

theorem primitive_haarFamily (i : SchauderIndex) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..t, haarFamily i x) =
      match i with
      | none => t
      | some ⟨j,k⟩ => schauder j k t := by
  have he : (∫ x in (0 : ℝ)..t, haarFamily i x) = ∫ x in (0 : ℝ)..t, haarFunction i x := by
    rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1,
      ← integral_Ico_eq_integral_Ioc, ← integral_Ico_eq_integral_Ioc]
    exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset
      (Ico_subset_Ico le_rfl ht.2) (coe_haarFamily i))
  rw [he]
  cases i with
  | none => exact cellPrimitive_zero_unit ht
  | some p => rfl

theorem inner_haarFamily_none (g : HaarL2) :
    ⟪haarFamily none, g⟫_ℝ = ∫ x in (0 : ℝ)..1, g x := by
  simpa [haarFamily] using inner_dyadicLp g (j := 0) (k := 0) (by norm_num)

theorem inner_haarFamily_some (g : HaarL2) (j : ℕ) (k : Fin (2^j)) :
    ⟪haarFamily (some ⟨j,k⟩), g⟫_ℝ = Real.sqrt ((2 : ℝ)^j) *
      (2 * (∫ x in (0 : ℝ)..(((k : ℝ)+1/2)/2^j), g x) -
        (∫ x in (0 : ℝ)..((k : ℝ)/2^j), g x) -
        (∫ x in (0 : ℝ)..(((k : ℝ)+1)/2^j), g x)) := by
  rw [haarFamily, inner_smul_left, inner_sub_left]
  rw [inner_dyadicLp_primitive g (show 2*k.val < 2^(j+1) by rw [pow_succ]; omega),
    inner_dyadicLp_primitive g (show 2*k.val+1 < 2^(j+1) by rw [pow_succ]; omega)]
  simp only [RCLike.conj_to_real, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_succ]
  have h0 : (2*(k : ℝ))/(2^j*2) = (k : ℝ)/2^j := by ring
  have h1 : (2*(k : ℝ)+1)/(2^j*2) = ((k : ℝ)+1/2)/2^j := by ring
  have h2 : (2*(k : ℝ)+1+1)/(2^j*2) = ((k : ℝ)+1)/2^j := by ring
  rw [h0,h1,h2]
  ring

theorem inner_haarFamily (i l : SchauderIndex) :
    ⟪haarFamily i, haarFamily l⟫_ℝ = if l = i then 1 else 0 := by
  classical
  cases i with
  | none =>
    rw [inner_haarFamily_none, primitive_haarFamily l (by norm_num)]
    cases l with
    | none => simp
    | some p => simpa [schauder] using integral_haar_eq_zero p.1 p.2 p.2.isLt
  | some p =>
    obtain ⟨j,k⟩ := p
    rw [inner_haarFamily_some]
    have ha : (k : ℝ)/2^j ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one (by positivity)).mpr (by exact_mod_cast k.isLt.le)⟩
    have hb : ((k : ℝ)+1)/2^j ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one (by positivity)).mpr (by exact_mod_cast k.isLt)⟩
    have hm : ((k : ℝ)+1/2)/2^j ∈ Icc (0 : ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      apply le_trans (b := ((k : ℝ)+1)/2^j) _ hb.2
      gcongr
      norm_num
    rw [primitive_haarFamily l hm, primitive_haarFamily l ha, primitive_haarFamily l hb]
    cases l with
    | none => simp only [reduceCtorEq, if_false]; ring
    | some q =>
      obtain ⟨m,n⟩ := q
      rw [schauder_secondDifference]
      congr 1
      simp only [Option.some.injEq, Sigma.mk.inj_iff]
      apply propext
      constructor
      · rintro ⟨rfl,h⟩; exact ⟨rfl, heq_of_eq (Fin.ext h)⟩
      · rintro ⟨rfl,h⟩; exact ⟨rfl, congrArg Fin.val (eq_of_heq h)⟩

theorem orthonormal_haarFamily : Orthonormal ℝ haarFamily := by
  rw [orthonormal_iff_ite]
  intro i l
  simpa only [eq_comm] using inner_haarFamily i l

end Foundations
