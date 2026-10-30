import Foundations.HaarBasis.Orthonormal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace NNReal
namespace Foundations

theorem dyadicLp_refine (j k : ℕ) :
    dyadicLp j k = dyadicLp (j+1) (2*k) + dyadicLp (j+1) (2*k+1) := by
  apply Lp.ext
  filter_upwards [coe_dyadicLp j k, coe_dyadicLp (j+1) (2*k),
    coe_dyadicLp (j+1) (2*k+1), Lp.coeFn_add (dyadicLp (j+1) (2*k))
      (dyadicLp (j+1) (2*k+1))] with x h0 h1 h2 h3
  simp only [h3, Pi.add_apply, h0,h1,h2]
  exact dyadicIndicator_refine j k x

theorem inner_dyadicLp_eq_zero (g : HaarL2)
    (hg : ∀ i, ⟪haarFamily i, g⟫_ℝ = 0) :
    ∀ j k, k < 2^j → ⟪dyadicLp j k, g⟫_ℝ = 0 := by
  intro j
  induction j with
  | zero =>
    intro k hk
    have : k = 0 := by simpa using hk
    subst k
    exact hg none
  | succ j ih =>
    intro k hk
    have hn : k/2 < 2^j := by rw [pow_succ] at hk; omega
    have hsum := ih (k/2) hn
    rw [dyadicLp_refine, inner_add_left] at hsum
    have hdiff := hg (some ⟨j, ⟨k/2,hn⟩⟩)
    simp only [haarFamily, inner_smul_left, inner_sub_left, RCLike.conj_to_real] at hdiff
    have hs : Real.sqrt ((2 : ℝ)^j) ≠ 0 := by positivity
    have hd := (mul_eq_zero.mp hdiff).resolve_left hs
    rcases (show k = 2*(k/2) ∨ k = 2*(k/2)+1 by omega) with h | h
    · rw [h]; linarith
    · rw [h]; linarith

theorem primitive_dyadic_eq_zero (g : HaarL2)
    (hg : ∀ i, ⟪haarFamily i, g⟫_ℝ = 0) (j n : ℕ) (hn : n ≤ 2^j) :
    (∫ x in (0 : ℝ)..((n : ℝ)/2^j), g x) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := inner_dyadicLp_eq_zero g hg j n (by omega)
    rw [inner_dyadicLp_primitive g (by omega), ih (by omega)] at h
    simpa using h

theorem primitive_eq_zero_of_haar_orthogonal (g : HaarL2)
    (hg : ∀ i, ⟪haarFamily i, g⟫_ℝ = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..t, g x) = 0 := by
  let q : ℕ → ℝ := fun j => (⌊t * 2^j⌋₊ : ℝ) / 2^j
  have hq : Tendsto q atTop (𝓝 t) :=
    (tendsto_nat_floor_mul_div_atTop ht.1).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hqn (j : ℕ) : ⌊t * 2^j⌋₊ ≤ 2^j := by
    apply Nat.floor_le_of_le
    push_cast
    exact mul_le_of_le_one_left (by positivity) ht.2
  have hmem (j : ℕ) : q j ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by dsimp [q]; positivity, ?_⟩
    exact (div_le_one (by positivity)).mpr (by exact_mod_cast hqn j)
  have hc := intervalIntegral.continuousOn_primitive_interval'
    (intervalIntegrable_haarL2 g) (a := 0) left_mem_uIcc
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hc
  have hlim := (hc t ht).tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨hq, Filter.Eventually.of_forall hmem⟩)
  have hz (j : ℕ) : (∫ x in (0 : ℝ)..q j, g x) = 0 :=
    primitive_dyadic_eq_zero g hg j _ (hqn j)
  exact tendsto_nhds_unique hlim (by simpa only [Function.comp_def,hz] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))

theorem haar_complete (g : HaarL2) (hg : ∀ i, ⟪haarFamily i, g⟫_ℝ = 0) : g = 0 := by
  have hder := (intervalIntegrable_haarL2 g).ae_hasDerivAt_integral
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hder
  have hz : ∀ᵐ x ∂haarMeasure, g x = 0 := by
    have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
    filter_upwards [ae_restrict_of_ae hder, ae_restrict_of_ae h0,
      ae_restrict_mem measurableSet_Ico] with x hx hx0 hxm
    have hin : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hxm.1 (Ne.symm hx0),hxm.2⟩
    have heq : (fun t => ∫ y in (0 : ℝ)..t, g y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhds hin.1 hin.2] with t ht
      exact primitive_eq_zero_of_haar_orthogonal g hg ⟨ht.1.le,ht.2.le⟩
    exact (hx ⟨hxm.1,hxm.2.le⟩ 0 (by norm_num)).unique
      ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq)
  apply Lp.ext
  filter_upwards [hz, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := haarMeasure)] with x hx h0
  exact hx.trans h0.symm

theorem orthogonal_span_haar_eq_bot : (Submodule.span ℝ (range haarFamily))ᗮ = ⊥ := by
  apply bot_unique
  intro g hg
  change g = 0
  apply haar_complete g
  intro i
  exact (Submodule.mem_orthogonal _ _).mp hg _ (Submodule.subset_span (mem_range_self i))

theorem dense_span_haar : (Submodule.span ℝ (range haarFamily)).topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, orthogonal_span_haar_eq_bot,
    Submodule.bot_orthogonal_eq_top]

def haarBasis : HilbertBasis SchauderIndex ℝ HaarL2 :=
  HilbertBasis.mk orthonormal_haarFamily (by rw [dense_span_haar])

@[simp] theorem haarBasis_apply (i : SchauderIndex) : haarBasis i = haarFamily i :=
  congrFun (HilbertBasis.coe_mk _ _) i

/-- Finite linear combinations of dyadic cell indicators. -/
def dyadicStepSpace : Submodule ℝ HaarL2 :=
  Submodule.span ℝ (range (fun p : Σ j : ℕ, Fin (2^j) => dyadicLp p.1 p.2))

theorem haarFamily_mem_dyadicStepSpace (i : SchauderIndex) : haarFamily i ∈ dyadicStepSpace := by
  have hc (j : ℕ) (k : Fin (2^j)) : dyadicLp j k ∈ dyadicStepSpace :=
    Submodule.subset_span ⟨⟨j,k⟩,rfl⟩
  cases i with
  | none => exact hc 0 ⟨0,by norm_num⟩
  | some p =>
    obtain ⟨j,k⟩ := p
    apply dyadicStepSpace.smul_mem
    exact dyadicStepSpace.sub_mem
      (hc (j+1) ⟨2*k,by rw [pow_succ]; omega⟩)
      (hc (j+1) ⟨2*k+1,by rw [pow_succ]; omega⟩)

theorem dyadicStep_dense : Dense (dyadicStepSpace : Set HaarL2) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  rw [← dense_span_haar]
  apply Submodule.topologicalClosure_mono
  exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact haarFamily_mem_dyadicStepSpace i)

end Foundations
