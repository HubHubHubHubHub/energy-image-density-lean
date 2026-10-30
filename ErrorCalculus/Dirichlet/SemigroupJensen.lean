import ErrorCalculus.Dirichlet.SemigroupMarkov
import ErrorCalculus.Dirichlet.ProductRule
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Semigroup Jensen

## Main results
Order and Jensen inequalities for the abstract semigroup, without a kernel.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

theorem semigroup_mono {t : ℝ} (ht : 0 ≤ t) {f g : Lp ℝ 2 μ}
    (hfg : ∀ᵐ ω ∂μ, f ω ≤ g ω) :
    ∀ᵐ ω ∂μ, S.semigroup t f ω ≤ S.semigroup t g ω := by
  have h := S.semigroup_nonneg ht (g-f) (by
    filter_upwards [hfg, Lp.coeFn_sub g f] with ω h hs
    simpa only [hs, Pi.sub_apply, sub_nonneg] using h)
  rw [map_sub] at h
  filter_upwards [h, Lp.coeFn_sub (S.semigroup t g) (S.semigroup t f)] with ω h hs
  simpa only [hs, Pi.sub_apply, sub_nonneg] using h

theorem semigroup_const {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    S.semigroup t (Lp.const 2 μ c) = Lp.const 2 μ c := by
  have hc : Lp.const 2 μ c = c • Lp.const 2 μ (1 : ℝ) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) (c := c),
      Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ)),
      Lp.coeFn_smul c (Lp.const 2 μ (1 : ℝ))] with ω hc h1 hs
    simp [hs]
  rw [hc, map_smul, S.semigroup_const_one ht]

/-- Absolute value as an L² class, for any probability space. -/
def absLp (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (Lp.memLp f).norm.toLp (fun ω => ‖f ω‖)

omit [IsProbabilityMeasure μ] in
theorem coeFn_absLp (f : Lp ℝ 2 μ) :
    absLp f =ᵐ[μ] fun ω => |f ω| := by
  exact (Lp.memLp f).norm.coeFn_toLp.trans
    (Eventually.of_forall fun ω => Real.norm_eq_abs (f ω))

theorem semigroup_abs_le {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 μ) :
    ∀ᵐ ω ∂μ, |S.semigroup t f ω| ≤ S.semigroup t (absLp f) ω := by
  have hp := S.semigroup_mono ht (f := f) (g := absLp f) (by
    filter_upwards [coeFn_absLp f] with ω ha
    rw [ha]; exact le_abs_self _)
  have hn := S.semigroup_mono ht (f := -f) (g := absLp f) (by
    filter_upwards [coeFn_absLp f, Lp.coeFn_neg f] with ω ha hn
    rw [ha, hn]; exact neg_le_abs _)
  rw [map_neg] at hn
  filter_upwards [hp, hn, Lp.coeFn_neg (S.semigroup t f)] with ω hp hn he
  rw [he] at hn
  exact abs_le.mpr ⟨by simpa using neg_le_neg hn, hp⟩

/-- Affine minorants pass through P_t, with no exceptional set uniformity assumption. -/
theorem semigroup_affine_le {t : ℝ} (ht : 0 ≤ t) (f g : Lp ℝ 2 μ)
    (a b : ℝ) (h : ∀ᵐ ω ∂μ, a * f ω + b ≤ g ω) :
    ∀ᵐ ω ∂μ, a * S.semigroup t f ω + b ≤ S.semigroup t g ω := by
  have hh := S.semigroup_mono ht (f := a • f + Lp.const 2 μ b) (g := g) (by
    filter_upwards [h, Lp.coeFn_add (a • f) (Lp.const 2 μ b),
      Lp.coeFn_smul a f, Lp.coeFn_const (p := 2) (μ := μ) (c := b)] with ω h ha hs hc
    simpa only [ha, hs, hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Function.const_apply] using h)
  rw [map_add, map_smul, S.semigroup_const ht] at hh
  filter_upwards [hh, Lp.coeFn_add (a • S.semigroup t f) (Lp.const 2 μ b),
    Lp.coeFn_smul a (S.semigroup t f),
    Lp.coeFn_const (p := 2) (μ := μ) (c := b)] with ω h ha hs hc
  simpa only [ha, hs, hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Function.const_apply] using h

/-- The square inequality on L² data whose square also belongs to L².
The countable intersection is over rational tangency points. -/
theorem semigroup_sq_le {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 μ)
    (hf : MemLp (fun ω => (f ω)^2) 2 μ) :
    ∀ᵐ ω ∂μ, (S.semigroup t f ω)^2 ≤ S.semigroup t (hf.toLp _) ω := by
  have h (c : ℚ) : ∀ᵐ ω ∂μ,
      2*(c:ℝ)*S.semigroup t f ω + (-(c:ℝ)^2) ≤ S.semigroup t (hf.toLp _) ω := by
    apply S.semigroup_affine_le ht f (hf.toLp _) (2*(c:ℝ)) (-(c:ℝ)^2)
    filter_upwards [hf.coeFn_toLp] with ω he
    rw [he]; nlinarith [sq_nonneg (f ω - (c:ℝ))]
  filter_upwards [ae_all_iff.mpr h] with ω hω
  have hall : ∀ c : ℝ, 2*c*S.semigroup t f ω - c^2 ≤ S.semigroup t (hf.toLp _) ω := by
    intro c
    apply Rat.denseRange_cast.induction_on (p := fun c : ℝ =>
      2*c*S.semigroup t f ω - c^2 ≤ S.semigroup t (hf.toLp _) ω) c
      (isClosed_le (by fun_prop) continuous_const)
    intro r
    simpa only [sub_eq_add_neg] using hω r
  have hc := hall (S.semigroup t f ω)
  nlinarith

/-- Jensen from a countable family of affine minorants. The composition is only
required to belong to L²; bounded data in particular satisfy this requirement. -/
theorem semigroup_jensen {t : ℝ} (ht : 0 ≤ t) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (hc : Continuous φ) (f : Lp ℝ 2 μ)
    (hf : MemLp (fun ω => φ (f ω)) 2 μ) :
    ∀ᵐ ω ∂μ, φ (S.semigroup t f ω) ≤ S.semigroup t (hf.toLp _) ω := by
  obtain ⟨L, b, hminor, hsup⟩ := hφ.real_univ_sSup_of_nat_affine_eq hc.lowerSemicontinuous
  have hL (n : ℕ) (x : ℝ) : L n x = L n 1 * x := by
    calc
      L n x = L n (x • (1 : ℝ)) := by simp
      _ = x • L n 1 := (L n).map_smul x 1
      _ = L n 1 * x := by simp [mul_comm]
  have hh (n : ℕ) : ∀ᵐ ω ∂μ,
      L n (S.semigroup t f ω) + b n ≤ S.semigroup t (hf.toLp _) ω := by
    have hi : ∀ᵐ ω ∂μ, L n 1 * f ω + b n ≤ hf.toLp _ ω := by
      filter_upwards [hf.coeFn_toLp] with ω he
      rw [he, ← hL]
      exact hminor n (f ω)
    filter_upwards [S.semigroup_affine_le ht f (hf.toLp _) (L n 1) (b n) hi] with ω he
    simpa only [hL n (S.semigroup t f ω)] using he
  filter_upwards [ae_all_iff.mpr hh] with ω hω
  have he := congrFun hsup (S.semigroup t f ω)
  rw [← he]
  apply ciSup_le
  rintro ⟨_, n, rfl⟩
  exact hω n

/-- Continuous scalar compositions of bounded data belong to every Lᵖ. -/
theorem memLp_continuous_comp_of_aeBounded {φ : ℝ → ℝ} (hc : Continuous φ)
    (f : Lp ℝ 2 μ) (hf : AEBounded (μ := μ) f) (p : ℝ≥0∞) :
    MemLp (fun ω => φ (f ω)) p μ := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (-M) M)).bddAbove_image
    hc.norm.continuousOn
  apply MemLp.of_bound (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)) C
  filter_upwards [hM] with ω hω
  exact hC ⟨f ω, abs_le.mp (by simpa only [Real.norm_eq_abs] using hω), rfl⟩

theorem semigroup_sq_le_bounded {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 μ)
    (hf : AEBounded (μ := μ) f) :
    ∀ᵐ ω ∂μ, (S.semigroup t f ω)^2 ≤ S.semigroup t
      ((memLp_continuous_comp_of_aeBounded (by fun_prop) f hf 2
        (φ := fun x : ℝ => x^2)).toLp _) ω :=
  S.semigroup_sq_le ht f _

theorem semigroup_jensen_bounded {t : ℝ} (ht : 0 ≤ t) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (hc : Continuous φ) (f : Lp ℝ 2 μ)
    (hf : AEBounded (μ := μ) f) :
    ∀ᵐ ω ∂μ, φ (S.semigroup t f ω) ≤ S.semigroup t
      ((memLp_continuous_comp_of_aeBounded hc f hf 2).toLp _) ω :=
  S.semigroup_jensen ht hφ hc f _

/-- Convexity of the real absolute power, including the endpoint p=1. -/
theorem convexOn_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x| ^ p) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hn := (convexOn_univ_norm (E := ℝ)).2 hx hy ha hb hab
  simp only [Real.norm_eq_abs] at hn
  exact (Real.rpow_le_rpow (abs_nonneg _) hn (by linarith)).trans
    ((convexOn_rpow hp).2 (abs_nonneg x) (abs_nonneg y) ha hb hab)

theorem semigroup_abs_pow_le {t p : ℝ} (ht : 0 ≤ t) (hp : 1 ≤ p)
    (f : Lp ℝ 2 μ) (hf : MemLp (fun ω => |f ω| ^ p) 2 μ) :
    ∀ᵐ ω ∂μ, |S.semigroup t f ω| ^ p ≤ S.semigroup t (hf.toLp _) ω :=
  S.semigroup_jensen ht (convexOn_abs_rpow hp)
    ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp continuous_abs) f hf

end ErrorCalculus.ErrorStructure
