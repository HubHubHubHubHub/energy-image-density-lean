import ErrorCalculus.Dirichlet.DetBounded
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
namespace ErrorCalculus

/-- The smooth cutoff is zero below ε/2 and one above ε. -/
def localizationCutoff (ε x : ℝ) : ℝ := Real.smoothTransition (2*x/ε-1)

theorem localizationCutoff_contDiff (ε : ℝ) : ContDiff ℝ ∞ (localizationCutoff ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).div_const ε |>.sub contDiff_const)

theorem localizationCutoff_nonneg (ε x : ℝ) : 0 ≤ localizationCutoff ε x :=
  Real.smoothTransition.nonneg _

theorem localizationCutoff_le_one (ε x : ℝ) : localizationCutoff ε x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem localizationCutoff_zero {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ ε/2) :
    localizationCutoff ε x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : 2*x/ε ≤ 1 := (div_le_iff₀ hε).mpr (by linarith)
  linarith

theorem localizationCutoff_one {ε x : ℝ} (hε : 0 < ε) (hx : ε ≤ x) :
    localizationCutoff ε x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have : 2 ≤ 2*x/ε := (le_div_iff₀ hε).mpr (by linarith)
  linarith

/-- Smooth regularization of the reciprocal, with the exact cutoff identity. -/
def smoothInverse (ε x : ℝ) : ℝ := localizationCutoff ε x / x

theorem smoothInverse_zero {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ ε/2) :
    smoothInverse ε x = 0 := by rw [smoothInverse, localizationCutoff_zero hε hx, zero_div]

theorem smoothInverse_eq_inv {ε x : ℝ} (hε : 0 < ε) (hx : ε ≤ x) :
    smoothInverse ε x = x⁻¹ := by rw [smoothInverse, localizationCutoff_one hε hx, one_div]

theorem smoothInverse_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (smoothInverse ε) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (show (0:ℝ) < ε/2 by linarith)] with x hx
    exact smoothInverse_zero hε hx.le
  · exact (localizationCutoff_contDiff ε).contDiffAt.div contDiffAt_id hx

theorem smoothInverse_mul {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    smoothInverse ε x * x = localizationCutoff ε x := by
  by_cases hx : x = 0
  · subst x
    simp [localizationCutoff_zero hε (show (0:ℝ) ≤ ε/2 by positivity)]
  · exact div_mul_cancel₀ _ hx

theorem smoothInverse_bounded {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ‖smoothInverse ε x‖ ≤ 2/ε := by
  by_cases hx : x ≤ ε/2
  · rw [smoothInverse_zero hε hx, norm_zero]; positivity
  · have hp : 0 < x := lt_trans (by positivity : (0:ℝ) < ε/2) (lt_of_not_ge hx)
    rw [smoothInverse, Real.norm_of_nonneg (div_nonneg (localizationCutoff_nonneg ε x) hp.le)]
    calc
      _ ≤ 1/x := div_le_div_of_nonneg_right (localizationCutoff_le_one ε x) hp.le
      _ ≤ 2/ε := (div_le_div_iff₀ hp hε).mpr (by linarith)


/-- The smooth reciprocal cutoff is globally Lipschitz. -/
theorem smoothInverse_lipschitz {ε : ℝ} (hε : 0 < ε) :
    ∃ L : NNReal, LipschitzWith L (smoothInverse ε) := by
  have hc : Continuous (deriv (smoothInverse ε)) :=
    (smoothInverse_contDiff hε).continuous_deriv (by simp)
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (ε/2) ε)).exists_bound_of_continuousOn hc.continuousOn
  let L : ℝ := |C| + (ε^2)⁻¹
  refine ⟨⟨L, by positivity⟩,
    lipschitzWith_of_nnnorm_deriv_le ((smoothInverse_contDiff hε).differentiable (by simp)) ?_⟩
  intro x
  change ‖deriv (smoothInverse ε) x‖ ≤ L
  by_cases hx : x < ε/2
  · have he : smoothInverse ε =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact smoothInverse_zero hε hy.le
    rw [he.deriv_eq, deriv_const, norm_zero]
    positivity
  · by_cases hx' : ε < x
    · have he : smoothInverse ε =ᶠ[𝓝 x] fun y => y⁻¹ := by
        filter_upwards [Ioi_mem_nhds hx'] with y hy
        exact smoothInverse_eq_inv hε hy.le
      rw [he.deriv_eq, deriv_inv, norm_neg, Real.norm_of_nonneg (by positivity)]
      have hxp : 0 < x := hε.trans hx'
      have hi : (x^2)⁻¹ ≤ (ε^2)⁻¹ := inv_le_inv₀ (by positivity) (by positivity) |>.mpr (by nlinarith)
      exact hi.trans (by dsimp [L]; linarith [abs_nonneg C])
    · exact (hC x ⟨le_of_not_gt hx, le_of_not_gt hx'⟩).trans
        ((le_abs_self C).trans (by dsimp [L]; exact le_add_of_nonneg_right (inv_nonneg.mpr (sq_nonneg ε))))

/-- At every positive determinant the dyadic cutoffs are eventually exactly one. -/
theorem localizationCutoff_eventually_one {x : ℝ} (hx : 0 < x) :
    ∀ᶠ n : ℕ in atTop, localizationCutoff ((1/2 : ℝ)^n) x = 1 := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)
  filter_upwards [ht.eventually (Iio_mem_nhds hx)] with n hn
  exact localizationCutoff_one (by positivity) hn.le

/-- The dyadic cutoff sequence is monotone on the positive half-line. -/
theorem localizationCutoff_dyadic_monotone {x : ℝ} (hx : 0 ≤ x) :
    Monotone (fun n : ℕ => localizationCutoff ((1/2 : ℝ)^n) x) := by
  intro m n hmn
  apply Real.smoothTransition.monotone
  apply sub_le_sub_right
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn)

namespace ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {d : ℕ}

/-- The localized inverse entries belong to D ∩ L∞. -/
theorem localizedWeights_mem (ε : ℝ) (hε : 0 < ε) (A : Fin d → Fin d → Ω → ℝ)
    (hA : ∀ i j, A i j ∈ S.boundedDomAlgebra) (i j : Fin d) :
    (fun a => smoothInverse ε (Matrix.of (fun k l => A k l a)).det *
      (Matrix.of (fun k l => A k l a)).adjugate i j) ∈ S.boundedDomAlgebra :=
  S.boundedDomAlgebra.mul_mem
    (S.contDiff_comp_mem_boundedDomAlgebra (S.det_mem_dom_of_bounded A hA)
      ((smoothInverse_contDiff hε).of_le (by simp)))
    (S.adjugate_mem_dom_of_bounded A hA i j)

/-- The actual bounded domain weights, without any inverse-integrability assumption. -/
def localizedWeights (ε : ℝ) (hε : 0 < ε) (A : Fin d → Fin d → Ω → ℝ)
    (hA : ∀ i j, A i j ∈ S.boundedDomAlgebra) (i j : Fin d) : S.dom :=
  S.boundedDomElement _ (S.localizedWeights_mem ε hε A hA i j)

theorem coeFn_localizedWeights (ε : ℝ) (hε : 0 < ε) (A : Fin d → Fin d → Ω → ℝ)
    (hA : ∀ i j, A i j ∈ S.boundedDomAlgebra) (i j : Fin d) :
    ⇑(S.localizedWeights ε hε A hA i j : Lp ℝ 2 μ) =ᵐ[μ] fun a =>
      smoothInverse ε (Matrix.of (fun k l => A k l a)).det *
        (Matrix.of (fun k l => A k l a)).adjugate i j :=
  S.coeFn_boundedDomElement _ _

theorem bounded_localizedWeights (ε : ℝ) (hε : 0 < ε) (A : Fin d → Fin d → Ω → ℝ)
    (hA : ∀ i j, A i j ∈ S.boundedDomAlgebra) (i j : Fin d) :
    AEBounded (μ := μ) (S.localizedWeights ε hε A hA i j : Lp ℝ 2 μ) :=
  S.bounded_boundedDomElement _ _

/-- adj(A) A = det(A) I gives the localized inverse identity a.e. -/
theorem localizedWeights_inverse (u : Fin d → S.dom) (ε : ℝ) (hε : 0 < ε)
    (A : Fin d → Fin d → Ω → ℝ) (hA : ∀ i j, A i j ∈ S.boundedDomAlgebra)
    (hΓ : ∀ j k, A j k =ᵐ[μ] S.Γ (u j) (u k)) (i k : Fin d) :
    ∀ᵐ a ∂μ, ∑ j, (S.localizedWeights ε hε A hA i j : Lp ℝ 2 μ) a *
      S.Γ (u j) (u k) a =
      localizationCutoff ε (Matrix.of (fun j l => A j l a)).det * (if i = k then 1 else 0) := by
  classical
  filter_upwards [ae_all_iff.mpr (fun j => S.coeFn_localizedWeights ε hε A hA i j),
    ae_all_iff.mpr (fun j => hΓ j k)] with a hw hΓ
  simp_rw [hw, ← hΓ, mul_assoc, ← Finset.mul_sum]
  have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i k)
    (Matrix.adjugate_mul (Matrix.of (fun j l => A j l a)))
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Matrix.of_apply] at he
  rw [he, ← mul_assoc, smoothInverse_mul hε]

end ErrorStructure
end ErrorCalculus
