import Foundations.MehlerD.Hermite
import Foundations.HermiteD.Basis
import Foundations.Semigroup.Contractive
import Mathlib.Topology.EMetricSpace.Lipschitz

noncomputable section
open Filter Topology Set MeasureTheory
open scoped InnerProductSpace
namespace Foundations
variable {ι : Type*} [Fintype ι]

theorem clm_ext_hermiteD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : Lp ℝ 2 (gaussianProduct ι) →L[ℝ] E)
    (h : ∀ n, A (hermiteNormalizedD n) = B (hermiteNormalizedD n)) : A = B := by
  ext f
  have ha := A.hasSum (hasSum_hermiteD_expansion f)
  have hb := B.hasSum (hasSum_hermiteD_expansion f)
  apply HasSum.unique ha
  simpa only [map_smul, h] using hb

theorem hasSum_mehlerD {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (gaussianProduct ι)) :
    HasSum (fun n : ι → ℕ => (Real.exp (-(hermiteDegreeD n : ℝ)*t) * hermiteD_coeff f n) • hermiteNormalizedD n)
      (mehlerD t f) := by
  simpa only [map_smul, mehlerD_hermiteNormalized ht, smul_smul, mul_comm] using
    (mehlerD t).hasSum (hasSum_hermiteD_expansion f)

theorem mehler_eq_spectralD {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (gaussianProduct ι)) :
    mehlerD t f = ∑' n : ι → ℕ, (Real.exp (-(hermiteDegreeD n : ℝ)*t) * hermiteD_coeff f n) • hermiteNormalizedD n :=
  (hasSum_mehlerD ht f).tsum_eq.symm

theorem mehler_addD {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    mehlerD (ι := ι) (s+t) = mehlerD s * mehlerD t := by
  apply clm_ext_hermiteD
  intro n
  simp only [mul_apply_eq_comp, mehlerD_hermiteNormalized (add_nonneg hs ht),
    mehlerD_hermiteNormalized ht, map_smul, mehlerD_hermiteNormalized hs, smul_smul]
  rw [mul_add, Real.exp_add, mul_comm]

theorem mehler_inner_hermiteD {t : ℝ} (ht : 0 ≤ t) (n : ι → ℕ) (f : Lp ℝ 2 (gaussianProduct ι)) :
    ⟪hermiteNormalizedD n, mehlerD t f⟫_ℝ =
      Real.exp (-(hermiteDegreeD n : ℝ)*t) * ⟪hermiteNormalizedD n, f⟫_ℝ := by
  have h : (innerSL ℝ (hermiteNormalizedD n)).comp (mehlerD t) =
      Real.exp (-(hermiteDegreeD n : ℝ)*t) • innerSL ℝ (hermiteNormalizedD n) := by
    apply clm_ext_hermiteD
    intro m
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      mehlerD_hermiteNormalized ht, innerSL_apply_apply, inner_smul_right, smul_eq_mul,
      (orthonormal_iff_ite.mp orthonormal_hermiteNormalizedD)]
    by_cases he : n=m
    · subst m; simp
    · simp [he]
  exact congrArg (fun T : Lp ℝ 2 (gaussianProduct ι) →L[ℝ] ℝ => T f) h

theorem hermite_coeff_mehlerD {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (gaussianProduct ι)) (n : ι → ℕ) :
    hermiteD_coeff (mehlerD t f) n = Real.exp (-(hermiteDegreeD n : ℝ)*t) * hermiteD_coeff f n := by
  simpa only [hermiteD_coeff, real_inner_comm] using mehler_inner_hermiteD ht n f

theorem mehler_selfAdjointD {t : ℝ} (ht : 0 ≤ t) (f g : Lp ℝ 2 (gaussianProduct ι)) :
    ⟪mehlerD t f, g⟫_ℝ = ⟪f, mehlerD t g⟫_ℝ := by
  have h : (innerSL ℝ g).comp (mehlerD t) = innerSL ℝ (mehlerD t g) := by
    apply clm_ext_hermiteD
    intro n
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      mehlerD_hermiteNormalized ht, inner_smul_right]
    simpa only [real_inner_comm] using (mehler_inner_hermiteD ht n g).symm
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm] using
    congrArg (fun T : Lp ℝ 2 (gaussianProduct ι) →L[ℝ] ℝ => T f) h

theorem mehler_positiveD {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (gaussianProduct ι)) :
    0 ≤ ⟪mehlerD t f, f⟫_ℝ := by
  have hh : 0 ≤ t/2 := by linarith
  have he : mehlerD (ι := ι) t = mehlerD (t/2) * mehlerD (t/2) := by
    simpa using mehler_addD hh hh
  rw [he, mul_apply_eq_comp, mehler_selfAdjointD hh]
  exact real_inner_self_nonneg

theorem continuous_mehler_applyD (f : Lp ℝ 2 (gaussianProduct ι)) :
    ContinuousOn (fun t : ℝ => mehlerD t f) (Ici 0) := by
  have hd : Dense (Submodule.span ℝ (range (hermiteNormalizedD (ι := ι))) : Set (Lp ℝ 2 (gaussianProduct ι))) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (dense_span_hermiteD (ι := ι))
  have hc : Continuous (fun z : Lp ℝ 2 (gaussianProduct ι) × Ici (0:ℝ) => mehlerD z.2 z.1) := by
    apply continuous_prod_of_dense_continuous_lipschitzWith _ 1 hd
    · intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨n,rfl⟩ := hg
        have h : Continuous (fun t : Ici (0:ℝ) =>
            Real.exp (-(hermiteDegreeD n : ℝ)*(t:ℝ)) • hermiteNormalizedD n) := by fun_prop
        exact h.congr (fun t => (mehlerD_hermiteNormalized t.property n).symm)
      | zero => simpa using (continuous_const : Continuous (fun _ : Ici (0:ℝ) => (0 : Lp ℝ 2 (gaussianProduct ι))))
      | add g h hg hh ihg ihh => simpa only [map_add, Pi.add_def] using ihg.add ihh
      | smul a g hg ih => simpa only [map_smul, Pi.smul_def] using ih.const_smul a
    · intro t
      apply LipschitzWith.of_dist_le_mul
      intro g h
      simpa only [dist_eq_norm, NNReal.coe_one, one_mul, ← map_sub] using
        norm_mehlerD_apply_le t.property (g-h)
  rw [continuousOn_iff_continuous_restrict]
  exact hc.comp (continuous_const.prodMk continuous_id)

def mehlerSemigroupD : ContractionSemigroup (Lp ℝ 2 (gaussianProduct ι)) where
  S := mehlerD
  norm_le := norm_mehlerD_le_one
  zero := mehlerD_zero
  add := mehler_addD
  continuous := continuous_mehler_applyD

end Foundations
