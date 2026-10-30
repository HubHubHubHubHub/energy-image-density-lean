import Foundations.Mehler.Hermite
import Foundations.Hermite.Basis
import Foundations.Semigroup.Contractive
import Mathlib.Topology.EMetricSpace.Lipschitz

noncomputable section
open Filter Topology Set MeasureTheory
open scoped InnerProductSpace
namespace Foundations

theorem clm_ext_hermite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : Lp ℝ 2 standardGaussian →L[ℝ] E)
    (h : ∀ n, A (hermiteNormalized n) = B (hermiteNormalized n)) : A = B := by
  ext f
  have ha := A.hasSum (hasSum_hermite_expansion f)
  have hb := B.hasSum (hasSum_hermite_expansion f)
  apply HasSum.unique ha
  simpa only [map_smul, h] using hb

theorem hasSum_mehler {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 standardGaussian) :
    HasSum (fun n : ℕ => (Real.exp (-(n:ℝ)*t) * hermite_coeff f n) • hermiteNormalized n)
      (mehler t f) := by
  simpa only [map_smul, mehler_hermiteNormalized ht, smul_smul, mul_comm] using
    (mehler t).hasSum (hasSum_hermite_expansion f)

theorem mehler_eq_spectral {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 standardGaussian) :
    mehler t f = ∑' n : ℕ, (Real.exp (-(n:ℝ)*t) * hermite_coeff f n) • hermiteNormalized n :=
  (hasSum_mehler ht f).tsum_eq.symm

theorem mehler_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    mehler (s+t) = mehler s * mehler t := by
  apply clm_ext_hermite
  intro n
  simp only [mul_apply_eq_comp, mehler_hermiteNormalized (add_nonneg hs ht),
    mehler_hermiteNormalized ht, map_smul, mehler_hermiteNormalized hs, smul_smul]
  rw [mul_add, Real.exp_add, mul_comm]

theorem mehler_inner_hermite {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (f : Lp ℝ 2 standardGaussian) :
    ⟪hermiteNormalized n, mehler t f⟫_ℝ =
      Real.exp (-(n:ℝ)*t) * ⟪hermiteNormalized n, f⟫_ℝ := by
  have h : (innerSL ℝ (hermiteNormalized n)).comp (mehler t) =
      Real.exp (-(n:ℝ)*t) • innerSL ℝ (hermiteNormalized n) := by
    apply clm_ext_hermite
    intro m
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      mehler_hermiteNormalized ht, innerSL_apply_apply, inner_smul_right, smul_eq_mul,
      (orthonormal_iff_ite.mp orthonormal_hermiteNormalized)]
    by_cases he : n=m
    · subst m; simp
    · simp [he]
  exact congrArg (fun T : Lp ℝ 2 standardGaussian →L[ℝ] ℝ => T f) h

theorem hermite_coeff_mehler {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 standardGaussian) (n : ℕ) :
    hermite_coeff (mehler t f) n = Real.exp (-(n:ℝ)*t) * hermite_coeff f n := by
  simpa only [hermite_coeff, real_inner_comm] using mehler_inner_hermite ht n f

theorem mehler_selfAdjoint {t : ℝ} (ht : 0 ≤ t) (f g : Lp ℝ 2 standardGaussian) :
    ⟪mehler t f, g⟫_ℝ = ⟪f, mehler t g⟫_ℝ := by
  have h : (innerSL ℝ g).comp (mehler t) = innerSL ℝ (mehler t g) := by
    apply clm_ext_hermite
    intro n
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      mehler_hermiteNormalized ht, inner_smul_right]
    simpa only [real_inner_comm] using (mehler_inner_hermite ht n g).symm
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm] using
    congrArg (fun T : Lp ℝ 2 standardGaussian →L[ℝ] ℝ => T f) h

theorem mehler_positive {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 standardGaussian) :
    0 ≤ ⟪mehler t f, f⟫_ℝ := by
  have hh : 0 ≤ t/2 := by linarith
  have he : mehler t = mehler (t/2) * mehler (t/2) := by
    simpa using mehler_add hh hh
  rw [he, mul_apply_eq_comp, mehler_selfAdjoint hh]
  exact real_inner_self_nonneg

theorem continuous_mehler_apply (f : Lp ℝ 2 standardGaussian) :
    ContinuousOn (fun t : ℝ => mehler t f) (Ici 0) := by
  have hd : Dense (Submodule.span ℝ (range hermiteNormalized) : Set (Lp ℝ 2 standardGaussian)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (by rw [span_hermiteNormalized_eq, dense_span_hermite])
  have hc : Continuous (fun z : Lp ℝ 2 standardGaussian × Ici (0:ℝ) => mehler z.2 z.1) := by
    apply continuous_prod_of_dense_continuous_lipschitzWith _ 1 hd
    · intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨n,rfl⟩ := hg
        have h : Continuous (fun t : Ici (0:ℝ) =>
            Real.exp (-(n:ℝ)*(t:ℝ)) • hermiteNormalized n) := by fun_prop
        exact h.congr (fun t => (mehler_hermiteNormalized t.property n).symm)
      | zero => simpa using (continuous_const : Continuous (fun _ : Ici (0:ℝ) => (0 : Lp ℝ 2 standardGaussian)))
      | add g h hg hh ihg ihh => simpa only [map_add, Pi.add_def] using ihg.add ihh
      | smul a g hg ih => simpa only [map_smul, Pi.smul_def] using ih.const_smul a
    · intro t
      apply LipschitzWith.of_dist_le_mul
      intro g h
      simpa only [dist_eq_norm, NNReal.coe_one, one_mul, ← map_sub] using
        norm_mehler_apply_le t.property (g-h)
  rw [continuousOn_iff_continuous_restrict]
  exact hc.comp (continuous_const.prodMk continuous_id)

def mehlerSemigroup : ContractionSemigroup (Lp ℝ 2 standardGaussian) where
  S := mehler
  norm_le := norm_mehler_le_one
  zero := mehler_zero
  add := mehler_add
  continuous := continuous_mehler_apply

end Foundations
