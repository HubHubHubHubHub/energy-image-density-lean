import Foundations.Sobolev1D.Local
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Foundations

/-- The oriented primitive, based at zero. -/
def primitive (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, g t

/-- The representative with prescribed value at zero. -/
def primitiveRepresentative (c : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ := c + primitive g x

theorem intervalIntegrable_of_locallyIntegrable {g : ℝ → ℝ}
    (hg : LocallyIntegrable g volume) (a b : ℝ) : IntervalIntegrable g volume a b :=
  intervalIntegrable_iff.mpr ((hg.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

theorem continuous_representative {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) (c : ℝ) :
    Continuous (primitiveRepresentative c g) :=
  continuous_const.add (intervalIntegral.continuous_primitive (intervalIntegrable_of_locallyIntegrable hg) 0)

theorem representative_sub_eq_integral {g : ℝ → ℝ} (hg : LocallyIntegrable g volume)
    (c a b : ℝ) : primitiveRepresentative c g b - primitiveRepresentative c g a = ∫ t in a..b, g t := by
  simp only [primitiveRepresentative, add_sub_add_left_eq_sub, primitive]
  exact intervalIntegral.integral_interval_sub_left (intervalIntegrable_of_locallyIntegrable hg 0 b)
    (intervalIntegrable_of_locallyIntegrable hg 0 a)

theorem absolutelyContinuousOnInterval_representative {g : ℝ → ℝ}
    (hg : LocallyIntegrable g volume) (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (primitiveRepresentative c g) a b := by
  have he : primitiveRepresentative c g =
      (fun _ => primitiveRepresentative c g a) + (fun x => ∫ t in a..x, g t) := by
    ext x
    have h := representative_sub_eq_integral hg c a x
    simp only [Pi.add_apply]
    linarith
  rw [he]
  exact ((LipschitzWith.const (primitiveRepresentative c g a)).lipschitzOnWith.absolutelyContinuousOnInterval).add
    ((intervalIntegrable_of_locallyIntegrable hg a b).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)

/-- Lebesgue differentiation identifies the derivative almost everywhere. -/
theorem ae_hasDerivAt_representative {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) (c : ℝ) :
    ∀ᵐ x ∂volume, HasDerivAt (primitiveRepresentative c g) (g x) x := by
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hg] with x hx
  exact (hx 0).const_add c

theorem deriv_representative_ae_eq {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) (c : ℝ) :
    deriv (primitiveRepresentative c g) =ᵐ[volume] g :=
  (ae_hasDerivAt_representative hg c).mono (fun _ hx => hx.deriv)

/-- The C¹ fundamental theorem, in the normalization used for the approximants. -/
theorem primitive_deriv_eq_sub {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ) :
    primitive (deriv f) x = f x - f 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    exact (hf.differentiable one_ne_zero t).hasDerivAt
  · exact hf.continuous_deriv_one.intervalIntegrable _ _

/-- Uniform control by the local L¹ norm on an interval containing zero and x. -/
theorem norm_primitive_le_integral_abs {g : ℝ → ℝ} (hg : LocallyIntegrable g volume)
    {R x : ℝ} (hR : 0 ≤ R) (hx : x ∈ Icc (-R) R) :
    ‖primitive g x‖ ≤ ∫ t in Icc (-R) R, ‖g t‖ := by
  apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
  apply setIntegral_mono_set (hg.integrableOn_isCompact isCompact_Icc).norm
    (Eventually.of_forall (fun t => norm_nonneg _))
  apply Eventually.of_forall
  intro t ht
  have hsub : uIcc (0:ℝ) x ⊆ Icc (-R) R :=
    uIcc_subset_Icc (by constructor <;> linarith) hx
  exact hsub (uIoc_subset_uIcc ht)

/-- Convergence of weighted L² functions gives uniform convergence of primitives on compacts. -/
theorem tendstoUniformlyOn_primitive_Icc {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (densityMeasure ρ)) (hg : MemLp g 2 (densityMeasure ρ))
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun n => primitive (f n)) (primitive g) atTop (Icc (-R) R) := by
  have hlocal := tendsto_integral_abs_sub_of_density hρ hpos hf hg hlim (K := Icc (-R) R) isCompact_Icc
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hlocal.eventually (gt_mem_nhds hε)] with n hn
  intro x hx
  have hfl := locallyIntegrable_of_memLp_density hρ hpos (hf n)
  have hgl := locallyIntegrable_of_memLp_density hρ hpos hg
  have he : primitive (f n) x - primitive g x = primitive (f n - g) x := by
    exact (intervalIntegral.integral_sub (intervalIntegrable_of_locallyIntegrable hfl 0 x)
      (intervalIntegrable_of_locallyIntegrable hgl 0 x)).symm
  rw [dist_comm, dist_eq_norm, he]
  exact (norm_primitive_le_integral_abs (hfl.sub hgl) hR hx).trans_lt hn

theorem tendsto_primitive {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (densityMeasure ρ)) (hg : MemLp g 2 (densityMeasure ρ))
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) (x : ℝ) :
    Tendsto (fun n => primitive (f n) x) atTop (𝓝 (primitive g x)) :=
  (tendstoUniformlyOn_primitive_Icc hρ hpos hf hg hlim |x| (abs_nonneg x)).tendsto_at
    ⟨neg_abs_le x, le_abs_self x⟩

end Foundations
