import GeometricMeasure.Analysis.TruncatedBessel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Elliptic Energy

## Main results
Global integration by parts under C¹ and four L² assumptions, energy under C³ and L² through order
three, Young and density. Realization on tests and their convolution, transferred L² bound; controls
and two counterexamples each isolating one assumption.

Bibliographic context: De Philippis–Rindler, pp. 9–10, (2.9)–(2.12). The heat-kernel and energy
estimates specialize the distributional framework.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped Topology RealInnerProductSpace Convolution ContDiff
namespace GeometricMeasure
variable {d : ℕ}

/--
Classical derivative in the canonical orthonormal basis. Source: DPR context, transcription pp.
9–10. Exact scope: parameters, assumptions and conclusion below.
-/
def coordDeriv (a : Fin d) (v : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fderiv ℝ v x (EuclideanSpace.single a 1)

/--
Classical Laplacian, the trace of the Hessian. Source: DPR context, transcription pp. 9–10. Exact
scope: parameters, assumptions and conclusion below.
-/
def euclLaplacian (v : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ a : Fin d, coordDeriv a (coordDeriv a v) x

/--
Squared L² norm; used only with MemLp. Source: DPR context, transcription pp. 9–10. Exact scope:
parameters, assumptions and conclusion below.
-/
def l2Sq (v : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ := ∫ x, v x ^ 2

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem l2Sq_nonneg (v : EuclideanSpace ℝ (Fin d) → ℝ) : 0 ≤ l2Sq v :=
  integral_nonneg (fun _ => sq_nonneg _)

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem contDiff_coordDeriv {v : EuclideanSpace ℝ (Fin d) → ℝ}
    {m n : ℕ∞ω} (hv : ContDiff ℝ n v) (hmn : m + 1 ≤ n) (a : Fin d) :
    ContDiff ℝ m (coordDeriv a v) :=
  (hv.fderiv_right hmn).clm_apply contDiff_const

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem coordDeriv_comm {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : ContDiff ℝ 2 v) (a b : Fin d) :
    coordDeriv a (coordDeriv b v) = coordDeriv b (coordDeriv a v) := by
  funext x
  have hf : Differentiable ℝ (fderiv ℝ v) :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have he (c : Fin d) :
      fderiv ℝ (fun y => (fderiv ℝ v y) (EuclideanSpace.single c 1)) x =
        (fderiv ℝ (fderiv ℝ v) x).flip (EuclideanSpace.single c 1) := by
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add] using
      (fderiv_clm_apply (x := x) (u := fun _ => EuclideanSpace.single c (1 : ℝ))
        (hf x) (differentiableAt_const _))
  change (fderiv ℝ (fun y => (fderiv ℝ v y) (EuclideanSpace.single b 1)) x)
      (EuclideanSpace.single a 1) =
    (fderiv ℝ (fun y => (fderiv ℝ v y) (EuclideanSpace.single a 1)) x)
      (EuclideanSpace.single b 1)
  rw [he, he]
  exact hv.contDiffAt.isSymmSndFDerivAt (by simp) _ _

/--
global integration by parts; the four L² assumptions ensure the three products are L¹. Source: DPR
context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem integral_coordDeriv_mul {p q : EuclideanSpace ℝ (Fin d) → ℝ}
    (hp : ContDiff ℝ 1 p) (hq : ContDiff ℝ 1 q) (a : Fin d)
    (hp2 : MemLp p 2) (hq2 : MemLp q 2)
    (hdp2 : MemLp (coordDeriv a p) 2) (hdq2 : MemLp (coordDeriv a q) 2) :
    (∫ x, coordDeriv a p x * q x) = - ∫ x, p x * coordDeriv a q x := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (v := EuclideanSpace.single a (1 : ℝ))
    (hdp2.integrable_mul hq2) (hp2.integrable_mul hdq2) (hp2.integrable_mul hq2)
    (fun x _ => (hp.differentiable (by norm_num)).differentiableAt)
    (fun x _ => (hq.differentiable (by norm_num)).differentiableAt)
  change (∫ x, p x * coordDeriv a q x) = -∫ x, coordDeriv a p x * q x at h
  linarith

/--
Analytic assumptions, including derivatives through order three. Source: DPR context, transcription
pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
structure L2EnergyData (v : EuclideanSpace ℝ (Fin d) → ℝ) : Prop where
  smooth : ContDiff ℝ 3 v
  l2 : MemLp v 2
  first : ∀ a, MemLp (coordDeriv a v) 2
  second : ∀ a b, MemLp (coordDeriv a (coordDeriv b v)) 2
  third : ∀ a b c, MemLp (coordDeriv a (coordDeriv b (coordDeriv c v))) 2

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integral_mul_coordDeriv_self {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : L2EnergyData v) (a : Fin d) :
    (∫ x, v x * coordDeriv a (coordDeriv a v) x) = -l2Sq (coordDeriv a v) := by
  have h := integral_coordDeriv_mul (hv.smooth.of_le (by norm_num))
    (contDiff_coordDeriv hv.smooth (by norm_num : (1 : ℕ∞ω) + 1 ≤ 3) a)
    a hv.l2 (hv.first a) (hv.first a) (hv.second a a)
  simp only [l2Sq, pow_two] at *
  linarith

/--
Two integrations by parts, with commutation justified by C³. Source: DPR context, transcription pp.
9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem integral_coordDeriv_twice_mul {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : L2EnergyData v) (a b : Fin d) :
    (∫ x, coordDeriv a (coordDeriv a v) x * coordDeriv b (coordDeriv b v) x) =
      l2Sq (coordDeriv b (coordDeriv a v)) := by
  have hfirst (i : Fin d) : ContDiff ℝ 2 (coordDeriv i v) :=
    contDiff_coordDeriv hv.smooth (by norm_num) i
  have hsecond (i j : Fin d) : ContDiff ℝ 1 (coordDeriv i (coordDeriv j v)) :=
    contDiff_coordDeriv (hfirst j) (by norm_num) i
  have h1 := integral_coordDeriv_mul ((hfirst a).of_le (by norm_num)) (hsecond b b)
    a (hv.first a) (hv.second b b) (hv.second a a) (hv.third a b b)
  have hcomm : coordDeriv a (coordDeriv b (coordDeriv b v)) =
      coordDeriv b (coordDeriv b (coordDeriv a v)) := by
    rw [coordDeriv_comm (hfirst b) a b,
      coordDeriv_comm (hv.smooth.of_le (by norm_num)) a b]
  rw [hcomm] at h1
  have h2 := integral_coordDeriv_mul ((hfirst a).of_le (by norm_num)) (hsecond b a)
    b (hv.first a) (hv.second b a) (hv.second b a) (hv.third b b a)
  simp only [l2Sq, pow_two] at *
  linarith

/--
Integrated Hessian/Laplacian identity, rather than a pointwise inequality. Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem l2Sq_laplacian {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : L2EnergyData v) :
    l2Sq (euclLaplacian v) = ∑ a : Fin d, ∑ b : Fin d,
      l2Sq (coordDeriv b (coordDeriv a v)) := by
  have hexp (x : EuclideanSpace ℝ (Fin d)) :
      euclLaplacian v x ^ 2 = ∑ a : Fin d, ∑ b : Fin d,
        coordDeriv a (coordDeriv a v) x * coordDeriv b (coordDeriv b v) x := by
    unfold euclLaplacian
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  unfold l2Sq
  simp_rw [hexp]
  rw [integral_finsetSum Finset.univ (fun a _ =>
    integrable_finsetSum Finset.univ (fun b _ =>
      (show Integrable (fun x => coordDeriv a (coordDeriv a v) x *
        coordDeriv b (coordDeriv b v) x) from
        (hv.second a a).integrable_mul (hv.second b b))))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum Finset.univ (fun b _ =>
    (show Integrable (fun x => coordDeriv a (coordDeriv a v) x *
      coordDeriv b (coordDeriv b v) x) from
      (hv.second a a).integrable_mul (hv.second b b)))]
  apply Finset.sum_congr rfl
  intro b _
  exact integral_coordDeriv_twice_mul hv a b

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem integral_mul_laplacian {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : L2EnergyData v) :
    (∫ x, v x * euclLaplacian v x) = - ∑ a : Fin d, l2Sq (coordDeriv a v) := by
  simp only [euclLaplacian, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun a _ =>
    (show Integrable (fun x => v x * coordDeriv a (coordDeriv a v) x) from
      hv.l2.integrable_mul (hv.second a a)))]
  simp only [integral_mul_coordDeriv_self hv, Finset.sum_neg_distrib]

/--
full elliptic energy identity. Source: DPR context, transcription pp. 9–10. Exact scope: parameters,
assumptions and conclusion below.
-/
theorem l2Sq_sub_laplacian {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : L2EnergyData v) :
    l2Sq (fun x => v x - euclLaplacian v x) =
      l2Sq v + 2 * (∑ a : Fin d, l2Sq (coordDeriv a v)) +
        ∑ a : Fin d, ∑ b : Fin d, l2Sq (coordDeriv b (coordDeriv a v)) := by
  have hl : MemLp (euclLaplacian v) 2 := by
    exact memLp_finsetSum _ (fun a _ => hv.second a a)
  have he : l2Sq (fun x => v x - euclLaplacian v x) =
      l2Sq v - 2 * (∫ x, v x * euclLaplacian v x) + l2Sq (euclLaplacian v) := by
    unfold l2Sq
    simp_rw [sub_sq, mul_assoc]
    have hi : Integrable (fun x => 2 * (v x * euclLaplacian v x)) :=
      (hv.l2.integrable_mul hl).const_mul 2
    rw [integral_add (μ := volume)
      (f := fun x => v x ^ 2 - 2 * (v x * euclLaplacian v x))
      (g := fun x => euclLaplacian v x ^ 2) (hv.l2.integrable_sq.sub hi) hl.integrable_sq,
      integral_sub (μ := volume) (f := fun x => v x ^ 2)
      (g := fun x => 2 * (v x * euclLaplacian v x)) hv.l2.integrable_sq hi]
    rw [integral_const_mul]
  rw [he, integral_mul_laplacian hv, l2Sq_laplacian hv]
  ring

/--
L² consequence in squared form, without ENNReal conversion. Source: DPR context, transcription pp.
9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem l2Sq_coordDeriv_le {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : L2EnergyData v) (a b : Fin d) :
    l2Sq (coordDeriv a (coordDeriv b v)) ≤ l2Sq (fun x => v x - euclLaplacian v x) := by
  rw [l2Sq_sub_laplacian hv]
  have h1 : l2Sq (coordDeriv a (coordDeriv b v)) ≤
      ∑ j : Fin d, l2Sq (coordDeriv j (coordDeriv b v)) :=
    Finset.single_le_sum (f := fun j => l2Sq (coordDeriv j (coordDeriv b v)))
      (fun _ _ => l2Sq_nonneg _) (Finset.mem_univ a)
  have h2 : (∑ j : Fin d, l2Sq (coordDeriv j (coordDeriv b v))) ≤
      ∑ i : Fin d, ∑ j : Fin d, l2Sq (coordDeriv j (coordDeriv i v)) :=
    Finset.single_le_sum (f := fun i => ∑ j : Fin d, l2Sq (coordDeriv j (coordDeriv i v)))
      (fun _ _ => Finset.sum_nonneg (fun _ _ => l2Sq_nonneg _))
      (Finset.mem_univ b)
  have h0 := l2Sq_nonneg v
  have hg : 0 ≤ ∑ i : Fin d, l2Sq (coordDeriv i v) :=
    Finset.sum_nonneg (fun _ _ => l2Sq_nonneg _)
  linarith

/--
Weighted Cauchy–Schwarz obtained from nonnegativity of a square. Source: DPR context, transcription
pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem integral_mul_sq_le {k f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hk : Integrable k) (hkf : Integrable (fun x => k x * f x))
    (hkf2 : Integrable (fun x => k x * f x ^ 2))
    (hkn : ∀ x, 0 ≤ k x) (hkm : (∫ x, k x) = 1) :
    (∫ x, k x * f x) ^ 2 ≤ ∫ x, k x * f x ^ 2 := by
  let c : ℝ := ∫ x, k x * f x
  have hp : 0 ≤ ∫ x, k x * (f x - c) ^ 2 :=
    integral_nonneg (fun x => mul_nonneg (hkn x) (sq_nonneg _))
  have he : (∫ x, k x * (f x - c) ^ 2) =
      (∫ x, k x * f x ^ 2) - 2 * c * (∫ x, k x * f x) + c ^ 2 * (∫ x, k x) := by
    simp_rw [show ∀ x, k x * (f x - c) ^ 2 =
      k x * f x ^ 2 - (2*c) * (k x * f x) + c ^ 2 * k x by intro x; ring]
    rw [integral_add (μ := volume)
      (f := fun x => k x * f x ^ 2 - (2*c) * (k x * f x))
      (g := fun x => c ^ 2 * k x) (hkf2.sub (hkf.const_mul _)) (hk.const_mul _),
      integral_sub (μ := volume) (f := fun x => k x * f x ^ 2)
      (g := fun x => (2*c) * (k x * f x)) hkf2 (hkf.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [he, hkm] at hp
  dsimp [c] at hp
  nlinarith

/--
Young L¹·L² for a nonnegative kernel of mass one, on L¹∩L². Source: DPR context, transcription pp.
9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem scalarConvolution_L2_le {k f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hk : Integrable k) (hkn : ∀ x, 0 ≤ k x) (hkm : (∫ x, k x) = 1)
    (hf : Integrable f) (hf2 : MemLp f 2) :
    MemLp (scalarConvolution k f) 2 ∧
      (∫ x, (scalarConvolution k f x) ^ 2) ≤ ∫ x, f x ^ 2 := by
  have hconv := integrable_scalarConvolution hk hf
  have hbound := integrable_scalarConvolution hk hf2.integrable_sq
  have hb : ∀ᵐ x, scalarConvolution k f x ^ 2 ≤
      scalarConvolution k (fun y => f y ^ 2) x := by
    filter_upwards [hk.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hf,
      hk.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hf2.integrable_sq] with x hx hx2
    exact integral_mul_sq_le hk hx hx2 hkn hkm
  have hsq : Integrable (fun x => scalarConvolution k f x ^ 2) := by
    apply hbound.mono' (hconv.aestronglyMeasurable.pow 2)
    filter_upwards [hb] with x hx
    simpa only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)] using hx
  constructor
  · exact (memLp_two_iff_integrable_sq hconv.aestronglyMeasurable).2 hsq
  · calc
      _ ≤ ∫ x, scalarConvolution k (fun y => f y ^ 2) x := integral_mono_ae hsq hbound hb
      _ = _ := by rw [integral_scalarConvolution hk hf2.integrable_sq, hkm, one_mul]

/--
Actual heat contraction on L¹∩L² inputs, without Fourier analysis. Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem heatKernel_convolution_L2 {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Integrable f) (hf2 : MemLp f 2) :
    MemLp (scalarConvolution (heatKernel d t) f) 2 ∧
      (∫ x, scalarConvolution (heatKernel d t) f x ^ 2) ≤ ∫ x, f x ^ 2 :=
  scalarConvolution_L2_le (integrable_heatKernel d t) (heatKernel_nonneg d t)
    (integral_heatKernel d ht) hf hf2

/--
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem memLp_two_of_integrable_bound {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Integrable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) : MemLp f 2 := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
  apply (hf.norm.const_mul C).mono' (hf.aestronglyMeasurable.pow 2)
  exact ae_of_all _ (fun x => by
    simp only [Pi.pow_apply, pow_two, norm_mul]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

/--
Discriminant of a nonnegative quadratic polynomial. Source: DPR context, transcription pp. 9–10.
Exact scope: parameters, assumptions and conclusion below.
-/
theorem sq_le_mul_of_quadratic_nonneg {A B C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : ℝ, 0 ≤ A - 2 * c * B + c ^ 2 * C) : B ^ 2 ≤ A * C := by
  rcases hC.lt_or_eq with hC | hC
  · have h1 := h (B / C)
    have e : A - 2 * (B / C) * B + (B / C) ^ 2 * C = A - B ^ 2 / C := by
      field_simp; ring
    rw [e] at h1
    have h2 : B ^ 2 / C ≤ A := by linarith
    rw [div_le_iff₀ hC] at h2
    linarith
  · rw [← hC] at h ⊢
    have hB : B = 0 := by
      by_contra hB
      have h1 := h ((A + 1) / (2 * B))
      have e : A - 2 * ((A + 1) / (2 * B)) * B + ((A + 1) / (2 * B)) ^ 2 * 0 = -1 := by
        field_simp
        ring
      linarith
    rw [hB]
    simp

/--
Weighted Cauchy–Schwarz, with arbitrary mass. Source: DPR context, transcription pp. 9–10. Exact
scope: parameters, assumptions and conclusion below.
-/
theorem integral_mul_sq_le_mul {k f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hk : Integrable k) (hkf : Integrable (fun x => k x * f x))
    (hkf2 : Integrable (fun x => k x * f x ^ 2)) (hkn : ∀ x, 0 ≤ k x) :
    (∫ x, k x * f x) ^ 2 ≤ (∫ x, k x * f x ^ 2) * ∫ x, k x := by
  apply sq_le_mul_of_quadratic_nonneg (integral_nonneg hkn)
  intro c
  have hp : 0 ≤ ∫ x, k x * (f x - c) ^ 2 :=
    integral_nonneg (fun x => mul_nonneg (hkn x) (sq_nonneg _))
  have he : (∫ x, k x * (f x - c) ^ 2) =
      (∫ x, k x * f x ^ 2) - 2 * c * (∫ x, k x * f x) + c ^ 2 * (∫ x, k x) := by
    simp_rw [show ∀ x, k x * (f x - c) ^ 2 =
      k x * f x ^ 2 - (2*c) * (k x * f x) + c ^ 2 * k x by intro x; ring]
    rw [integral_add (μ := volume)
      (f := fun x => k x * f x ^ 2 - (2*c) * (k x * f x))
      (g := fun x => c ^ 2 * k x) (hkf2.sub (hkf.const_mul _)) (hk.const_mul _),
      integral_sub (μ := volume) (f := fun x => k x * f x ^ 2)
      (g := fun x => (2*c) * (k x * f x)) hkf2 (hkf.const_mul _),
      integral_const_mul, integral_const_mul]
  linarith

/--
L² Cauchy–Schwarz in real integrals. Source: DPR context, transcription pp. 9–10. Exact scope:
parameters, assumptions and conclusion below.
-/
theorem integral_mul_sq_le_L2 {F G : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : MemLp F 2) (hG : MemLp G 2) :
    (∫ x, F x * G x) ^ 2 ≤ (∫ x, F x ^ 2) * ∫ x, G x ^ 2 := by
  apply sq_le_mul_of_quadratic_nonneg (integral_nonneg (fun _ => sq_nonneg _))
  intro c
  have hp : 0 ≤ ∫ x, (F x - c * G x) ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hFG : Integrable (fun x => F x * G x) := hF.integrable_mul hG
  have he : (∫ x, (F x - c * G x) ^ 2) =
      (∫ x, F x ^ 2) - 2 * c * (∫ x, F x * G x) + c ^ 2 * (∫ x, G x ^ 2) := by
    simp_rw [show ∀ x, (F x - c * G x) ^ 2 =
      F x ^ 2 - (2*c) * (F x * G x) + c ^ 2 * G x ^ 2 by intro x; ring]
    rw [integral_add (μ := volume)
      (f := fun x => F x ^ 2 - (2*c) * (F x * G x))
      (g := fun x => c ^ 2 * G x ^ 2) (hF.integrable_sq.sub (hFG.const_mul _))
      (hG.integrable_sq.const_mul _),
      integral_sub (μ := volume) (f := fun x => F x ^ 2)
      (g := fun x => (2*c) * (F x * G x)) hF.integrable_sq (hFG.const_mul _),
      integral_const_mul, integral_const_mul]
  linarith

/--
L² Minkowski in real integrals. Source: DPR context, transcription pp. 9–10. Exact scope:
parameters, assumptions and conclusion below.
-/
theorem sqrt_integral_sq_add_le {F G : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : MemLp F 2) (hG : MemLp G 2) :
    Real.sqrt (∫ x, (F x + G x) ^ 2) ≤
      Real.sqrt (∫ x, F x ^ 2) + Real.sqrt (∫ x, G x ^ 2) := by
  have hA : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hC : 0 ≤ ∫ x, G x ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hFG : Integrable (fun x => F x * G x) := hF.integrable_mul hG
  have hcs := integral_mul_sq_le_L2 hF hG
  have hB : (∫ x, F x * G x) ≤ Real.sqrt (∫ x, F x ^ 2) * Real.sqrt (∫ x, G x ^ 2) := by
    rw [← Real.sqrt_mul hA]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hcs)
  have he : (∫ x, (F x + G x) ^ 2) =
      (∫ x, F x ^ 2) + 2 * (∫ x, F x * G x) + (∫ x, G x ^ 2) := by
    simp_rw [show ∀ x, (F x + G x) ^ 2 =
      F x ^ 2 + 2 * (F x * G x) + G x ^ 2 by intro x; ring]
    rw [integral_add (μ := volume)
      (f := fun x => F x ^ 2 + 2 * (F x * G x))
      (g := fun x => G x ^ 2) (hF.integrable_sq.add (hFG.const_mul _)) hG.integrable_sq,
      integral_add (μ := volume) (f := fun x => F x ^ 2)
      (g := fun x => 2 * (F x * G x)) hF.integrable_sq (hFG.const_mul _),
      integral_const_mul]
  have hsa := Real.sq_sqrt hA
  have hsc := Real.sq_sqrt hC
  have hle : (∫ x, (F x + G x) ^ 2) ≤
      (Real.sqrt (∫ x, F x ^ 2) + Real.sqrt (∫ x, G x ^ 2)) ^ 2 := by
    rw [he]
    nlinarith
  calc Real.sqrt (∫ x, (F x + G x) ^ 2) ≤
      Real.sqrt ((Real.sqrt (∫ x, F x ^ 2) + Real.sqrt (∫ x, G x ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = _ := Real.sqrt_sq (by positivity)

/--
Young L¹·L² for a signed kernel: ‖K*f‖₂² ≤ ‖K‖₁² ‖f‖₂², f ∈ L¹ ∩ L². Source: DPR context,
transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion below.
-/
theorem scalarConvolution_L2_bound {K f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hK : Integrable K) (hf : Integrable f) (hf2 : MemLp f 2) :
    MemLp (scalarConvolution K f) 2 ∧
      (∫ x, scalarConvolution K f x ^ 2) ≤ (∫ x, ‖K x‖) ^ 2 * ∫ x, f x ^ 2 := by
  set N := ∫ x, ‖K x‖ with hN
  have hKn : Integrable (fun y => ‖K y‖) := hK.norm
  have hsq : Integrable (fun y => f y ^ 2) := hf2.integrable_sq
  have hbound := integrable_scalarConvolution hKn hsq
  have hconv := integrable_scalarConvolution hK hf
  have hb : ∀ᵐ x, scalarConvolution K f x ^ 2 ≤
      N * scalarConvolution (fun y => ‖K y‖) (fun y => f y ^ 2) x := by
    filter_upwards [hKn.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hf.norm,
      hKn.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hsq] with x hx hx2
    have h1 : |scalarConvolution K f x| ≤ ∫ y, ‖K y‖ * ‖f (x - y)‖ := by
      rw [scalarConvolution_apply, ← Real.norm_eq_abs]
      simpa only [norm_mul] using norm_integral_le_integral_norm (fun y => K y * f (x - y))
    have hx' : Integrable (fun y => ‖K y‖ * ‖f (x - y)‖) := hx
    have hx2' : Integrable (fun y => ‖K y‖ * ‖f (x - y)‖ ^ 2) := by
      have h : Integrable (fun y => ‖K y‖ * f (x - y) ^ 2) := hx2
      simpa only [Real.norm_eq_abs, sq_abs] using h
    have h2 := integral_mul_sq_le_mul (k := fun y => ‖K y‖) (f := fun y => ‖f (x - y)‖)
      hKn hx' hx2' (fun _ => norm_nonneg _)
    have h3 : (∫ y, ‖K y‖ * ‖f (x - y)‖ ^ 2) =
        scalarConvolution (fun y => ‖K y‖) (fun y => f y ^ 2) x := by
      rw [scalarConvolution_apply]
      simp only [Real.norm_eq_abs, sq_abs]
    calc scalarConvolution K f x ^ 2 = |scalarConvolution K f x| ^ 2 := (sq_abs _).symm
      _ ≤ (∫ y, ‖K y‖ * ‖f (x - y)‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ (∫ y, ‖K y‖ * ‖f (x - y)‖ ^ 2) * N := h2
      _ = N * scalarConvolution (fun y => ‖K y‖) (fun y => f y ^ 2) x := by rw [h3, mul_comm]
  have hsqi : Integrable (fun x => scalarConvolution K f x ^ 2) := by
    apply (hbound.const_mul N).mono' (hconv.aestronglyMeasurable.pow 2)
    filter_upwards [hb] with x hx
    simpa only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)] using hx
  constructor
  · exact (memLp_two_iff_integrable_sq hconv.aestronglyMeasurable).2 hsqi
  · calc _ ≤ ∫ x, N * scalarConvolution (fun y => ‖K y‖) (fun y => f y ^ 2) x :=
          integral_mono_ae hsqi (hbound.const_mul N) hb
      _ = N * (N * ∫ x, f x ^ 2) := by
          rw [integral_const_mul, integral_scalarConvolution hKn hsq]
      _ = _ := by ring

/--
Exact consequence of the extension H_t=0 for t≤0. Source: DPR context, transcription pp. 9–10. Exact
scope: parameters, assumptions and conclusion below.
-/
theorem truncatedBessel_nonpositive_time (d : ℕ) {η : ℝ} (hη : η ≤ 0) :
    truncatedBessel d η = besselKernel d := by
  funext x
  unfold truncatedBessel besselKernel
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    by_cases ht : 0 < t
    · have hηt : η < t := lt_of_le_of_lt hη ht
      simp [Set.indicator, ht, hηt]
    · have hz : heatKernel d t x = 0 := by simp only [heatKernel, if_neg ht]
      simp [Set.indicator, hz])

/--
A single assumption removed: η≥0 in the mass formula. Source: DPR context, transcription pp. 9–10.
Exact scope: parameters, assumptions and conclusion below.
-/
theorem counterexample_truncated_mass_negative_time (d : ℕ) :
    (∫ x, truncatedBessel d (-1) x) = 1 ∧
    (∫ x, truncatedBessel d (-1) x) ≠ Real.exp (-(-1 : ℝ)) := by
  rw [truncatedBessel_nonpositive_time d (by norm_num), integral_besselKernel]
  constructor
  · rfl
  · have h : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    norm_num only [neg_neg]
    exact ne_of_lt h

/--
Algebraic identities for the power-integral coefficients; no kernel estimate is assumed established.
Source: DPR context, transcription pp. 9–10. Exact scope: parameters, assumptions and conclusion
below.
-/
theorem inv_add_coefficients_le {D : ℝ} (hD : 1 ≤ D) :
    1 / (2 * (D + 2)) + 1 / (D + 4) ≤ 1 ∧
    1 / (2 * (D + 2)) + 1 / D ≤ 2 ∧
    1 / (4 * D) + 3 / (2 * (D + 2)) ≤ 1 ∧
    1 / (4 * (D + 4)) + 3 / (2 * (D + 2)) ≤ 2 := by
  have h1 : 1 / (2 * (D + 2)) ≤ (1 / 6 : ℝ) := by
    apply (div_le_iff₀ (by linarith)).2
    linarith
  have h2 : 1 / (D + 4) ≤ (1 / 5 : ℝ) := by
    apply (div_le_iff₀ (by linarith)).2
    linarith
  have h3 : 1 / D ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (by linarith)).2
    linarith
  have h4 : 1 / (4 * D) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (by linarith)).2
    linarith
  have h5 : 3 / (2 * (D + 2)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by linarith)).2
    linarith
  have h6 : 1 / (4 * (D + 4)) ≤ (1 / 20 : ℝ) := by
    apply (div_le_iff₀ (by linarith)).2
    linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end GeometricMeasure
