import Foundations.MehlerD.Markov
import Foundations.LogSobolev.EntropyLimit
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate derivative, including on the zero-dimensional space. -/
def partialD (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

structure IsC1BoundedD (f : (ι → ℝ) → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 f
  bounded : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
  partial_bounded : ∀ i, ∃ C : ℝ, ∀ x, ‖partialD f i x‖ ≤ C

def IsC2BoundedD (f : (ι → ℝ) → ℝ) : Prop :=
  IsC1BoundedD f ∧ ∀ i, IsC1BoundedD (partialD f i)

def gradNormSqD (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ := ∑ i, (partialD f i x)^2

theorem IsC1BoundedD.hasFDerivAt {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (x) :
    HasFDerivAt f (fderiv ℝ f x) x := (hf.contDiff.differentiable (by norm_num) x).hasFDerivAt

theorem IsC1BoundedD.continuous_partial {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (i) :
    Continuous (partialD f i) := by
  exact (hf.contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem fderiv_eq_sum_partialD (f : (ι → ℝ) → ℝ) (x v : ι → ℝ) :
    fderiv ℝ f x v = ∑ i, v i * partialD f i x := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [partialD, map_sum]

theorem IsC1BoundedD.fderiv_bounded {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ C := by
  choose C hC using hf.partial_bounded
  have hC0 : ∀ i, 0 ≤ C i := fun i => (norm_nonneg _).trans (hC i 0)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC0 i), fun x => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun i _ => hC0 i))
  intro v
  rw [fderiv_eq_sum_partialD]
  calc
    _ ≤ ∑ i, ‖v i * partialD f i x‖ := norm_sum_le _ _
    _ ≤ ∑ i, C i * ‖v‖ := Finset.sum_le_sum fun i _ => by
      rw [norm_mul, mul_comm]
      exact mul_le_mul (hC i x) (norm_le_pi_norm v i) (norm_nonneg _) (hC0 i)
    _ = _ := (Finset.sum_mul ..).symm

theorem memLp_gaussianD_of_bounded {E : Type*} [NormedAddCommGroup E]
    {f : (ι → ℝ) → E} (hf : Continuous f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (p : ENNReal) : MemLp f p (gaussianProduct ι) := by
  obtain ⟨C,hC⟩ := hb
  exact MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)

theorem IsC1BoundedD.memLp {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (p : ENNReal) :
    MemLp f p (gaussianProduct ι) := memLp_gaussianD_of_bounded hf.contDiff.continuous hf.bounded p

theorem IsC1BoundedD.memLp_partial {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f)
    (i) (p : ENNReal) : MemLp (partialD f i) p (gaussianProduct ι) :=
  memLp_gaussianD_of_bounded (hf.continuous_partial i) (hf.partial_bounded i) p

theorem partialD_const (c : ℝ) (i : ι) (x : ι → ℝ) : partialD (fun _ => c) i x = 0 := by
  simp [partialD]

theorem partialD_add {f g : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (hg : IsC1BoundedD g) (i x) :
    partialD (fun x => f x+g x) i x = partialD f i x+partialD g i x := by
  simpa only [Pi.add_def, ContinuousLinearMap.add_apply, partialD] using
    congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) ((hf.hasFDerivAt x).add (hg.hasFDerivAt x)).fderiv

theorem partialD_mul {f g : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (hg : IsC1BoundedD g) (i x) :
    partialD (fun x => f x*g x) i x = partialD f i x*g x+f x*partialD g i x := by
  simpa [Pi.mul_def, partialD, mul_comm, add_comm] using
    congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) ((hf.hasFDerivAt x).mul (hg.hasFDerivAt x)).fderiv

theorem IsC1BoundedD.const (c : ℝ) : IsC1BoundedD (fun _ : ι → ℝ => c) := by
  exact ⟨contDiff_const,⟨‖c‖,fun _ => le_rfl⟩,fun i => ⟨0,by simp [partialD_const]⟩⟩

theorem IsC1BoundedD.add {f g : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (hg : IsC1BoundedD g) :
    IsC1BoundedD (fun x => f x+g x) := by
  obtain ⟨C,hC⟩ := hf.bounded
  obtain ⟨D,hD⟩ := hg.bounded
  refine ⟨hf.contDiff.add hg.contDiff,⟨C+D,fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩,?_⟩
  intro i
  obtain ⟨C',hC'⟩ := hf.partial_bounded i
  obtain ⟨D',hD'⟩ := hg.partial_bounded i
  refine ⟨C'+D',fun x => ?_⟩
  rw [partialD_add hf hg]
  exact (norm_add_le _ _).trans (add_le_add (hC' x) (hD' x))

theorem IsC1BoundedD.mul {f g : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (hg : IsC1BoundedD g) :
    IsC1BoundedD (fun x => f x*g x) := by
  obtain ⟨C,hC⟩ := hf.bounded
  obtain ⟨D,hD⟩ := hg.bounded
  have hC0 := (norm_nonneg (f 0)).trans (hC 0)
  refine ⟨hf.contDiff.mul hg.contDiff,⟨C*D,fun x => ?_⟩,?_⟩
  · rw [norm_mul]; exact mul_le_mul (hC x) (hD x) (norm_nonneg _) hC0
  · intro i
    obtain ⟨C',hC'⟩ := hf.partial_bounded i
    obtain ⟨D',hD'⟩ := hg.partial_bounded i
    refine ⟨C'*D+C*D',fun x => ?_⟩
    rw [partialD_mul hf hg]
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    exact add_le_add (mul_le_mul (hC' x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (hC' 0)))
      (mul_le_mul (hC x) (hD' x) (norm_nonneg _) hC0)

theorem IsC1BoundedD.const_mul {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (c : ℝ) :
    IsC1BoundedD (fun x => c*f x) := (IsC1BoundedD.const c).mul hf

theorem partialD_const_mul {f : (ι → ℝ) → ℝ} (hf : IsC1BoundedD f) (c : ℝ) (i x) :
    partialD (fun x => c*f x) i x = c*partialD f i x := by
  simp [partialD_mul (IsC1BoundedD.const c) hf,partialD_const]

theorem IsC2BoundedD.const (c : ℝ) : IsC2BoundedD (fun _ : ι → ℝ => c) := by
  refine ⟨IsC1BoundedD.const c,fun i => ?_⟩
  simpa only [funext (partialD_const c i)] using IsC1BoundedD.const (ι := ι) 0

theorem IsC2BoundedD.add {f g : (ι → ℝ) → ℝ} (hf : IsC2BoundedD f) (hg : IsC2BoundedD g) :
    IsC2BoundedD (fun x => f x+g x) := by
  refine ⟨hf.1.add hg.1,fun i => ?_⟩
  simpa only [funext (partialD_add hf.1 hg.1 i)] using (hf.2 i).add (hg.2 i)

theorem IsC2BoundedD.mul {f g : (ι → ℝ) → ℝ} (hf : IsC2BoundedD f) (hg : IsC2BoundedD g) :
    IsC2BoundedD (fun x => f x*g x) := by
  refine ⟨hf.1.mul hg.1,fun i => ?_⟩
  simpa only [funext (partialD_mul hf.1 hg.1 i)] using
    ((hf.2 i).mul hg.1).add (hf.1.mul (hg.2 i))

end Foundations
