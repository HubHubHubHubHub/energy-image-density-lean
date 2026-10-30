import ErrorCalculus.Dirichlet.ErrorStructure
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Instances.Rat
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic

/-!
# Gamma Kernel

## Main results
Countable kernels and the single measurable exceptional set.
-/
noncomputable section
open Classical
set_option maxHeartbeats 800000
open MeasureTheory Filter
namespace ErrorCalculus
variable {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Bilinear extension of a kernel to finitely supported coordinates. -/
def kernelForm (A : ι → ι → ℝ) : (ι →₀ ℝ) →ₗ[ℝ] (ι →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun i => Finsupp.linearCombination ℝ (A i))

theorem kernelForm_apply (A : ι → ι → ℝ) (a b : ι →₀ ℝ) :
    kernelForm A a b = ∑ i ∈ a.support, ∑ j ∈ b.support, a i * b j * A i j := by
  classical
  simp [kernelForm, Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum,
    mul_assoc]

@[simp] theorem kernelForm_single (A : ι → ι → ℝ) (i j : ι) :
    kernelForm A (Finsupp.single i 1) (Finsupp.single j 1) = A i j := by
  simp [kernelForm]

theorem kernelForm_symm (A : ι → ι → ℝ) (hA : ∀ i j, A i j = A j i)
    (a b : ι →₀ ℝ) : kernelForm A a b = kernelForm A b a := by
  rw [kernelForm_apply, kernelForm_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA i j]
  ring

/-- Evaluation of a finite linear combination of L¹ classes. -/
theorem coeFn_linearCombination [Countable ι] (f : ι → Lp ℝ 1 μ) (a : ι →₀ ℝ) :
    Finsupp.linearCombination ℝ f a =ᵐ[μ]
      fun ω => Finsupp.linearCombination ℝ (fun i => f i ω) a := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  filter_upwards [Lp.coeFn_finsetSum a.support (fun i => a i • f i),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i) (f i))] with ω hs ht
  simp only [hs, Finset.sum_apply, ht, Pi.smul_apply, smul_eq_mul]

variable [IsProbabilityMeasure μ] (S : ErrorStructure Ω μ) [Countable ι] (f : ι → S.dom)

/-- The canonical L¹ representatives are measurable and already symmetric everywhere. -/
def rawGammaKernel (ω : Ω) (i j : ι) : ℝ := S.Γ (f i) (f j) ω

theorem rawGammaKernel_measurable (i j : ι) : Measurable (fun ω => rawGammaKernel S f ω i j) :=
  (Lp.stronglyMeasurable _).measurable

theorem rawGammaKernel_symm (ω : Ω) (i j : ι) :
    rawGammaKernel S f ω i j = rawGammaKernel S f ω j i := by
  simp only [rawGammaKernel, S.Γ_symm (f i) (f j)]

theorem rawGammaKernel_ae (a b : ι →₀ ℝ) :
    (fun ω => kernelForm (rawGammaKernel S f ω) a b) =ᵐ[μ]
      S.Γ (Finsupp.linearCombination ℝ f a) (Finsupp.linearCombination ℝ f b) := by
  classical
  have he : S.Γ (Finsupp.linearCombination ℝ f a) (Finsupp.linearCombination ℝ f b) =
      Finsupp.linearCombination ℝ (fun i => Finsupp.linearCombination ℝ
        (fun j => S.Γ (f i) (f j)) b) a := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [he]
  filter_upwards [coeFn_linearCombination (fun i => Finsupp.linearCombination ℝ
      (fun j => S.Γ (f i) (f j)) b) a,
    ae_all_iff.mpr (fun i => coeFn_linearCombination (fun j => S.Γ (f i) (f j)) b)]
    with ω ha hb
  rw [ha]
  simp_rw [hb]
  simp [kernelForm, Finsupp.linearCombination_apply, Finsupp.sum, rawGammaKernel,
    Finset.mul_sum, mul_assoc]

/-- Only countably many finite rational tests are used to define the good set. -/
def gammaGood : Set Ω := {ω | ∀ (s : Finset ι) (q : s → ℚ),
  0 ≤ ∑ i : s, ∑ j : s, (q i : ℝ) * (q j : ℝ) * rawGammaKernel S f ω i j}

theorem gammaGood_measurable : MeasurableSet (gammaGood S f) := by
  classical
  simp only [gammaGood, Set.setOf_forall]
  exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun q =>
    measurableSet_le measurable_const (by
      exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
        measurable_const.mul (rawGammaKernel_measurable S f i j))

theorem gammaGood_ae : ∀ᵐ ω ∂μ, ω ∈ gammaGood S f := by
  classical
  apply ae_all_iff.mpr
  intro s
  apply ae_all_iff.mpr
  intro q
  let a : ι →₀ ℝ := ∑ i : s, (q i : ℝ) • Finsupp.single (i : ι) 1
  filter_upwards [rawGammaKernel_ae S f a a,
    S.Γ_nonneg (Finsupp.linearCombination ℝ f a)] with ω he hp
  rw [← he] at hp
  simp only [a, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, kernelForm_single, Finset.mul_sum] at hp
  rw [Finset.sum_comm] at hp
  simpa only [mul_assoc, mul_left_comm, mul_comm, Pi.zero_apply] using hp

/-- Continuity in each finite coefficient space upgrades rational tests to real tests. -/
theorem gammaGood_nonneg (ω : Ω) (hω : ω ∈ gammaGood S f) (a : ι →₀ ℝ) :
    0 ≤ kernelForm (rawGammaKernel S f ω) a a := by
  classical
  have hd : DenseRange (fun q : a.support → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hn : ∀ v : a.support → ℝ,
      0 ≤ ∑ i : a.support, ∑ j : a.support, v i * v j * rawGammaKernel S f ω i j := by
    intro v
    exact hd.induction_on v (isClosed_le continuous_const (by fun_prop)) (hω a.support)
  rw [kernelForm_apply]
  have hh := hn (fun i => a i)
  simp only [Finset.univ_eq_attach] at hh
  convert hh using 1
  exact (Finset.sum_attach a.support (fun i => ∑ j ∈ a.support, a i * a j * rawGammaKernel S f ω i j)).symm.trans (by
    apply Finset.sum_congr rfl
    intro i hi
    exact (Finset.sum_attach a.support (fun j => a i * a j * rawGammaKernel S f ω i j)).symm)

/-- One measurable null set is corrected, before any uncountable quantification. -/
def positiveGammaKernel (ω : Ω) (i j : ι) : ℝ :=
  if ω ∈ gammaGood S f then rawGammaKernel S f ω i j else 0

theorem positiveGammaKernel_measurable (i j : ι) :
    Measurable (fun ω => positiveGammaKernel S f ω i j) :=
  Measurable.ite (gammaGood_measurable S f) (rawGammaKernel_measurable S f i j) measurable_const

theorem positiveGammaKernel_symm (ω : Ω) (i j : ι) :
    positiveGammaKernel S f ω i j = positiveGammaKernel S f ω j i := by
  simp only [positiveGammaKernel, rawGammaKernel_symm S f ω i j]

theorem positiveGammaKernel_nonneg (ω : Ω) (a : ι →₀ ℝ) :
    0 ≤ kernelForm (positiveGammaKernel S f ω) a a := by
  classical
  by_cases hω : ω ∈ gammaGood S f
  · have he : positiveGammaKernel S f ω = rawGammaKernel S f ω := by
      funext i j; exact if_pos hω
    rw [he]
    exact gammaGood_nonneg S f ω hω a
  · simp [positiveGammaKernel, hω, kernelForm_apply]

theorem positiveGammaKernel_ae (a b : ι →₀ ℝ) :
    (fun ω => kernelForm (positiveGammaKernel S f ω) a b) =ᵐ[μ]
      S.Γ (Finsupp.linearCombination ℝ f a) (Finsupp.linearCombination ℝ f b) := by
  filter_upwards [gammaGood_ae S f, rawGammaKernel_ae S f a b] with ω hω he
  have hk : positiveGammaKernel S f ω = rawGammaKernel S f ω := by
    funext i j; exact if_pos hω
  rw [hk]
  exact he

end ErrorCalculus
