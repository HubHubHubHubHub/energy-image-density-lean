import Foundations.LogSobolevD.BoundedCalculus
import Foundations.LogSobolevD.Fisher
import Foundations.LogSobolevD.MehlerTime

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations

/-- Entropy for an arbitrary measurable space. Its integrability is a separate conclusion. -/
def entropyOf {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) : ℝ :=
  (∫ x, f x*Real.log (f x) ∂μ) - (∫ x, f x ∂μ)*Real.log (∫ x, f x ∂μ)

@[simp] theorem entropyOf_real (μ : Measure ℝ) (f : ℝ → ℝ) : entropyOf μ f = entropy μ f := rfl

theorem bounded_comp_of_continuous' {X : Type*} {φ : ℝ → ℝ} {f : X → ℝ} (hφ : Continuous φ)
    (hf : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : ∃ C : ℝ, ∀ x, ‖φ (f x)‖ ≤ C := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-C) C) hφ.continuousOn
  refine ⟨D,fun x => hD _ ?_⟩
  exact abs_le.mp (hC x)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mehlerEntropyD (f : (ι → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ x, mehlerKernelD t f x * Real.log (mehlerKernelD t f x) ∂gaussianProduct ι

theorem integrable_mul_log_of_boundedD {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => f x*Real.log (f x)) (gaussianProduct ι) :=
  (memLp_gaussianD_of_bounded (Real.continuous_mul_log.comp hf)
    (bounded_comp_of_continuous' (f := f) Real.continuous_mul_log hb) 1).integrable le_rfl

theorem integral_mul_generatorD_coord {u h : (ι → ℝ) → ℝ} (hu : IsC1BoundedD u)
    (hh : IsC2BoundedD h) (i : ι) :
    (∫ x, u x*(partialD (partialD h i) i x-x i*partialD h i x) ∂gaussianProduct ι) =
      -(∫ x, partialD u i x*partialD h i x ∂gaussianProduct ι) := by
  have hi₁ : Integrable (fun x => partialD u i x*partialD h i x) (gaussianProduct ι) :=
    (hu.memLp_partial i 2).integrable_mul (hh.1.memLp_partial i 2)
  have hi₂ : Integrable (fun x => u x*partialD (partialD h i) i x) (gaussianProduct ι) :=
    (hu.memLp 2).integrable_mul ((hh.2 i).memLp_partial i 2)
  have hi₃ := integrable_coord_mul_boundedD (hu.mul (hh.2 i)).contDiff.continuous
    (hu.mul (hh.2 i)).bounded i
  have hd := funext (partialD_mul hu (hh.2 i) i)
  have hibp := integral_partialD_gaussian (hu.mul (hh.2 i)) i
  rw [hd,integral_add hi₁ hi₂] at hibp
  have he : (∫ x, u x*(partialD (partialD h i) i x-x i*partialD h i x) ∂gaussianProduct ι) =
      (∫ x, u x*partialD (partialD h i) i x ∂gaussianProduct ι)-
      (∫ x, x i*(u x*partialD h i x) ∂gaussianProduct ι) := by
    rw [← integral_sub hi₂ hi₃]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  rw [he]; linarith

theorem integrable_mul_generatorD_coord {u h : (ι → ℝ) → ℝ} (hu : IsC1BoundedD u)
    (hh : IsC2BoundedD h) (i : ι) :
    Integrable (fun x => u x*(partialD (partialD h i) i x-x i*partialD h i x)) (gaussianProduct ι) := by
  have hi₂ : Integrable (fun x => u x*partialD (partialD h i) i x) (gaussianProduct ι) :=
    (hu.memLp 2).integrable_mul ((hh.2 i).memLp_partial i 2)
  have hi₃ := integrable_coord_mul_boundedD (hu.mul (hh.2 i)).contDiff.continuous
    (hu.mul (hh.2 i)).bounded i
  convert hi₂.sub hi₃ using 1
  ext x
  simp only [Pi.sub_apply]
  ring

theorem integral_mul_generatorD {u h : (ι → ℝ) → ℝ} (hu : IsC1BoundedD u)
    (hh : IsC2BoundedD h) :
    (∫ x, u x*ouGeneratorD h x ∂gaussianProduct ι) =
      -(∫ x, ∑ i, partialD u i x*partialD h i x ∂gaussianProduct ι) := by
  simp only [ouGeneratorD,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_mul_generatorD_coord hu hh i),
    integral_finsetSum _ (f := fun i x => partialD u i x*partialD h i x) (fun i _ => (hu.memLp_partial i 2).integrable_mul (hh.1.memLp_partial i 2))]
  simp only [integral_mul_generatorD_coord hu hh,Finset.sum_neg_distrib]

theorem integral_log_generatorD {g : (ι → ℝ) → ℝ} (hg : IsC2BoundedD g)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ g x) :
    (∫ x, (1+Real.log (g x))*ouGeneratorD g x ∂gaussianProduct ι) = -fisherInfoD g := by
  have hl := hg.1.log hε hpos
  rw [integral_mul_generatorD ((IsC1BoundedD.const 1).add hl) hg]
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ (fun x => ?_)
  simp only [partialD_add (IsC1BoundedD.const 1) hl,partialD_const,zero_add,
    partialD_log hg.1 x (hε.trans_le (hpos x)).ne',gradNormSqD,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Foundations
