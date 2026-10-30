import Foundations.LogSobolev.BoundedCalculus
import Foundations.LogSobolev.Fisher
import Foundations.LogSobolev.GaussianIBP

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations

/-- The real-valued entropy; results using it also establish integrability. -/
def entropy (μ : Measure ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x, f x*Real.log (f x) ∂μ) - (∫ x, f x ∂μ)*Real.log (∫ x, f x ∂μ)

def mehlerEntropy (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, mehlerKernel t f x * Real.log (mehlerKernel t f x) ∂standardGaussian

theorem bounded_comp_of_continuous {φ f : ℝ → ℝ} (hφ : Continuous φ)
    (hf : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : ∃ C : ℝ, ∀ x, ‖φ (f x)‖ ≤ C := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-C) C) hφ.continuousOn
  refine ⟨D,fun x => hD _ ?_⟩
  exact abs_le.mp (hC x)

theorem integrable_mul_log_of_bounded {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => f x*Real.log (f x)) standardGaussian :=
  (memLp_gaussian_of_bounded (Real.continuous_mul_log.comp hf)
    (bounded_comp_of_continuous (f := f) Real.continuous_mul_log hb) 1).integrable le_rfl

theorem integral_log_generator {g : ℝ → ℝ} (hg : IsC2Bounded g)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ g x) :
    (∫ x, (1+Real.log (g x))*(deriv (deriv g) x-x*deriv g x) ∂standardGaussian) =
      -fisherInfo g := by
  let u := fun x => 1+Real.log (g x)
  have hu : IsC1Bounded u := (IsC1Bounded.const 1).add (hg.1.log hε hpos)
  have hd : deriv (fun x => u x*deriv g x) =
      fun x => fisherDensity g x+u x*deriv (deriv g) x := by
    funext x
    have hn : g x ≠ 0 := (hε.trans_le (hpos x)).ne'
    have hh := (((hg.1.hasDerivAt x).log hn).const_add 1).mul (hg.2.hasDerivAt x)
    apply hh.deriv.trans
    dsimp [fisherDensity,u]
    ring
  have higg : Integrable (fun x => u x*deriv (deriv g) x) standardGaussian := by
    exact (memLp_gaussian_of_bounded (hu.contDiff.continuous.mul hg.2.contDiff.continuous_deriv_one)
      (by
        obtain ⟨C,hC⟩ := hu.bounded
        obtain ⟨D,hD⟩ := hg.2.deriv_bounded
        refine ⟨C*D,fun x => ?_⟩
        simp only [Pi.mul_apply,norm_mul]
        exact mul_le_mul (hC x) (hD x) (norm_nonneg _) ((norm_nonneg (u 0)).trans (hC 0))) 1).integrable le_rfl
  have hibp := integral_deriv_gaussian (hu.mul hg.2)
  have hadd := integral_add ((memLp_fisherDensity hg.1 hε hpos 1).integrable le_rfl) higg
  rw [hd,hadd] at hibp
  have hix := integrable_id_mul_bounded (hu.mul hg.2).contDiff.continuous (hu.mul hg.2).bounded
  have he : (∫ x, u x*(deriv (deriv g) x-x*deriv g x) ∂standardGaussian) =
      (∫ x, u x*deriv (deriv g) x ∂standardGaussian)-
      (∫ x, x*(u x*deriv g x) ∂standardGaussian) := by
    rw [← integral_sub higg hix]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  rw [he]
  dsimp [fisherInfo]
  linarith

end Foundations
