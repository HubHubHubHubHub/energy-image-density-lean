import Foundations.LogSobolev.MehlerDeriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Topology
namespace Foundations

theorem IsC1Bounded.const (c : ℝ) : IsC1Bounded (fun _ : ℝ => c) := by
  exact ⟨contDiff_const, ⟨‖c‖,fun _ => le_rfl⟩, ⟨0, by simp⟩⟩

theorem IsC1Bounded.add {f g : ℝ → ℝ} (hf : IsC1Bounded f) (hg : IsC1Bounded g) :
    IsC1Bounded (fun x => f x+g x) := by
  obtain ⟨C,hC⟩ := hf.bounded
  obtain ⟨D,hD⟩ := hg.bounded
  obtain ⟨C',hC'⟩ := hf.deriv_bounded
  obtain ⟨D',hD'⟩ := hg.deriv_bounded
  refine ⟨hf.contDiff.add hg.contDiff,⟨C+D,fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩,
    ⟨C'+D',fun x => ?_⟩⟩
  have he : deriv (fun x => f x+g x) x = deriv f x+deriv g x := ((hf.hasDerivAt x).add (hg.hasDerivAt x)).deriv
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (hC' x) (hD' x))

theorem IsC1Bounded.mul {f g : ℝ → ℝ} (hf : IsC1Bounded f) (hg : IsC1Bounded g) :
    IsC1Bounded (fun x => f x*g x) := by
  obtain ⟨C,hC⟩ := hf.bounded
  obtain ⟨D,hD⟩ := hg.bounded
  obtain ⟨C',hC'⟩ := hf.deriv_bounded
  obtain ⟨D',hD'⟩ := hg.deriv_bounded
  have hC0 := (norm_nonneg (f 0)).trans (hC 0)
  have hC'0 := (norm_nonneg (deriv f 0)).trans (hC' 0)
  refine ⟨hf.contDiff.mul hg.contDiff,⟨C*D,fun x => ?_⟩,⟨C'*D+C*D',fun x => ?_⟩⟩
  · rw [norm_mul]
    exact mul_le_mul (hC x) (hD x) (norm_nonneg _) hC0
  · have he : deriv (fun x => f x*g x) x = deriv f x*g x+f x*deriv g x := ((hf.hasDerivAt x).mul (hg.hasDerivAt x)).deriv
    rw [he]
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    exact add_le_add (mul_le_mul (hC' x) (hD x) (norm_nonneg _) hC'0)
      (mul_le_mul (hC x) (hD' x) (norm_nonneg _) hC0)

theorem IsC1Bounded.const_mul {f : ℝ → ℝ} (hf : IsC1Bounded f) (c : ℝ) :
    IsC1Bounded (fun x => c*f x) := (IsC1Bounded.const c).mul hf

theorem IsC2Bounded.const (c : ℝ) : IsC2Bounded (fun _ : ℝ => c) := by
  refine ⟨IsC1Bounded.const c,?_⟩
  simpa using IsC1Bounded.const 0

theorem IsC2Bounded.add {f g : ℝ → ℝ} (hf : IsC2Bounded f) (hg : IsC2Bounded g) :
    IsC2Bounded (fun x => f x+g x) := by
  refine ⟨hf.1.add hg.1,?_⟩
  have he : deriv (fun x => f x+g x) = fun x => deriv f x+deriv g x := by
    funext x; exact ((hf.1.hasDerivAt x).add (hg.1.hasDerivAt x)).deriv
  rw [he]; exact hf.2.add hg.2

theorem IsC2Bounded.mul {f g : ℝ → ℝ} (hf : IsC2Bounded f) (hg : IsC2Bounded g) :
    IsC2Bounded (fun x => f x*g x) := by
  refine ⟨hf.1.mul hg.1,?_⟩
  have he : deriv (fun x => f x*g x) = fun x => deriv f x*g x+f x*deriv g x := by
    funext x; exact ((hf.1.hasDerivAt x).mul (hg.1.hasDerivAt x)).deriv
  rw [he]; exact (hf.2.mul hg.1).add (hf.1.mul hg.2)

theorem isC2Bounded_mehlerKernel {f : ℝ → ℝ} (hf : IsC2Bounded f) (t : ℝ) :
    IsC2Bounded (mehlerKernel t f) := by
  refine ⟨isC1Bounded_mehlerKernel hf.1 t,?_⟩
  have he : deriv (mehlerKernel t f) = fun x => mehlerCoeffA t * mehlerKernel t (deriv f) x :=
    funext (deriv_mehlerKernel hf.1 t)
  rw [he]; exact (isC1Bounded_mehlerKernel hf.2 t).const_mul _

theorem norm_log_le_of_bounds {ε C z : ℝ} (hε : 0 < ε) (hz : ε ≤ z) (hC : z ≤ C) :
    ‖Real.log z‖ ≤ ‖Real.log ε‖+‖Real.log C‖ := by
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · have := Real.log_le_log hε hz
    have := neg_abs_le (Real.log ε)
    have := abs_nonneg (Real.log C)
    simp only [Real.norm_eq_abs]; linarith
  · have := Real.log_le_log (hε.trans_le hz) hC
    have := le_abs_self (Real.log C)
    have := abs_nonneg (Real.log ε)
    simp only [Real.norm_eq_abs]; linarith

theorem IsC1Bounded.log {f : ℝ → ℝ} (hf : IsC1Bounded f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) : IsC1Bounded (fun x => Real.log (f x)) := by
  obtain ⟨C,hC⟩ := hf.bounded
  obtain ⟨D,hD⟩ := hf.deriv_bounded
  have hne : ∀ x, f x ≠ 0 := fun x => (hε.trans_le (hpos x)).ne'
  refine ⟨hf.contDiff.log hne,⟨‖Real.log ε‖+‖Real.log C‖,fun x =>
    norm_log_le_of_bounds hε (hpos x) ((le_abs_self _).trans (hC x))⟩,⟨D/ε,fun x => ?_⟩⟩
  rw [((hf.hasDerivAt x).log (hne x)).deriv,norm_div,Real.norm_of_nonneg (hε.le.trans (hpos x))]
  exact div_le_div₀ ((norm_nonneg _).trans (hD x)) (hD x) hε (hpos x)

end Foundations
