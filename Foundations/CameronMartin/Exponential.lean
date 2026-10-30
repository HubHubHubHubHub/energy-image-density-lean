import Foundations.CameronMartin.GaussianLaw
import Foundations.Sections.Basic

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Foundations

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {v : NNReal}

theorem integral_exp_gaussian_linear (hX : P.map X = gaussianReal 0 v) (c d : ℝ) :
    (∫ x, Real.exp (c*X x-d) ∂P) = Real.exp ((v:ℝ)*c^2/2-d) := by
  simp_rw [Real.exp_sub]
  rw [integral_div]
  change mgf X P c / Real.exp d = _
  rw [mgf_gaussianReal hX]
  simp [Real.exp_sub]

theorem integrable_exp_gaussian_linear (hX : P.map X = gaussianReal 0 v) (c d : ℝ) :
    Integrable (fun x => Real.exp (c*X x-d)) P := by
  have hm : AEMeasurable X P := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  have hi : Integrable (fun x => Real.exp (c*x)) (P.map X) := by
    rw [hX]; exact integrable_exp_mul_gaussianReal c
  simpa only [Real.exp_sub,Function.comp_def] using (hi.comp_aemeasurable hm).div_const (Real.exp d)

theorem memLp_exp_gaussian_linear (hX : P.map X = gaussianReal 0 v) (c d : ℝ) :
    MemLp (fun x => Real.exp (c*X x-d)) 2 P := by
  have hm : AEMeasurable X P := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  convert integrable_exp_gaussian_linear hX (2*c) (2*d) using 1
  funext x
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem integral_sq_exp_gaussian_linear (hX : P.map X = gaussianReal 0 v) (c d : ℝ) :
    (∫ x, (Real.exp (c*X x-d))^2 ∂P) = Real.exp (2*(v:ℝ)*c^2-2*d) := by
  have he : (fun x => (Real.exp (c*X x-d))^2) =
      (fun x => Real.exp ((2*c)*X x-2*d)) := by
    funext x
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he,integral_exp_gaussian_linear hX]
  congr 1
  ring

end Foundations
