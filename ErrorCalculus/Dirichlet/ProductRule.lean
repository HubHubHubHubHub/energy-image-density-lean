import ErrorCalculus.Dirichlet.Truncation
import ErrorCalculus.Dirichlet.Calculus
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Essential boundedness of a real representative; no bound on the exceptional null set. -/
def AEBounded (f : Ω → ℝ) : Prop := ∃ C : ℝ, ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C

theorem AEBounded.memLp_top {f : Ω → ℝ} (hf : AEBounded (μ := μ) f)
    (hm : AEStronglyMeasurable f μ) : MemLp f ∞ μ := by
  obtain ⟨C,hC⟩ := hf
  exact MemLp.of_bound hm C hC

namespace ErrorStructure
variable (S : ErrorStructure Ω μ)

/-- The calculus axiom applied to the truncated product. -/
theorem product_calculus (F G : S.dom)
    (hF : AEBounded (μ := μ) (F : Lp ℝ 2 μ))
    (hG : AEBounded (μ := μ) (G : Lp ℝ 2 μ))
    (w : Lp ℝ 2 μ) (hw : ⇑w =ᵐ[μ] fun ω => (F : Lp ℝ 2 μ) ω * (G : Lp ℝ 2 μ) ω) :
    ∃ hd : w ∈ S.dom, ∀ H : S.dom, S.Γ ⟨w,hd⟩ H =ᵐ[μ]
      fun ω => (F : Lp ℝ 2 μ) ω * S.Γ G H ω + (G : Lp ℝ 2 μ) ω * S.Γ F H ω := by
  obtain ⟨C,hC⟩ := hF
  obtain ⟨D,hD⟩ := hG
  let M := max C D
  have hb : ∀ᵐ ω ∂μ, |(F : Lp ℝ 2 μ) ω| ≤ M ∧ |(G : Lp ℝ 2 μ) ω| ≤ M := by
    filter_upwards [hC,hD] with ω hC hD
    exact ⟨(by simpa only [Real.norm_eq_abs] using hC.trans (le_max_left C D)),
      (by simpa only [Real.norm_eq_abs] using hD.trans (le_max_right C D))⟩
  have he : ⇑w =ᵐ[μ] fun ω => truncatedProduct M (fun i => (![F,G] i : Lp ℝ 2 μ) ω) := by
    filter_upwards [hw,hb] with ω hw hb
    rw [hw, truncatedProduct_eq_mul hb.1 hb.2]
    rfl
  obtain ⟨hd,hchain⟩ := S.calc 2 (by decide) ![F,G] (truncatedProduct M) _
    (truncatedProduct_contDiff M) (truncatedProduct_lipschitz M) w he
  refine ⟨hd,fun H => ?_⟩
  filter_upwards [hchain H,hb] with ω hω hb
  rw [hω]
  simp_rw [fderiv_truncatedProduct (x := fun i => (![F,G] i : Lp ℝ 2 μ) ω) hb.1 hb.2]
  simp [Fin.sum_univ_two, Pi.single_apply, mul_comm, add_comm]

/-- The product belongs to the domain, for any L² class representing it. -/
theorem mul_mem_dom_of_bounded (F G : S.dom)
    (hF : AEBounded (μ := μ) (F : Lp ℝ 2 μ))
    (hG : AEBounded (μ := μ) (G : Lp ℝ 2 μ))
    (w : Lp ℝ 2 μ) (hw : ⇑w =ᵐ[μ] fun ω => (F : Lp ℝ 2 μ) ω * (G : Lp ℝ 2 μ) ω) :
    w ∈ S.dom := (S.product_calculus F G hF hG w hw).choose

/-- The canonical product domain element. -/
def boundedMul (F G : S.dom)
    (hF : AEBounded (μ := μ) (F : Lp ℝ 2 μ))
    (hG : AEBounded (μ := μ) (G : Lp ℝ 2 μ)) : S.dom := by
  let hp : MemLp (fun ω => (F : Lp ℝ 2 μ) ω * (G : Lp ℝ 2 μ) ω) 2 μ :=
    (Lp.memLp (G : Lp ℝ 2 μ)).mul' (hF.memLp_top (Lp.aestronglyMeasurable _))
  exact ⟨hp.toLp _, S.mul_mem_dom_of_bounded F G hF hG _ hp.coeFn_toLp⟩

theorem coeFn_boundedMul (F G : S.dom)
    (hF : AEBounded (μ := μ) (F : Lp ℝ 2 μ))
    (hG : AEBounded (μ := μ) (G : Lp ℝ 2 μ)) :
    ⇑(S.boundedMul F G hF hG : Lp ℝ 2 μ) =ᵐ[μ]
      fun ω => (F : Lp ℝ 2 μ) ω * (G : Lp ℝ 2 μ) ω :=
  ((Lp.memLp (G : Lp ℝ 2 μ)).mul' (hF.memLp_top (Lp.aestronglyMeasurable _)) :
    MemLp (fun ω => (F : Lp ℝ 2 μ) ω * (G : Lp ℝ 2 μ) ω) 2 μ).coeFn_toLp

/-- The mixed product rule, independent of the chosen representative. -/
theorem gamma_mul (F G w H : S.dom)
    (hF : AEBounded (μ := μ) (F : Lp ℝ 2 μ))
    (hG : AEBounded (μ := μ) (G : Lp ℝ 2 μ))
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun ω => (F : Lp ℝ 2 μ) ω * (G : Lp ℝ 2 μ) ω) :
    S.Γ w H =ᵐ[μ] fun ω =>
      (F : Lp ℝ 2 μ) ω * S.Γ G H ω + (G : Lp ℝ 2 μ) ω * S.Γ F H ω :=
  (S.product_calculus F G hF hG w hw).choose_spec H

/-- The diagonal product rule. -/
theorem gamma_mul_self (F G w : S.dom)
    (hF : AEBounded (μ := μ) (F : Lp ℝ 2 μ))
    (hG : AEBounded (μ := μ) (G : Lp ℝ 2 μ))
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun ω => (F : Lp ℝ 2 μ) ω * (G : Lp ℝ 2 μ) ω) :
    S.Γ w w =ᵐ[μ] fun ω => (F : Lp ℝ 2 μ) ω ^ 2 * S.Γ G G ω +
      2 * (F : Lp ℝ 2 μ) ω * (G : Lp ℝ 2 μ) ω * S.Γ F G ω +
      (G : Lp ℝ 2 μ) ω ^ 2 * S.Γ F F ω := by
  filter_upwards [S.gamma_mul F G w w hF hG hw,
    S.gamma_mul F G w F hF hG hw, S.gamma_mul F G w G hF hG hw] with ω hww hwF hwG
  rw [S.Γ_symm G w, S.Γ_symm F w, hwF, hwG] at hww
  rw [S.Γ_symm G F] at hww
  rw [hww]
  ring

theorem energy_mul (F G w H : S.dom)
    (hF : AEBounded (μ := μ) (F : Lp ℝ 2 μ))
    (hG : AEBounded (μ := μ) (G : Lp ℝ 2 μ))
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun ω => (F : Lp ℝ 2 μ) ω * (G : Lp ℝ 2 μ) ω) :
    S.energy.E w H = (1/2 : ℝ) * ∫ ω,
      ((F : Lp ℝ 2 μ) ω * S.Γ G H ω + (G : Lp ℝ 2 μ) ω * S.Γ F H ω) ∂μ := by
  rw [ErrorData.energy_apply, integral_congr_ae (S.gamma_mul F G w H hF hG hw)]

end ErrorStructure
end ErrorCalculus
