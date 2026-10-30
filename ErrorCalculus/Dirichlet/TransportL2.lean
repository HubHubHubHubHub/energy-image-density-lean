import ErrorCalculus.Dirichlet.ErrorStructure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
open scoped ENNReal
namespace ErrorCalculus

/-- two measure-preserving maps inverse almost everywhere. -/
structure MeasureIsoModZero {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') where
  forward : Ω → Ω'
  backward : Ω' → Ω
  forward_preserving : MeasurePreserving forward μ ν
  backward_preserving : MeasurePreserving backward ν μ
  backward_forward : ∀ᵐ x ∂μ, backward (forward x) = x
  forward_backward : ∀ᵐ y ∂ν, forward (backward y) = y

namespace MeasureIsoModZero
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {μ : Measure Ω} {ν : Measure Ω'} (e : MeasureIsoModZero μ ν)

/-- The inverse mod-zero isomorphism. -/
def symm : MeasureIsoModZero ν μ where
  forward := e.backward
  backward := e.forward
  forward_preserving := e.backward_preserving
  backward_preserving := e.forward_preserving
  backward_forward := e.forward_backward
  forward_backward := e.backward_forward

theorem pullback_inverse (p : ℝ≥0∞) (f : Lp ℝ p μ) :
    Lp.compMeasurePreserving e.forward e.forward_preserving
      (Lp.compMeasurePreserving e.backward e.backward_preserving f) = f := by
  rw [← Lp.compMeasurePreserving_comp_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
    (e.backward_preserving.comp e.forward_preserving), e.backward_forward] with x hx he
  exact hx.trans (congrArg f he)

/-- Pullback is a linear isometric equivalence for every normed Lp. -/
def lp (p : ℝ≥0∞) [Fact (1 ≤ p)] : Lp ℝ p ν ≃ₗᵢ[ℝ] Lp ℝ p μ :=
  LinearIsometryEquiv.ofLinearIsometry
    (Lp.compMeasurePreservingₗᵢ ℝ e.forward e.forward_preserving)
    (Lp.compMeasurePreservingₗ ℝ e.backward e.backward_preserving)
    (by ext f : 1; exact e.pullback_inverse p f)
    (by ext f : 1; exact e.symm.pullback_inverse p f)

theorem coe_lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp ℝ p ν) :
    ⇑(e.lp p f) =ᵐ[μ] f ∘ e.forward :=
  Lp.coeFn_compMeasurePreserving f e.forward_preserving

theorem coe_lp_symm (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp ℝ p μ) :
    ⇑((e.lp p).symm f) =ᵐ[ν] f ∘ e.backward :=
  Lp.coeFn_compMeasurePreserving f e.backward_preserving

theorem coe_lp_at_backward (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp ℝ p ν) :
    ∀ᵐ y ∂ν, e.lp p f (e.backward y) = f y := by
  filter_upwards [e.backward_preserving.quasiMeasurePreserving.ae (e.coe_lp p f),
    e.forward_backward] with y hy he
  exact hy.trans (congrArg f he)

@[simp] theorem lp_const [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : ℝ) :
    e.lp p (Lp.const p ν c) = Lp.const p μ c := by
  apply Lp.ext
  filter_upwards [e.coe_lp p (Lp.const p ν c),
    e.forward_preserving.quasiMeasurePreserving.ae (Lp.coeFn_const p ν c),
    Lp.coeFn_const p μ c] with x hx hy hz
  exact hx.trans (hy.trans hz.symm)

@[simp] theorem lp_symm_const [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : ℝ) :
    (e.lp p).symm (Lp.const p μ c) = Lp.const p ν c :=
  (e.lp p).injective (by simp)

theorem integral_lp_symm (f : Lp ℝ 1 μ) :
    (∫ y, (e.lp 1).symm f y ∂ν) = ∫ x, f x ∂μ := by
  rw [integral_congr_ae (e.coe_lp_symm 1 f)]
  have hm : AEStronglyMeasurable (⇑f) (ν.map e.backward) := by
    rw [e.backward_preserving.map_eq]
    exact Lp.aestronglyMeasurable f
  have h := integral_map e.backward_preserving.aemeasurable hm
  simpa only [e.backward_preserving.map_eq, Function.comp_def] using h.symm

/-- Pullback preserves the integral of every Lp representative. -/
theorem integral_lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp ℝ p ν) :
    (∫ x, e.lp p f x ∂μ) = ∫ y, f y ∂ν := by
  rw [integral_congr_ae (e.coe_lp p f)]
  have hm : AEStronglyMeasurable (⇑f) (μ.map e.forward) := by
    rw [e.forward_preserving.map_eq]
    exact Lp.aestronglyMeasurable f
  have h := integral_map e.forward_preserving.aemeasurable hm
  simpa only [e.forward_preserving.map_eq, Function.comp_def] using h.symm

end MeasureIsoModZero

/-- The L² equivalence, oriented from target to source. -/
abbrev transportL2 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} (e : MeasureIsoModZero μ ν) := e.lp 2

end ErrorCalculus
