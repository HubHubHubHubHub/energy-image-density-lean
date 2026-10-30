import ErrorCalculus.Dirichlet.ImageBasic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus

/-- Bounded measurable real tests used in the Radon--Nikodym characterization. -/
structure ImageTest (α : Type*) [MeasurableSpace α] where
  toFun : α → ℝ
  measurable : Measurable toFun
  bound : ∃ C : ℝ, ∀ x, ‖toFun x‖ ≤ C

namespace ImageTest
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
instance : CoeFun (ImageTest α) (fun _ => α → ℝ) := ⟨toFun⟩

def one : ImageTest α := ⟨fun _ => 1, measurable_const, 1, by simp⟩

def indicator (s : Set α) (hs : MeasurableSet s) : ImageTest α :=
  ⟨s.indicator (fun _ => 1), measurable_const.indicator hs, 1, by
    intro x; by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]⟩

def comp (H : ImageTest β) (f : α → β) (hf : Measurable f) : ImageTest α :=
  ⟨H ∘ f, H.measurable.comp hf, H.bound.imp fun _ hC x => hC (f x)⟩

def mul (H K : ImageTest α) : ImageTest α where
  toFun x := H x * K x
  measurable := H.measurable.mul K.measurable
  bound := by
    obtain ⟨C, hC⟩ := H.bound
    obtain ⟨D, hD⟩ := K.bound
    refine ⟨max C 0 * max D 0, fun x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul ((hC x).trans (le_max_left _ _)) ((hD x).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)

variable (H : ImageTest α) {ν : Measure α}

theorem integrable_mul (f : Lp ℝ 1 ν) : Integrable (fun x => H x * f x) ν := by
  obtain ⟨C, hC⟩ := H.bound
  exact (L1.integrable_coeFn f).bdd_mul H.measurable.aestronglyMeasurable (ae_of_all _ hC)

/-- Integration against a bounded test is linear on L¹ classes. -/
def integral : Lp ℝ 1 ν →ₗ[ℝ] ℝ where
  toFun f := ∫ x, H x * f x ∂ν
  map_add' f g := by
    calc
      _ = ∫ x, H x * f x + H x * g x ∂ν := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with x hx
        simp only [hx, Pi.add_apply, mul_add]
      _ = _ := integral_add (H.integrable_mul f) (H.integrable_mul g)
  map_smul' c f := by
    calc
      _ = ∫ x, c * (H x * f x) ∂ν := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with x hx
        rw [hx]; simp only [Pi.smul_apply, smul_eq_mul]; ring
      _ = _ := integral_const_mul _ _

@[simp] theorem integral_one (f : Lp ℝ 1 ν) :
    (one : ImageTest α).integral f = ∫ x, f x ∂ν := by simp [integral, one]

@[simp] theorem integral_indicator (s : Set α) (hs : MeasurableSet s) (f : Lp ℝ 1 ν) :
    (indicator s hs).integral f = ∫ x in s, f x ∂ν := by
  change (∫ x, s.indicator (fun _ => (1 : ℝ)) x * f x ∂ν) = _
  simp_rw [← Set.indicator_mul_left, one_mul]
  exact MeasureTheory.integral_indicator hs

/-- measurable-set integrals determine L¹ classes. -/
theorem eq_of_setIntegral_eq (f g : Lp ℝ 1 ν)
    (h : ∀ s, MeasurableSet s → ∫ x in s, f x ∂ν = ∫ x in s, g x ∂ν) : f = g := by
  apply Lp.ext
  exact Integrable.ae_eq_of_forall_setIntegral_eq f g (L1.integrable_coeFn f)
    (L1.integrable_coeFn g) (fun s hs _ => h s hs)

/-- bounded measurable tests determine L¹ classes. -/
theorem eq_of_integral_eq (f g : Lp ℝ 1 ν)
    (h : ∀ H : ImageTest α, H.integral f = H.integral g) : f = g := by
  apply eq_of_setIntegral_eq f g
  intro s hs
  simpa only [integral_indicator] using h (indicator s hs)

end ImageTest
end ErrorCalculus
