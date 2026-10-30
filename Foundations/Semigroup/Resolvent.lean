import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Contractive resolvents, their common dense domain, and their generator. -/
noncomputable section
open Filter Topology
namespace Foundations

/-- The values at nonpositive parameters are immaterial. -/
structure ContractionResolvent (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  G : ℝ → H →L[ℝ] H
  resolvent_eq : ∀ {a b}, 0 < a → 0 < b → G a - G b = (b-a) • (G a * G b)
  norm_le : ∀ {b}, 0 < b → ‖b • G b‖ ≤ 1
  tendsto_id : ∀ x, Tendsto (fun b => b • G b x) atTop (𝓝 x)

namespace ContractionResolvent
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (R : ContractionResolvent H)

theorem commute_G {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Commute (R.G a) (R.G b) := by
  by_cases h : a = b
  · subst b; exact Commute.refl _
  have h₁ := R.resolvent_eq ha hb
  have h₂ := R.resolvent_eq hb ha
  have he : (b-a) • (R.G a * R.G b) = (b-a) • (R.G b * R.G a) := by
    linear_combination (norm := module) -h₁ - h₂
  exact (smul_right_injective (H →L[ℝ] H) (sub_ne_zero.mpr (Ne.symm h)) he : _)

theorem resolvent_apply {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : H) :
    R.G a x - R.G b x = (b-a) • R.G a (R.G b x) :=
  congrArg (fun f : H →L[ℝ] H => f x) (R.resolvent_eq ha hb)

theorem G_eq_zero {b : ℝ} (hb : 0 < b) {x : H} (hx : R.G b x = 0) : x = 0 := by
  have hz : ∀ a > 0, R.G a x = 0 := by
    intro a ha
    have he := R.resolvent_apply ha hb x
    simpa [hx] using he
  have ht : Tendsto (fun a : ℝ => a • R.G a x) atTop (𝓝 (0 : H)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    simp [hz a ha]
  exact tendsto_nhds_unique (R.tendsto_id x) ht

theorem injective_G {b : ℝ} (hb : 0 < b) : Function.Injective (R.G b) := by
  intro x y h
  apply sub_eq_zero.mp
  apply R.G_eq_zero hb
  simp [map_sub, h]

theorem range_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    LinearMap.range (R.G a).toLinearMap = LinearMap.range (R.G b).toLinearMap := by
  suffices hh : ∀ a b : ℝ, 0 < a → 0 < b →
      LinearMap.range (R.G a).toLinearMap ≤ LinearMap.range (R.G b).toLinearMap from
    le_antisymm (hh a b ha hb) (hh b a hb ha)
  intro a b ha hb x hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨y + (b-a) • R.G a y, ?_⟩
  have he := R.resolvent_apply ha hb y
  have hc := congrArg (fun f : H →L[ℝ] H => f y) (R.commute_G ha hb).eq
  change R.G a (R.G b y) = R.G b (R.G a y) at hc
  change R.G b (y + (b-a) • R.G a y) = R.G a y
  rw [map_add, map_smul, ← hc]
  linear_combination (norm := module) -he

def dom : Submodule ℝ H := LinearMap.range (R.G 1).toLinearMap

theorem mem_dom_G {b : ℝ} (hb : 0 < b) (x : H) : R.G b x ∈ R.dom := by
  rw [dom, ← R.range_eq hb (by norm_num : (0:ℝ)<1)]
  exact ⟨x, rfl⟩

theorem dense_dom : Dense (R.dom : Set H) := by
  intro x
  apply mem_closure_of_tendsto (R.tendsto_id x)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  exact R.dom.smul_mem b (R.mem_dom_G hb x)

def domainEquiv : H ≃ₗ[ℝ] R.dom := LinearEquiv.ofInjective (R.G 1).toLinearMap
  (R.injective_G (by norm_num))

def generator : R.dom →ₗ[ℝ] H := R.dom.subtype - R.domainEquiv.symm.toLinearMap

theorem generator_G_one (y : H) :
    R.generator ⟨R.G 1 y, R.mem_dom_G (by norm_num) y⟩ = R.G 1 y - y := by
  change R.G 1 y - R.domainEquiv.symm (R.domainEquiv y) = _
  rw [LinearEquiv.symm_apply_apply]

theorem generator_G {b : ℝ} (hb : 0 < b) (y : H) :
    R.generator ⟨R.G b y, R.mem_dom_G hb y⟩ = b • R.G b y - y := by
  have he := R.resolvent_apply hb (by norm_num : (0:ℝ)<1) y
  have hc := congrArg (fun f : H →L[ℝ] H => f y) (R.commute_G hb (by norm_num : (0:ℝ)<1)).eq
  change R.G b (R.G 1 y) = R.G 1 (R.G b y) at hc
  have hr : R.G 1 (y + (1-b) • R.G b y) = R.G b y := by
    rw [map_add, map_smul, ← hc]; linear_combination (norm := module) -he
  have hs : (⟨R.G b y, R.mem_dom_G hb y⟩ : R.dom) =
      ⟨R.G 1 (y + (1-b) • R.G b y), R.mem_dom_G (by norm_num) _⟩ :=
    Subtype.ext hr.symm
  rw [hs, R.generator_G_one, hr]
  module

theorem G_generator {b : ℝ} (hb : 0 < b) (x : R.dom) :
    R.G b (b • (x:H) - R.generator x) = x := by
  obtain ⟨y, hy⟩ : ∃ y, R.G b y = (x:H) := by
    have hx : (x:H) ∈ LinearMap.range (R.G 1).toLinearMap := x.property
    rw [← R.range_eq hb (by norm_num : (0:ℝ)<1)] at hx
    exact hx
  have hx : x = ⟨R.G b y, R.mem_dom_G hb y⟩ := Subtype.ext hy.symm
  rw [hx, R.generator_G hb]
  simp

end ContractionResolvent
end Foundations
