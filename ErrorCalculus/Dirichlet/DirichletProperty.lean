import ErrorCalculus.Dirichlet.ContractionLipschitz
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Algebra.Order.Module.Basic

noncomputable section
open MeasureTheory
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ)

/-- Every scalar normal contraction preserves the domain and decreases energy. -/
theorem normal_contraction {F : ℝ → ℝ} (hF : LipschitzWith 1 F)
    (u : S.dom) (w : Lp ℝ 2 μ)
    (hw : ⇑w =ᵐ[μ] fun ω => F ((u : Lp ℝ 2 μ) ω)) :
    ∃ hd : w ∈ S.dom, S.energy.E ⟨w, hd⟩ ⟨w, hd⟩ ≤ S.energy.E u u := by
  simpa using S.lipschitz_comp_mem_dom_energy_le hF u w hw

/-- absolute value belongs to the domain, without EID. -/
theorem abs_mem_dom' (u : S.dom) : |(u : Lp ℝ 2 μ)| ∈ S.dom :=
  S.lipschitz_comp_mem_dom (show LipschitzWith 1 (abs : ℝ → ℝ) from
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y)
    u _ (Lp.coeFn_abs _)

/-- absolute value decreases energy. -/
theorem energy_abs_le (u : S.dom) :
    S.energy.E ⟨|(u : Lp ℝ 2 μ)|, S.abs_mem_dom' u⟩
      ⟨|(u : Lp ℝ 2 μ)|, S.abs_mem_dom' u⟩ ≤ S.energy.E u u := by
  exact (S.normal_contraction (LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y) u _ (Lp.coeFn_abs _)).choose_spec

/-- positive parts belong to the domain. -/
theorem posPart_mem_dom' (u : S.dom) : Lp.posPart (u : Lp ℝ 2 μ) ∈ S.dom :=
  S.lipschitz_comp_mem_dom (LipschitzWith.id.max_const 0) u _ (Lp.coeFn_posPart _)

/-- positive parts decrease energy. -/
theorem energy_posPart_le (u : S.dom) :
    S.energy.E ⟨Lp.posPart (u : Lp ℝ 2 μ), S.posPart_mem_dom' u⟩
      ⟨Lp.posPart (u : Lp ℝ 2 μ), S.posPart_mem_dom' u⟩ ≤ S.energy.E u u :=
  (S.normal_contraction (LipschitzWith.id.max_const 0) u _ (Lp.coeFn_posPart _)).choose_spec

/-- negative parts belong to the domain. -/
theorem negPart_mem_dom (u : S.dom) : Lp.negPart (u : Lp ℝ 2 μ) ∈ S.dom :=
  S.lipschitz_comp_mem_dom ((LipschitzWith.id.neg).max_const 0) u _ (Lp.coeFn_negPart_eq_max _)

/-- negative parts decrease energy. -/
theorem energy_negPart_le (u : S.dom) :
    S.energy.E ⟨Lp.negPart (u : Lp ℝ 2 μ), S.negPart_mem_dom u⟩
      ⟨Lp.negPart (u : Lp ℝ 2 μ), S.negPart_mem_dom u⟩ ≤ S.energy.E u u :=
  (S.normal_contraction ((LipschitzWith.id.neg).max_const 0) u _ (Lp.coeFn_negPart_eq_max _)).choose_spec

/-- truncation above at any real constant. -/
theorem min_const_mem_dom (u : S.dom) (c : ℝ) :
    (u : Lp ℝ 2 μ) ⊓ Lp.const 2 μ c ∈ S.dom := by
  apply S.lipschitz_comp_mem_dom (LipschitzWith.id.min_const c) u
  filter_upwards [Lp.coeFn_inf (u : Lp ℝ 2 μ) (Lp.const 2 μ c),
    Lp.coeFn_const (p := 2) (μ := μ) (c := c)] with ω hi hc
  simp [hi]

/-- truncation above decreases energy. -/
theorem energy_min_const_le (u : S.dom) (c : ℝ) :
    S.energy.E ⟨(u : Lp ℝ 2 μ) ⊓ Lp.const 2 μ c, S.min_const_mem_dom u c⟩
      ⟨(u : Lp ℝ 2 μ) ⊓ Lp.const 2 μ c, S.min_const_mem_dom u c⟩ ≤ S.energy.E u u := by
  apply (S.normal_contraction (LipschitzWith.id.min_const c) u _ ?_).choose_spec
  filter_upwards [Lp.coeFn_inf (u : Lp ℝ 2 μ) (Lp.const 2 μ c),
    Lp.coeFn_const (p := 2) (μ := μ) (c := c)] with ω hi hc
  simp [hi]

/-- The unit truncation is a normal contraction of every domain element. -/
theorem unitContraction_mem_dom (u : S.dom) :
    (0 ⊔ (u : Lp ℝ 2 μ)) ⊓ Lp.const 2 μ 1 ∈ S.dom := by
  apply S.lipschitz_comp_mem_dom ((LipschitzWith.id.const_max 0).min_const 1) u
  filter_upwards [Lp.coeFn_inf (0 ⊔ (u : Lp ℝ 2 μ)) (Lp.const 2 μ 1),
    Lp.coeFn_sup (0 : Lp ℝ 2 μ) u, Lp.coeFn_zero ℝ 2 μ,
    Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with ω hi hs hz hc
  simp [hi, hs]

/-- The Markov bound for unit truncation. -/
theorem energy_unitContraction_le (u : S.dom) :
    S.energy.E ⟨(0 ⊔ (u : Lp ℝ 2 μ)) ⊓ Lp.const 2 μ 1, S.unitContraction_mem_dom u⟩
      ⟨(0 ⊔ (u : Lp ℝ 2 μ)) ⊓ Lp.const 2 μ 1, S.unitContraction_mem_dom u⟩ ≤ S.energy.E u u := by
  apply (S.normal_contraction ((LipschitzWith.id.const_max 0).min_const 1) u _ ?_).choose_spec
  filter_upwards [Lp.coeFn_inf (0 ⊔ (u : Lp ℝ 2 μ)) (Lp.const 2 μ 1),
    Lp.coeFn_sup (0 : Lp ℝ 2 μ) u, Lp.coeFn_zero ℝ 2 μ,
    Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with ω hi hs hz hc
  simp [hi, hs]

/-- stability under infimum, by the absolute-value identity. -/
theorem inf_mem_dom (u v : S.dom) : (u : Lp ℝ 2 μ) ⊓ v ∈ S.dom := by
  rw [inf_eq_half_smul_add_sub_abs_sub' ℝ]
  exact S.dom.smul_mem _ (S.dom.sub_mem (S.dom.add_mem u.property v.property) (S.abs_mem_dom' (v-u)))

/-- stability under supremum, by the absolute-value identity. -/
theorem sup_mem_dom (u v : S.dom) : (u : Lp ℝ 2 μ) ⊔ v ∈ S.dom := by
  rw [sup_eq_half_smul_add_add_abs_sub' ℝ]
  exact S.dom.smul_mem _ (S.dom.add_mem (S.dom.add_mem u.property v.property) (S.abs_mem_dom' (v-u)))

/-- The energy-seminorm bound for infimum. -/
theorem seminorm_inf_le (u v : S.energy.dom) :
    S.energy.seminorm ⟨(u : Lp ℝ 2 μ) ⊓ v, S.inf_mem_dom u v⟩ ≤
      (1/2 : ℝ) * (S.energy.seminorm (u+v) + S.energy.seminorm (u-v)) := by
  let a : S.energy.dom := ⟨|(v-u : S.energy.dom).val|, S.abs_mem_dom' (v-u)⟩
  have hid : (⟨(u : Lp ℝ 2 μ) ⊓ v, S.inf_mem_dom u v⟩ : S.energy.dom) =
      (2⁻¹ : ℝ) • ((u+v)-a) := Subtype.ext (inf_eq_half_smul_add_sub_abs_sub' ℝ _ _)
  have ha : S.energy.seminorm a ≤ S.energy.seminorm (u-v) := by
    have hh := Real.sqrt_le_sqrt (S.energy_abs_le (v-u))
    change S.energy.seminorm a ≤ S.energy.seminorm (v-u) at hh
    simpa only [← S.energy.norm_j, map_sub, norm_sub_rev] using hh
  have hh : S.energy.seminorm ((u+v)-a) ≤ S.energy.seminorm (u+v) + S.energy.seminorm a := by
    simpa only [← S.energy.norm_j, map_sub] using norm_sub_le (S.energy.j (u+v)) (S.energy.j a)
  rw [hid, S.energy.seminorm_smul]
  norm_num
  linarith

/-- The energy-seminorm bound for supremum. -/
theorem seminorm_sup_le (u v : S.energy.dom) :
    S.energy.seminorm ⟨(u : Lp ℝ 2 μ) ⊔ v, S.sup_mem_dom u v⟩ ≤
      (1/2 : ℝ) * (S.energy.seminorm (u+v) + S.energy.seminorm (u-v)) := by
  let a : S.energy.dom := ⟨|(v-u : S.energy.dom).val|, S.abs_mem_dom' (v-u)⟩
  have hid : (⟨(u : Lp ℝ 2 μ) ⊔ v, S.sup_mem_dom u v⟩ : S.energy.dom) =
      (2⁻¹ : ℝ) • ((u+v)+a) := Subtype.ext (sup_eq_half_smul_add_add_abs_sub' ℝ _ _)
  have ha : S.energy.seminorm a ≤ S.energy.seminorm (u-v) := by
    have hh := Real.sqrt_le_sqrt (S.energy_abs_le (v-u))
    change S.energy.seminorm a ≤ S.energy.seminorm (v-u) at hh
    simpa only [← S.energy.norm_j, map_sub, norm_sub_rev] using hh
  have hh := S.energy.seminorm_add (u+v) a
  rw [hid, S.energy.seminorm_smul]
  norm_num
  linarith

/-- Every error structure has the Dirichlet (Markov) property. -/
theorem isDirichlet : ∀ u : S.dom,
    ∃ hd : (0 ⊔ (u : Lp ℝ 2 μ)) ⊓ Lp.const 2 μ 1 ∈ S.dom,
      S.energy.E ⟨_, hd⟩ ⟨_, hd⟩ ≤ S.energy.E u u :=
  fun u => ⟨S.unitContraction_mem_dom u, S.energy_unitContraction_le u⟩

end ErrorCalculus.ErrorStructure
