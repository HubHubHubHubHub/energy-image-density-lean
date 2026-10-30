import ErrorCalculus.Dirichlet.LowerSemicontinuous
import ErrorCalculus.Dirichlet.Calculus
import ErrorCalculus.Dirichlet.LipschitzRegularize

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Uniform errors tending to zero imply convergence of the corresponding L² classes. -/
theorem tendsto_Lp_of_uniform_error {q : ℕ → Lp ℝ 2 μ} {w : Lp ℝ 2 μ}
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |q n ω - w ω| ≤ e n) : Tendsto q atTop (𝓝 w) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound n : ‖q n - w‖ ≤ e n * ‖Lp.const 2 μ (1 : ℝ)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (q n) w, hb n,
      Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with ω hs hb hc
    simpa only [hs, Pi.sub_apply, hc, Function.const_apply, norm_one, mul_one,
      Real.norm_eq_abs] using hb
  exact squeeze_zero (fun _ => norm_nonneg _) hbound (by simpa using he.mul_const ‖Lp.const 2 μ (1 : ℝ)‖)

/-- Scalar composition in L², for the actual representative of any L² class. -/
theorem lipschitz_scalar_memLp (u : Lp ℝ 2 μ) {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) : MemLp (fun ω => F (u ω)) 2 μ := by
  let p : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  exact composition_memLp (fun _ : Fin 1 => u) (hF.comp p.lipschitz)

variable (S : ErrorStructure Ω μ)

/--
arbitrary scalar Lipschitz calculus, by mollification and L.3. Only closedness and the C¹ calculus
are used; no energy image density hypothesis.
-/
theorem lipschitz_comp_mem_dom_energy_le {F : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (u : S.dom) (w : Lp ℝ 2 μ)
    (hw : ⇑w =ᵐ[μ] fun ω => F ((u : Lp ℝ 2 μ) ω)) :
    ∃ hd : w ∈ S.dom, S.energy.E ⟨w, hd⟩ ⟨w, hd⟩ ≤ (L : ℝ)^2 * S.energy.E u u := by
  let hf n := lipschitz_scalar_memLp (u : Lp ℝ 2 μ) (lipschitzMollify_lipschitz hF n)
  let q n := (hf n).toLp _
  have hq n : ⇑(q n) =ᵐ[μ] fun ω => lipschitzMollify F n ((u : Lp ℝ 2 μ) ω) :=
    (hf n).coeFn_toLp
  have hd n : q n ∈ S.dom :=
    (S.chain_one ((lipschitzMollify_contDiff hF n).of_le (by simp))
      (lipschitzMollify_lipschitz hF n) u (q n) (hq n)).choose
  let x n : S.dom := ⟨q n, hd n⟩
  have he n : S.energy.E (x n) (x n) ≤ (L : ℝ)^2 * S.energy.E u u :=
    S.energy_contraction ((lipschitzMollify_contDiff hF n).of_le (by simp))
      (lipschitzMollify_lipschitz hF n) u (x n) (hq n)
  have ht : Tendsto q atTop (𝓝 w) := by
    apply tendsto_Lp_of_uniform_error (e := fun n => (L : ℝ) * (1/2 : ℝ)^n)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).const_mul (L : ℝ)
    · intro n
      filter_upwards [hq n, hw] with ω hq hw
      rw [hq, hw]
      exact abs_lipschitzMollify_sub_le hF n _
  exact S.energy_closed.mem_dom_of_tendsto_of_energy_le (x := x) ht he

/-- domain membership for every scalar Lipschitz function. -/
theorem lipschitz_comp_mem_dom {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (u : S.dom) (w : Lp ℝ 2 μ)
    (hw : ⇑w =ᵐ[μ] fun ω => F ((u : Lp ℝ 2 μ) ω)) : w ∈ S.dom :=
  (S.lipschitz_comp_mem_dom_energy_le hF u w hw).choose

/-- The exact squared Lipschitz energy bound, without EID. -/
theorem energy_lipschitz_comp_le {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (u w : S.dom)
    (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun ω => F ((u : Lp ℝ 2 μ) ω)) :
    S.energy.E w w ≤ (L : ℝ)^2 * S.energy.E u u :=
  (S.lipschitz_comp_mem_dom_energy_le hF u w hw).choose_spec

/-- A canonical domain element for an arbitrary scalar Lipschitz composition. -/
def lipschitzComp {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (u : S.dom) : S.dom :=
  let h := lipschitz_scalar_memLp (u : Lp ℝ 2 μ) hF
  ⟨h.toLp _, S.lipschitz_comp_mem_dom hF u (h.toLp _) h.coeFn_toLp⟩

/-- The canonical Lipschitz composition has the required representative. -/
theorem coeFn_lipschitzComp {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (u : S.dom) :
    ⇑(S.lipschitzComp hF u : Lp ℝ 2 μ) =ᵐ[μ] fun ω => F ((u : Lp ℝ 2 μ) ω) :=
  (lipschitz_scalar_memLp (u : Lp ℝ 2 μ) hF).coeFn_toLp

end ErrorCalculus.ErrorStructure
