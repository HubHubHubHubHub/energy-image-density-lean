import ErrorCalculus.Dirichlet.QuadForm
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The algebraic carré du champ on a linear L² domain. -/
structure ErrorData (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] where
  dom : Submodule ℝ (Lp ℝ 2 μ)
  Γ : dom →ₗ[ℝ] dom →ₗ[ℝ] Lp ℝ 1 μ
  Γ_symm : ∀ u v, Γ u v = Γ v u
  Γ_nonneg : ∀ u, 0 ≤ᵐ[μ] ⇑(Γ u u)

/-- integration is a linear functional on L¹ classes. -/
def integralL1 : Lp ℝ 1 μ →ₗ[ℝ] ℝ where
  toFun f := ∫ ω, f ω ∂μ
  map_add' f g := by
    rw [integral_congr_ae (Lp.coeFn_add f g)]
    exact integral_add (L1.integrable_coeFn f) (L1.integrable_coeFn g)
  map_smul' c f := by
    rw [integral_congr_ae (Lp.coeFn_smul c f)]
    exact integral_smul c f

namespace ErrorData
/-- The energy form, with the normalization 1/2. -/
def energy (S : ErrorData Ω μ) : QuadForm (Lp ℝ 2 μ) where
  dom := S.dom
  E :=
    { toFun := fun u => (1 / 2 : ℝ) • (integralL1.comp (S.Γ u))
      map_add' := by intro u v; ext w; simp [mul_add]
      map_smul' := by intro c u; ext w; simp [mul_left_comm] }
  symm u v := by
    change (1/2:ℝ) * integralL1 (S.Γ u v) = (1/2:ℝ) * integralL1 (S.Γ v u)
    rw [S.Γ_symm]
  nonneg u := mul_nonneg (by norm_num) (integral_nonneg_of_ae (S.Γ_nonneg u))

@[simp] theorem energy_apply (S : ErrorData Ω μ) (u v : S.dom) :
    S.energy.E u v = (1/2:ℝ) * ∫ ω, S.Γ u v ω ∂μ := rfl
end ErrorData

/-- Bouleau's five axioms, with C¹ Lipschitz calculus on arbitrary finite tuples. -/
structure ErrorStructure (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] extends ErrorData Ω μ where
  dense : Dense (dom : Set (Lp ℝ 2 μ))
  «calc» : ∀ (m : ℕ), 0 < m → ∀ (u : Fin m → dom) (F : (Fin m → ℝ) → ℝ)
    (L : ℝ≥0), ContDiff ℝ 1 F → LipschitzWith L F →
    ∀ w : Lp ℝ 2 μ, (⇑w =ᵐ[μ] fun ω => F (fun i => (u i : Lp ℝ 2 μ) ω)) →
    ∃ hw : w ∈ dom, ∀ v : dom,
      ⇑(Γ ⟨w, hw⟩ v) =ᵐ[μ] fun ω => ∑ i,
        fderiv ℝ F (fun j => (u j : Lp ℝ 2 μ) ω) (Pi.single i 1) * Γ (u i) v ω
  energy_closed : toErrorData.energy.IsClosed
  one_mem : Lp.const 2 μ (1 : ℝ) ∈ dom

namespace ErrorStructure
/-- The energy of an error structure. -/
abbrev energy (S : ErrorStructure Ω μ) := S.toErrorData.energy

/-- Every finite Lipschitz composition has an L² representative. -/
theorem composition_memLp {m : ℕ} (u : Fin m → Lp ℝ 2 μ)
    {F : (Fin m → ℝ) → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) :
    MemLp (fun ω => F (fun i => u i ω)) 2 μ := by
  have hu : MemLp (fun ω i => u i ω) 2 μ := MemLp.of_eval fun i => Lp.memLp (u i)
  have hg : LipschitzWith L (fun x => F x - F 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he : (F x - F 0) - (F y - F 0) = F x - F y := by ring
    simpa only [dist_eq_norm, he] using hF.dist_le_mul x y
  have hh := hg.comp_memLp (by simp) hu
  have hc : MemLp (fun _ : Ω => F 0) 2 μ := memLp_const _
  convert hh.add hc using 1
  ext ω
  dsimp
  ring

/-- existence of the class quantified over in the calculus property. -/
theorem exists_composition {m : ℕ} (u : Fin m → Lp ℝ 2 μ)
    {F : (Fin m → ℝ) → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) :
    ∃ w : Lp ℝ 2 μ, ⇑w =ᵐ[μ] fun ω => F (fun i => u i ω) := by
  let h := composition_memLp u hF
  exact ⟨h.toLp _, h.coeFn_toLp⟩

/-- zero energy is equivalent to an almost surely zero carré du champ. -/
theorem energy_eq_zero_iff (S : ErrorStructure Ω μ) (u : S.dom) :
    S.energy.E u u = 0 ↔ ⇑(S.Γ u u) =ᵐ[μ] 0 := by
  rw [ErrorData.energy_apply, mul_eq_zero]
  simp only [show (1 / 2 : ℝ) ≠ 0 by norm_num, false_or]
  exact integral_eq_zero_iff_of_nonneg_ae (S.Γ_nonneg u) (L1.integrable_coeFn _)

/-- The algebraic data of the zero error structure. -/
def zeroData : ErrorData Ω μ where
  dom := ⊤
  Γ := 0
  Γ_symm _ _ := rfl
  Γ_nonneg _ := by
    change 0 ≤ᵐ[μ] ⇑(0 : Lp ℝ 1 μ)
    filter_upwards [Lp.coeFn_zero ℝ 1 μ] with ω hω
    exact le_of_eq hω.symm

/-- The zero data have identically zero energy. -/
@[simp] theorem zeroData_energy (u v : (zeroData (Ω := Ω) (μ := μ)).dom) :
    (zeroData (Ω := Ω) (μ := μ)).energy.E u v = 0 := by
  change (1 / 2 : ℝ) * integralL1 (0 : Lp ℝ 1 μ) = 0
  simp

/-- The zero form on all L² is closed. -/
theorem zeroData_closed : (zeroData (Ω := Ω) (μ := μ)).energy.IsClosed := by
  intro u _ v _
  refine ⟨Submodule.mem_top, ?_⟩
  simp only [zeroData_energy]
  exact tendsto_const_nhds

/-- a nonempty model of all five axioms on every probability space. -/
def zero : ErrorStructure Ω μ where
  toErrorData := zeroData
  dense := by simp [zeroData]
  «calc» m hm u F L hC hL w hw := by
    refine ⟨Submodule.mem_top, fun v => ?_⟩
    have hz := Lp.coeFn_zero ℝ 1 μ
    filter_upwards [hz] with ω hω
    change (0 : Lp ℝ 1 μ) ω = ∑ i,
      fderiv ℝ F (fun j => (u j : Lp ℝ 2 μ) ω) (Pi.single i 1) * (0 : Lp ℝ 1 μ) ω
    simp only [hω, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  energy_closed := zeroData_closed
  one_mem := Submodule.mem_top

end ErrorStructure
end ErrorCalculus
