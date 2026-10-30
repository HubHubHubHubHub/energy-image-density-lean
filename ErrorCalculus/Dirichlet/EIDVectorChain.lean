import ErrorCalculus.Dirichlet.LipschitzEID
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {d : ℕ}

/-- The measurable vector formed from the chosen scalar representatives. -/
def representativeVec (u : Fin d → S.dom) (ω : Ω) : Fin d → ℝ :=
  fun i => S.representative (u i) ω

theorem measurable_representativeVec (u : Fin d → S.dom) :
    Measurable (S.representativeVec u) :=
  measurable_pi_lambda _ (fun i => S.measurable_representative (u i))

theorem coeFn_representativeVec (u : Fin d → S.dom) :
    (fun ω i => (u i : Lp ℝ 2 μ) ω) =ᵐ[μ] S.representativeVec u := by
  filter_upwards [ae_all_iff.mpr (fun i => S.coeFn_representative (u i))] with ω hω
  exact funext hω

/-- The canonical change from the finite sup norm to the Euclidean norm. -/
def euclideanEquiv (d : ℕ) : (Fin d → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm

def toEuclidean (u : Fin d → S.dom) : Ω → EuclideanSpace ℝ (Fin d) :=
  euclideanEquiv d ∘ S.representativeVec u

theorem measurable_toEuclidean (u : Fin d → S.dom) : Measurable (S.toEuclidean u) :=
  (euclideanEquiv d).continuous.measurable.comp (S.measurable_representativeVec u)

/-- membership for any L² class representing the compact C¹ composition. -/
theorem comp_mem_dom_of_contDiff_compactSupport (hd : 0 < d) (u : Fin d → S.dom)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (hk : HasCompactSupport φ)
    (v : Lp ℝ 2 μ) (hv : ⇑v =ᵐ[μ] fun ω => φ (S.representativeVec u ω)) :
    v ∈ S.dom := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hk hφ (by norm_num)
  apply (S.calc d hd u φ L hφ hL v ?_).choose
  exact hv.trans ((S.coeFn_representativeVec u).fun_comp φ).symm

/-- The mixed chain rule, expressed with measurable representatives. -/
theorem gamma_comp_eq_sum (hd : 0 < d) (u : Fin d → S.dom)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (hk : HasCompactSupport φ)
    (v : S.dom) (hv : ⇑(v : Lp ℝ 2 μ) =ᵐ[μ] fun ω => φ (S.representativeVec u ω))
    (z : S.dom) :
    S.Γ v z =ᵐ[μ] fun ω => ∑ k,
      fderiv ℝ φ (S.representativeVec u ω) (Pi.single k 1) * S.Γ (u k) z ω := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hk hφ (by norm_num)
  obtain ⟨_, hchain⟩ := S.calc d hd u φ L hφ hL v
    (hv.trans ((S.coeFn_representativeVec u).fun_comp φ).symm)
  filter_upwards [hchain z, S.coeFn_representativeVec u] with ω hω hu
  simpa only [hu] using hω

theorem compactComp_memLp (u : Fin d → S.dom) {φ : (Fin d → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hk : HasCompactSupport φ) :
    MemLp (fun ω => φ (S.representativeVec u ω)) 2 μ := by
  obtain ⟨C, hC⟩ := hk.exists_bound_of_continuous hφ.continuous
  exact MemLp.of_bound
    (hφ.continuous.measurable.comp (S.measurable_representativeVec u)).aestronglyMeasurable
    C (Eventually.of_forall fun ω => hC _)

/-- The actual domain element used in the weighted IPP hypothesis. -/
def compactComp (hd : 0 < d) (u : Fin d → S.dom) (φ : (Fin d → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hk : HasCompactSupport φ) : S.dom :=
  ⟨(S.compactComp_memLp u hφ hk).toLp _,
    S.comp_mem_dom_of_contDiff_compactSupport hd u hφ hk _
      (S.compactComp_memLp u hφ hk).coeFn_toLp⟩

theorem coeFn_compactComp (hd : 0 < d) (u : Fin d → S.dom) (φ : (Fin d → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hk : HasCompactSupport φ) :
    ⇑(S.compactComp hd u φ hφ hk : Lp ℝ 2 μ) =ᵐ[μ]
      fun ω => φ (S.representativeVec u ω) :=
  (S.compactComp_memLp u hφ hk).coeFn_toLp

end ErrorCalculus.ErrorStructure
