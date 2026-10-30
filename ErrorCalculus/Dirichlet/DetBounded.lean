import ErrorCalculus.Dirichlet.ContractionLipschitz
import ErrorCalculus.Dirichlet.GeneratorWeights
import Mathlib.LinearAlgebra.Matrix.Adjugate

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem AEBounded.congr {f g : Ω → ℝ} (hf : AEBounded (μ := μ) f)
    (h : f =ᵐ[μ] g) : AEBounded (μ := μ) g := by
  obtain ⟨C,hC⟩ := hf
  refine ⟨C, ?_⟩
  filter_upwards [h,hC] with ω he hc
  rwa [← he]

omit [IsProbabilityMeasure μ] in
theorem AEBounded.add {f g : Ω → ℝ} (hf : AEBounded (μ := μ) f)
    (hg : AEBounded (μ := μ) g) : AEBounded (μ := μ) (f+g) := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  refine ⟨C+D, ?_⟩
  filter_upwards [hC,hD] with ω hc hd
  exact (norm_add_le _ _).trans (add_le_add hc hd)

omit [IsProbabilityMeasure μ] in
theorem AEBounded.mul {f g : Ω → ℝ} (hf : AEBounded (μ := μ) f)
    (hg : AEBounded (μ := μ) g) : AEBounded (μ := μ) (f*g) := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  refine ⟨|C| * |D|, ?_⟩
  filter_upwards [hC,hD] with ω hc hd
  simpa only [Pi.mul_apply, norm_mul] using
    mul_le_mul (hc.trans (le_abs_self C)) (hd.trans (le_abs_self D)) (norm_nonneg _) (abs_nonneg _)

namespace ErrorStructure
variable (S : ErrorStructure Ω μ)

/-- Functions admitting an essentially bounded representative in the closed domain.
Null-set changes are allowed; no pointwise algebra structure on L² is assumed. -/
def boundedDomAlgebra : Subalgebra ℝ (Ω → ℝ) where
  carrier := {f | ∃ v : S.dom, ⇑(v : Lp ℝ 2 μ) =ᵐ[μ] f ∧ AEBounded (μ := μ) f}
  algebraMap_mem' c := ⟨S.const c, Lp.coeFn_const _ _ _,
    ⟨‖c‖, Eventually.of_forall (fun _ => le_rfl)⟩⟩
  add_mem' := by
    rintro f g ⟨v,hv,hf⟩ ⟨w,hw,hg⟩
    refine ⟨v+w, ?_, hf.add hg⟩
    exact (Lp.coeFn_add _ _).trans (hv.add hw)
  mul_mem' := by
    rintro f g ⟨v,hv,hf⟩ ⟨w,hw,hg⟩
    exact ⟨S.boundedMul v w (hf.congr hv.symm) (hg.congr hw.symm),
      (S.coeFn_boundedMul _ _ _ _).trans (hv.mul hw), hf.mul hg⟩

/-- Domain elements with an essential bound belong to the function algebra. -/
theorem mem_boundedDomAlgebra (v : S.dom)
    (hv : AEBounded (μ := μ) (v : Lp ℝ 2 μ)) :
    (fun ω => (v : Lp ℝ 2 μ) ω) ∈ S.boundedDomAlgebra := ⟨v, EventuallyEq.rfl, hv⟩

/-- A chosen L² domain representative of a function in the bounded algebra. -/
def boundedDomElement (f : Ω → ℝ) (hf : f ∈ S.boundedDomAlgebra) : S.dom := hf.choose

theorem coeFn_boundedDomElement (f : Ω → ℝ) (hf : f ∈ S.boundedDomAlgebra) :
    ⇑(S.boundedDomElement f hf : Lp ℝ 2 μ) =ᵐ[μ] f := hf.choose_spec.1

theorem bounded_boundedDomElement (f : Ω → ℝ) (hf : f ∈ S.boundedDomAlgebra) :
    AEBounded (μ := μ) (S.boundedDomElement f hf : Lp ℝ 2 μ) :=
  hf.choose_spec.2.congr (S.coeFn_boundedDomElement f hf).symm

/-- Every C¹ scalar function preserves the bounded domain algebra. The compact
extension is only used on the bounded essential range of the argument. -/
theorem contDiff_comp_mem_boundedDomAlgebra {f : Ω → ℝ} (hf : f ∈ S.boundedDomAlgebra)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) : (F ∘ f) ∈ S.boundedDomAlgebra := by
  obtain ⟨v,hv,C,hC⟩ := hf
  let H : ℝ → ℝ := fun x => truncationBump C x * F x
  have hH : ContDiff ℝ 1 H := (truncationBump C).contDiff.mul hF
  have hk : HasCompactSupport H := (truncationBump C).hasCompactSupport.mul_right
  obtain ⟨L,hL⟩ := hH.lipschitzWith_of_hasCompactSupport hk (by norm_num)
  have he : (fun ω => H ((v : Lp ℝ 2 μ) ω)) =ᵐ[μ] F ∘ f := by
    filter_upwards [hv,hC] with ω hv hc
    change truncationBump C _ * F _ = _
    rw [hv, truncationBump_eq_one (by simpa only [Real.norm_eq_abs] using hc), one_mul]
    rfl
  obtain ⟨D,hD⟩ := hk.exists_bound_of_continuous hH.continuous
  refine ⟨S.lipschitzComp hL v, (S.coeFn_lipschitzComp hL v).trans he, D, ?_⟩
  filter_upwards [he] with ω hω
  have h := hD ((v : Lp ℝ 2 μ) ω)
  change H ((v : Lp ℝ 2 μ) ω) = (F ∘ f) ω at hω
  rwa [← hω]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- determinants are bounded domain functions, by the algebra rule. -/
theorem det_mem_dom_of_bounded (A : n → n → Ω → ℝ)
    (hA : ∀ i j, A i j ∈ S.boundedDomAlgebra) :
    (fun ω => (Matrix.of (fun i j => A i j ω)).det) ∈ S.boundedDomAlgebra := by
  let B : Matrix n n S.boundedDomAlgebra := fun i j => ⟨A i j, hA i j⟩
  have he : (fun ω => (Matrix.of (fun i j => A i j ω)).det) =
      ((S.boundedDomAlgebra.val B.det) : Ω → ℝ) := by
    funext ω
    have h := (Pi.evalRingHom (fun _ : Ω => ℝ) ω).map_det
      (Matrix.of (fun i j => A i j))
    have h' := S.boundedDomAlgebra.val.map_det B
    exact h.symm.trans (congrFun h'.symm ω)
  rw [he]
  exact B.det.property

/-- The adjugate entries are also bounded domain functions. -/
theorem adjugate_mem_dom_of_bounded (A : n → n → Ω → ℝ)
    (hA : ∀ i j, A i j ∈ S.boundedDomAlgebra) (i j : n) :
    (fun ω => (Matrix.of (fun k l => A k l ω)).adjugate i j) ∈ S.boundedDomAlgebra := by
  let B : Matrix n n S.boundedDomAlgebra := fun k l => ⟨A k l, hA k l⟩
  have he : (fun ω => (Matrix.of (fun k l => A k l ω)).adjugate i j) =
      ((S.boundedDomAlgebra.val (B.adjugate i j)) : Ω → ℝ) := by
    funext ω
    have h := congrArg (fun M : Matrix n n ℝ => M i j)
      ((Pi.evalRingHom (fun _ : Ω => ℝ) ω).map_adjugate (Matrix.of (fun k l => A k l)))
    have h' := congrArg (fun M : Matrix n n (Ω → ℝ) => M i j)
      (S.boundedDomAlgebra.val.map_adjugate B)
    exact h.symm.trans (congrFun h'.symm ω)
  rw [he]
  exact (B.adjugate i j).property

end ErrorStructure
end ErrorCalculus
