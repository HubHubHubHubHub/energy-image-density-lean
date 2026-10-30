import ErrorCalculus.Dirichlet.DensityGamma
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators NNReal
namespace ErrorCalculus

/-- A finite family of bounded functions is bounded in the product norm. -/
theorem finite_tuple_bound {m : ℕ} {g : Fin m → ℝ → ℝ}
    (hg : ∀ i, ∃ C, ∀ x, ‖g i x‖ ≤ C) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖fun i => g i x‖ ≤ C := by
  choose C hC using hg
  refine ⟨∑ i, |C i|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), fun x => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mpr
  intro i
  exact (hC i x).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)))

/-- The ordinary finite-dimensional chain rule, before taking classes. -/
theorem deriv_comp_tuple {m : ℕ} {g : Fin m → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 1 (g i)) {F : (Fin m → ℝ) → ℝ}
    (hF : ContDiff ℝ 1 F) (x : ℝ) :
    deriv (fun y => F (fun i => g i y)) x =
      fderiv ℝ F (fun i => g i x) (fun i => deriv (g i) x) := by
  exact ((hF.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_pi.mpr fun i => ((hg i).differentiable (by norm_num) x).hasDerivAt)).deriv

/-- C¹ Lipschitz compositions preserve C¹_b. -/
theorem IsC1Bounded.comp_tuple {m : ℕ} {g : Fin m → ℝ → ℝ}
    (hg : ∀ i, IsC1Bounded (g i)) {F : (Fin m → ℝ) → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) :
    IsC1Bounded (fun x => F (fun i => g i x)) := by
  obtain ⟨C, hC0, hC⟩ := finite_tuple_bound (fun i => (hg i).2.1)
  obtain ⟨D, hD0, hD⟩ := finite_tuple_bound (fun i => (hg i).2.2)
  refine ⟨hF.comp (contDiff_pi.mpr fun i => (hg i).1), ⟨(L:ℝ)*C + ‖F 0‖, fun x => ?_⟩,
    ⟨(L:ℝ)*D, fun x => ?_⟩⟩
  · have hb := hL.dist_le_mul (fun i => g i x) 0
    simp only [dist_eq_norm, sub_zero] at hb
    have ha := norm_add_le (F (fun i => g i x)-F 0) (F 0)
    rw [sub_add_cancel] at ha
    exact ha.trans (add_le_add (hb.trans (mul_le_mul_of_nonneg_left (hC x) L.coe_nonneg)) le_rfl)
  · rw [deriv_comp_tuple (fun i => (hg i).1) hF]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hL) (hD x) (norm_nonneg _) L.coe_nonneg)

/-- Coordinate expression of a linear differential. -/
theorem fderiv_tuple_sum {m : ℕ} (F : (Fin m → ℝ) → ℝ) (y z : Fin m → ℝ) :
    fderiv ℝ F y z = ∑ i, fderiv ℝ F y (Pi.single i 1) * z i := by
  have hz : z = ∑ i, z i • Pi.single i (1:ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hz, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

variable (ρ : ℝ → ℝ) [SmoothDensity ρ] [IsProbabilityMeasure (densityMeasure ρ)]

/--
A C¹ Lipschitz composition of finitely many proto-domain elements, represented by w in L²,
belongs to the proto-domain and satisfies Γ(w, v) = Σᵢ ∂ᵢF(u) Γ(uᵢ, v) almost everywhere for every
domain
test v.
-/
theorem protoData_calculus (m : ℕ) (_hm : 0 < m) (u : Fin m → protoDom ρ)
    (F : (Fin m → ℝ) → ℝ) (L : ℝ≥0) (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F)
    (w : Lp ℝ 2 (densityMeasure ρ))
    (hw : ⇑w =ᵐ[densityMeasure ρ] fun x => F (fun i => (u i : Lp ℝ 2 (densityMeasure ρ)) x)) :
    ∃ hd : w ∈ (protoData ρ).dom, ∀ v : (protoData ρ).dom,
      ⇑((protoData ρ).Γ ⟨w, hd⟩ v) =ᵐ[densityMeasure ρ] fun x => ∑ i,
        fderiv ℝ F (fun j => (u j : Lp ℝ 2 (densityMeasure ρ)) x) (Pi.single i 1) *
          (protoData ρ).Γ (u i) v x := by
  let g := fun x => F (fun i => rep ρ (u i) x)
  have hg : IsC1Bounded g := IsC1Bounded.comp_tuple (fun i => rep_isC1Bounded ρ (u i)) hF hL
  have hu : ∀ᵐ x ∂densityMeasure ρ, ∀ i, (u i : Lp ℝ 2 (densityMeasure ρ)) x = rep ρ (u i) x :=
    ae_all_iff.mpr (fun i => coeFn_rep ρ (u i))
  have hwg : ⇑w =ᵐ[densityMeasure ρ] g := by
    filter_upwards [hw, hu] with x hx hux
    rw [hx]
    exact congrArg F (funext hux)
  have hd : w ∈ protoDom ρ := ⟨g, hg, hwg⟩
  refine ⟨hd, fun v => ?_⟩
  have hrep := rep_unique ρ ⟨w, hd⟩ hg.1.continuous hwg
  have hΓ : ∀ᵐ x ∂densityMeasure ρ, ∀ i,
      gamma₀ ρ (u i) v x = deriv (rep ρ (u i)) x * deriv (rep ρ v) x :=
    ae_all_iff.mpr (fun i => coeFn_gamma₀ ρ (u i) v)
  filter_upwards [coeFn_gamma₀ ρ ⟨w, hd⟩ v, hu, hΓ] with x hx hux hgam
  change gamma₀ ρ ⟨w, hd⟩ v x = _
  rw [hx, hrep]
  have htuple : (fun j => (u j : Lp ℝ 2 (densityMeasure ρ)) x) = fun j => rep ρ (u j) x := funext hux
  change deriv g x * deriv (rep ρ v) x = _
  rw [deriv_comp_tuple (fun i => (rep_isC1Bounded ρ (u i)).1) hF, fderiv_tuple_sum,
    Finset.sum_mul, htuple]
  apply Finset.sum_congr rfl
  intro i _
  change _ = _ * gamma₀ ρ (u i) v x
  rw [hgam i]
  ring

/-- The four pre-closure axioms, without modifying ErrorStructure. -/
structure ProtoErrorStructure (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] extends ErrorData Ω μ where
  dense : Dense (dom : Set (Lp ℝ 2 μ))
  «calc» : ∀ (m : ℕ), 0 < m → ∀ (u : Fin m → dom) (F : (Fin m → ℝ) → ℝ)
    (L : ℝ≥0), ContDiff ℝ 1 F → LipschitzWith L F →
    ∀ w : Lp ℝ 2 μ, (⇑w =ᵐ[μ] fun ω => F (fun i => (u i : Lp ℝ 2 μ) ω)) →
    ∃ hw : w ∈ dom, ∀ v : dom,
      ⇑(Γ ⟨w, hw⟩ v) =ᵐ[μ] fun ω => ∑ i,
        fderiv ℝ F (fun j => (u j : Lp ℝ 2 μ) ω) (Pi.single i 1) * Γ (u i) v ω
  one_mem : Lp.const 2 μ (1 : ℝ) ∈ dom

def ProtoErrorStructure.toErrorStructure {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (S : ProtoErrorStructure Ω μ) (h : S.toErrorData.energy.IsClosed) :
    ErrorStructure Ω μ := { S with energy_closed := h }

/-- Energy of the proto-structure, with the same normalization as ErrorData. -/
abbrev ProtoErrorStructure.energy {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (S : ProtoErrorStructure Ω μ) := S.toErrorData.energy

/-- Transport along an equality of probability measures. -/
def ProtoErrorStructure.transport {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ = ν) (S : ProtoErrorStructure Ω μ) :
    ProtoErrorStructure Ω ν := h ▸ S

theorem ProtoErrorStructure.isClosable_transport {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ = ν) (S : ProtoErrorStructure Ω μ)
    (hS : S.energy.IsClosable) : (S.transport h).energy.IsClosable := by
  subst ν
  exact hS

/-- All four proto-structure axioms for the positive density. -/
def densityProto : ProtoErrorStructure ℝ (densityMeasure ρ) where
  toErrorData := protoData ρ
  dense := dense_protoDom ρ
  «calc» := protoData_calculus ρ
  one_mem := const_mem_protoDom ρ 1

end ErrorCalculus
