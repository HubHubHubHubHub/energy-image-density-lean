import DprBridge.Coordinate
import ErrorCalculus.Dirichlet.EIDConditionalVariants

/-!
# EID

## Main results
General Bouleau–Hirsch EID for every `ErrorStructure Ω μ`, with μ a probability measure, in every
dimension. Only the DPR argument is discharged; generator-domain memberships are retained wherever
they occur. The elaboration option below is inherited from the sources; the kernel is unchanged.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology Matrix ErrorCalculus
open scoped InnerProductSpace
namespace DprBridge
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {n : ℕ}

/-- specialize `ErrorCalculus.ErrorStructure.eid_of_generatorDom_of_DPR` without a DPR argument. -/
theorem eid_of_generatorDom (f : Fin n → S.dom) 
    (hf : ∀ i, (f i : Lp ℝ 2 μ) ∈ S.generatorDom) : S.eidMeasure f ≪ volume :=
  ErrorCalculus.ErrorStructure.eid_of_generatorDom_of_DPR S f (dePhilippisRindler n) hf

/-- specialize `ErrorCalculus.ErrorStructure.eid_restrict_seq_of_DPR` without a DPR argument. -/
theorem eid_restrict_seq (f g : Fin n → S.dom) 
    (hg : ∀ j, (g j : Lp ℝ 2 μ) ∈ S.generatorDom) :
    (S.eidMeasure f).restrict (S.mixedDetPos f g) ≪ volume :=
  ErrorCalculus.ErrorStructure.eid_restrict_seq_of_DPR S f g (dePhilippisRindler n) hg

/--
EID for every error structure on a probability space, in every dimension: the pushforward of μ
restricted to {det Γ[f] > 0} is absolutely continuous with respect to Lebesgue measure. Specialize
`ErrorCalculus.ErrorStructure.eid_of_DPR` by discharging DPR, without modifying the definitions of
`ErrorStructure` or `eidMeasure`. This result discharges the explicit EID hypotheses of the
variants, products and monotone limit; no new specialization is added.
-/
theorem eid_unconditional (f : Fin n → S.dom)  :
    S.eidMeasure f ≪ volume :=
  ErrorCalculus.ErrorStructure.eid_of_DPR S f (dePhilippisRindler n)

/--
specialize `ErrorCalculus.ErrorStructure.eid_toEuclidean_of_generatorDom_of_DPR` without a DPR
argument.
-/
theorem eid_toEuclidean_of_generatorDom (f : Fin n → S.dom)
     (hf : ∀ i, (f i : Lp ℝ 2 μ) ∈ S.generatorDom) :
    (μ.restrict {ω | 0 < (Matrix.of (fun i j => S.Γ (f i) (f j) ω)).det}).map
      (S.toEuclidean f) ≪ volume :=
  ErrorCalculus.ErrorStructure.eid_toEuclidean_of_generatorDom_of_DPR S f (dePhilippisRindler n) hf

/-- specialize `ErrorCalculus.ErrorStructure.eid_of_DPR_toEuclidean` without a DPR argument. -/
theorem eid_toEuclidean (f : Fin n → S.dom)  :
    (μ.restrict {ω | 0 < (Matrix.of (fun i j => S.Γ (f i) (f j) ω)).det}).map
      (S.toEuclidean f) ≪ volume :=
  ErrorCalculus.ErrorStructure.eid_of_DPR_toEuclidean S f (dePhilippisRindler n)

end DprBridge
