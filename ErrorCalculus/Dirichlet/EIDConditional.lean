import ErrorCalculus.Dirichlet.ConditionalMatrixLemma
import ErrorCalculus.Dirichlet.DirichletCurrentNormal
import ErrorCalculus.Dirichlet.DePhilippisRindlerHypothesis

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus

/-- Positivity of a density under ν suffices to dominate ν by the weighted reference measure. -/
theorem absolutelyContinuous_withDensity_of_ae_ne_zero {α : Type*} [MeasurableSpace α]
    {ν η : Measure α} (hν : ν ≪ η) {p : α → ENNReal} (hp : Measurable p)
    (hpos : ∀ᵐ y ∂ν, p y ≠ 0) : ν ≪ η.withDensity p := by
  intro B hB
  have he : ∀ᵐ y ∂η, p y ≠ 0 → y ∉ B :=
    (ae_withDensity_iff hp).mp (measure_eq_zero_iff_ae_notMem.mp hB)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hν.ae_le he, hpos] with y hy hp
  exact hy hp

/-- Row normalization preserves full span. Zero rows cause no difficulty in this algebraic step. -/
theorem span_polarDirections_of_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hdet : A.det ≠ 0) (w : Fin n → (Fin n → ℝ) → (Fin n → ℝ))
    (y : Fin n → ℝ) (hw : ∀ i, w i y = A i) :
    Submodule.span ℝ (Set.range (fun i => polarDirection (w i) i y)) = ⊤ := by
  have ht : Submodule.span ℝ (Set.range A.row) = ⊤ := by
    rw [← range_vecMulLinear, LinearMap.range_eq_top]
    exact Matrix.vecMul_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  apply le_antisymm le_top
  rw [← ht]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have he : A.row i = polarNorm (w i y) • polarDirection (w i) i y := by
    ext j
    exact (congrFun (hw i) j).symm.trans (polarNorm_mul_direction (w i) i j y).symm
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

namespace ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {n : ℕ}

/-- EBM (4.14). Using the independently proved BH lemma, every conditional row
has nonzero norm ν-a.e.; this gives absolute continuity directly. -/
theorem absolutelyContinuous_eidMeasure_dirichletRow (f : Fin n → S.dom) (i : Fin n) :
    S.eidMeasure f ≪ (S.dirichletRow f i).mass := by
  rw [S.dirichletRow_mass]
  apply absolutelyContinuous_withDensity_of_ae_ne_zero
    (S.eidMeasure_absolutelyContinuous_imageLaw f)
    (((continuous_polarNorm n).measurable.comp
      ((measurable_pi_apply i).comp (S.measurable_conditionalMatrix f))).ennreal_ofReal)
  filter_upwards [S.det_condMatrix_ne_zero_ae f] with y hy
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  apply lt_of_le_of_ne (polarNorm_nonneg _) (Ne.symm ?_)
  intro hz
  have hr := polarNorm_eq_zero.mp hz
  exact hy (Matrix.det_eq_zero_of_row_eq_zero i (fun j => congrFun hr j))

/-- EBM (4.15), full span of the polar directions under the EID measure. -/
theorem span_dirichletRow_ae (f : Fin n → S.dom) :
    ∀ᵐ y ∂S.eidMeasure f,
      Submodule.span ℝ (Set.range (fun i => (S.dirichletRow f i).direction y)) = ⊤ := by
  filter_upwards [S.det_condMatrix_ne_zero_ae f] with y hy
  exact span_polarDirections_of_det_ne_zero (S.conditionalMatrix f y) hy
    (fun i y => S.conditionalMatrix f y i) y (fun _ => rfl)

/-- EBM Theorem 1.7 for generator-domain coordinates, conditional only on DPR.
No boundedness or domain-membership assumption on the Γ entries is imposed. -/
theorem eid_of_generatorDom_of_DPR (f : Fin n → S.dom) (hDPR : DePhilippisRindler n)
    (hf : ∀ i, (f i : Lp ℝ 2 μ) ∈ S.generatorDom) : S.eidMeasure f ≪ volume :=
  hDPR (S.dirichletRow f) (fun i => S.dirichletRow_isNormal f i (hf i))
    (S.eidMeasure f) inferInstance (S.absolutelyContinuous_eidMeasure_dirichletRow f)
    (S.span_dirichletRow_ae f)

end ErrorStructure
end ErrorCalculus
