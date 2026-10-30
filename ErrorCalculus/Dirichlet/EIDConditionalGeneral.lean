import ErrorCalculus.Dirichlet.EIDConditional
import ErrorCalculus.Dirichlet.MixedDirichletCurrent

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {n : ℕ}

/-- Positivity set of a mixed conditional determinant. -/
def mixedDetPos (f g : Fin n → S.dom) : Set (Fin n → ℝ) :=
  {y | 0 < (S.mixedConditionalMatrix f g y).det}

theorem measurableSet_mixedDetPos (f g : Fin n → S.dom) : MeasurableSet (S.mixedDetPos f g) :=
  measurableSet_lt measurable_const
    (continuous_id.matrix_det.measurable.comp (S.measurable_mixedConditionalMatrix f g))

/-- EBM (4.20)–(4.21) and DPR for a generator approximation. No symmetry of the
mixed matrix is assumed: the current directions are its columns. -/
theorem eid_restrict_seq_of_DPR (f g : Fin n → S.dom) (hDPR : DePhilippisRindler n)
    (hg : ∀ j, (g j : Lp ℝ 2 μ) ∈ S.generatorDom) :
    (S.eidMeasure f).restrict (S.mixedDetPos f g) ≪ volume := by
  let ν := (S.eidMeasure f).restrict (S.mixedDetPos f g)
  have hac : ν ≪ S.eidImageLaw f :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
      (S.eidMeasure_absolutelyContinuous_imageLaw f)
  have hdet : ∀ᵐ y ∂ν, 0 < (S.mixedConditionalMatrix f g y).det :=
    ae_restrict_mem (S.measurableSet_mixedDetPos f g)
  apply hDPR (S.dirichletRowSeq f g) (fun j => S.dirichletRowSeq_isNormal f g j (hg j))
    ν inferInstance
  · intro j
    change ν ≪ (S.eidImageLaw f).withDensity
      (fun y => ENNReal.ofReal (polarNorm (fun i => S.condMatrixEntry f g i j y)))
    apply absolutelyContinuous_withDensity_of_ae_ne_zero hac
      (((continuous_polarNorm n).measurable.comp
        (measurable_pi_lambda _ (fun i => (Lp.stronglyMeasurable _).measurable))).ennreal_ofReal)
    filter_upwards [hdet] with y hy
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    apply lt_of_le_of_ne (polarNorm_nonneg _) (Ne.symm ?_)
    intro hz
    have hr := polarNorm_eq_zero.mp hz
    exact hy.ne' (Matrix.det_eq_zero_of_column_eq_zero j (fun i => congrFun hr i))
  · filter_upwards [hdet] with y hy
    exact span_polarDirections_of_det_ne_zero (S.mixedConditionalMatrix f g y).transpose
      (by simpa using hy.ne') (fun j y i => S.condMatrixEntry f g i j y) y (fun _ => rfl)

/-- The conditional determinant is positive ν-a.e., by PSD and the proved BH lemma. -/
theorem det_condMatrix_pos_ae (f : Fin n → S.dom) :
    ∀ᵐ y ∂S.eidMeasure f, 0 < (S.conditionalMatrix f y).det := by
  filter_upwards [S.det_condMatrix_ne_zero_ae f,
    (S.eidMeasure_absolutelyContinuous_imageLaw f).ae_le
      (S.imageGammaMatrixGeneral_posSemidef_ae f)] with y hn hp
  exact lt_of_le_of_ne hp.det_nonneg (Ne.symm hn)

/-- EBM Theorem 1.7 for every finite tuple in the form domain, conditional only
on the named De Philippis–Rindler hypothesis. The final limit uses an eventual
cover, correctly accounting for negative determinants of the mixed approximants. -/
theorem eid_of_DPR (f : Fin n → S.dom) (hDPR : DePhilippisRindler n) :
    S.eidMeasure f ≪ volume := by
  let g : ℕ → Fin n → S.dom := fun k j => S.generatorApprox (f j) k
  obtain ⟨s, hs, hae⟩ := S.det_condMatrix_seq_tendsto_ae f g
    (fun j => S.generatorApprox_tendsto_formSpace (f j))
  apply absolutelyContinuous_of_ae_eventually_mem (fun k => S.mixedDetPos f (g (s k)))
    (fun k => S.measurableSet_mixedDetPos f (g (s k)))
    (fun k => S.eid_restrict_seq_of_DPR f (g (s k)) hDPR
      (fun j => S.generatorApprox_mem_generatorDom (f j) (s k)))
  filter_upwards [hae, S.det_condMatrix_pos_ae f] with y hy hp
  exact hy.eventually (eventually_gt_nhds hp)

end ErrorCalculus.ErrorStructure
