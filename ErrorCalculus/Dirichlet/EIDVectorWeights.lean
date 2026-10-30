import ErrorCalculus.Dirichlet.EIDVectorChain

noncomputable section
open MeasureTheory Filter Topology
namespace ErrorCalculus.ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {d : ℕ}

/-- a bounded measurable left inverse of the carré du champ matrix. -/
structure MalliavinWeights (u : Fin d → S.dom) (w : Fin d → Fin d → Ω → ℝ) : Prop where
  measurable : ∀ i j, Measurable (w i j)
  bounded : ∀ i j, ∃ C : ℝ, ∀ ω, ‖w i j ω‖ ≤ C
  inverse : ∀ i k, ∀ᵐ ω ∂μ,
    ∑ j, w i j ω * S.Γ (u j) (u k) ω = if i = k then 1 else 0

/-- symmetry of Γ turns the left inverse identity into the weighted chain rule. -/
theorem fderiv_comp_eq_sum_weights_gamma (hd : 0 < d) (u : Fin d → S.dom)
    {w : Fin d → Fin d → Ω → ℝ} (hw : S.MalliavinWeights u w)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (hk : HasCompactSupport φ)
    (v : S.dom) (hv : ⇑(v : Lp ℝ 2 μ) =ᵐ[μ] fun ω => φ (S.representativeVec u ω))
    (i : Fin d) :
    (fun ω => fderiv ℝ φ (S.representativeVec u ω) (Pi.single i 1)) =ᵐ[μ]
      fun ω => ∑ j, w i j ω * S.Γ v (u j) ω := by
  classical
  filter_upwards [ae_all_iff.mpr (fun j => S.gamma_comp_eq_sum hd u hφ hk v hv (u j)),
    ae_all_iff.mpr (hw.inverse i)] with ω hc hi
  symm
  simp_rw [hc]
  calc
    _ = ∑ k, fderiv ℝ φ (S.representativeVec u ω) (Pi.single k 1) *
        (∑ j, w i j ω * S.Γ (u j) (u k) ω) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      rw [S.Γ_symm (u k) (u j)]
      ring
    _ = _ := by simp [hi]

theorem MalliavinWeights.integrable_sum_gamma {u : Fin d → S.dom}
    {w : Fin d → Fin d → Ω → ℝ} (hw : S.MalliavinWeights u w) (i : Fin d) (v : S.dom) :
    Integrable (fun ω => ∑ j, w i j ω * S.Γ v (u j) ω) μ := by
  apply integrable_finsetSum
  intro j _
  obtain ⟨C, hC⟩ := hw.bounded i j
  exact (L1.integrable_coeFn (S.Γ v (u j))).bdd_mul
    (hw.measurable i j).aestronglyMeasurable (Eventually.of_forall hC)

end ErrorCalculus.ErrorStructure
