import ErrorCalculus.Dirichlet.WienerCoordinates
import ErrorCalculus.Dirichlet.ClosureUniqueness
import Foundations.CameronMartin.WienerIntegral

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Topology
open scoped InnerProductSpace
namespace ErrorCalculus

theorem wienerCoordinate_eq_gaussianCoordinate (i : ℕ) :
    wienerCoordinate i = Foundations.gaussianCoordinate i :=
  Lp.ext ((coeFn_wienerCoordinate i).trans (Foundations.coe_gaussianCoordinate i).symm)

/-- Finite first-chaos sums, as elements of the closed domain. -/
def wienerFirstSum (s : Finset ℕ) (a : ℕ → ℝ) : wienerStructure.dom :=
  ∑ i ∈ s, a i • wienerX i

theorem coe_wienerFirstSum (s : Finset ℕ) (a : ℕ → ℝ) :
    (wienerFirstSum s a : Lp ℝ 2 wienerCoord) = Foundations.wienerPartial a s := by
  simp only [wienerFirstSum, Foundations.wienerPartial, Submodule.coe_sum,
    Submodule.coe_smul, wienerX, wienerCoordinate_eq_gaussianCoordinate]

/-- The W2 coordinate formula identifies Γ with the ambient scalar product on finite sums. -/
theorem wienerFirstSum_Γ (s t : Finset ℕ) (a b : ℕ → ℝ) :
    wienerStructure.Γ (wienerFirstSum s a) (wienerFirstSum t b) =
      Lp.const 1 wienerCoord
        ⟪(wienerFirstSum s a : Lp ℝ 2 wienerCoord),
          (wienerFirstSum t b : Lp ℝ 2 wienerCoord)⟫_ℝ := by
  classical
  let C := Lp.constₗ 1 wienerCoord ℝ (E := ℝ)
  have hi (i j : ℕ) : wienerStructure.Γ (wienerX i) (wienerX j) =
      C ⟪(wienerX i : Lp ℝ 2 wienerCoord), (wienerX j : Lp ℝ 2 wienerCoord)⟫_ℝ := by
    rw [wienerStructure_Γ_coordinate]
    change Lp.const 1 wienerCoord _ = C ⟪wienerCoordinate i, wienerCoordinate j⟫_ℝ
    rw [wienerCoordinate_eq_gaussianCoordinate, wienerCoordinate_eq_gaussianCoordinate,
      orthonormal_iff_ite.mp Foundations.orthonormal_gaussianCoordinate]
    rfl
  change _ = C _
  simp only [wienerFirstSum, Submodule.coe_sum, Submodule.coe_smul,
    sum_inner, inner_sum, real_inner_smul_left, inner_smul_right,
    map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hi]
  simp only [← map_sum, ← map_smul, smul_eq_mul]

theorem wienerFirstSum_energy (s t : Finset ℕ) (a b : ℕ → ℝ) :
    wienerStructure.energy.E (wienerFirstSum s a) (wienerFirstSum t b) =
      (1/2 : ℝ) * ⟪(wienerFirstSum s a : Lp ℝ 2 wienerCoord),
        (wienerFirstSum t b : Lp ℝ 2 wienerCoord)⟫_ℝ := by
  rw [ErrorData.energy_apply, wienerFirstSum_Γ]
  rw [integral_congr_ae (Lp.coeFn_const _ _ _)]
  simp

theorem wienerFirstSum_energy_sub (s t : Finset ℕ) (a b : ℕ → ℝ) :
    wienerStructure.energy.E (wienerFirstSum s a - wienerFirstSum t b)
      (wienerFirstSum s a - wienerFirstSum t b) =
      (1/2 : ℝ) * ‖(wienerFirstSum s a : Lp ℝ 2 wienerCoord) -
        (wienerFirstSum t b : Lp ℝ 2 wienerCoord)‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [map_sub, LinearMap.sub_apply, wienerFirstSum_energy,
    inner_sub_left, inner_sub_right]
  ring

theorem wienerFirstSum_tendsto (a : Foundations.CameronMartinSpace) :
    Tendsto (fun n => (wienerFirstSum (Finset.range n) a : Lp ℝ 2 wienerCoord))
      atTop (𝓝 (Foundations.wienerIntegral a)) := by
  simpa only [coe_wienerFirstSum] using Foundations.tendsto_wienerPartial a

/-- The L²-Cauchy first-chaos sums are also Cauchy in energy. -/
theorem wienerFirstSum_isCauchy (a : Foundations.CameronMartinSpace) :
    wienerStructure.energy.IsCauchy (fun n => wienerFirstSum (Finset.range n) a) := by
  rw [wienerStructure.energy.isCauchy_iff]
  have hc := (wienerFirstSum_tendsto a).cauchySeq
  refine ⟨hc, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  have h := hN m hm n hn
  rw [dist_eq_norm] at h
  change Real.sqrt (wienerStructure.energy.E _ _) < ε
  rw [wienerFirstSum_energy_sub]
  apply lt_of_le_of_lt _ h
  calc
    _ ≤ Real.sqrt (‖(wienerFirstSum (Finset.range m) a : Lp ℝ 2 wienerCoord) -
        (wienerFirstSum (Finset.range n) a : Lp ℝ 2 wienerCoord)‖^2) :=
      Real.sqrt_le_sqrt (by
        nlinarith [sq_nonneg ‖(wienerFirstSum (Finset.range m) a : Lp ℝ 2 wienerCoord) -
          (wienerFirstSum (Finset.range n) a : Lp ℝ 2 wienerCoord)‖])
    _ = _ := Real.sqrt_sq (norm_nonneg _)

/-- closedness places every deterministic Wiener integral in the domain. -/
theorem wienerIntegral_mem_wienerStructure_dom (a : Foundations.CameronMartinSpace) :
    Foundations.wienerIntegral a ∈ wienerStructure.dom :=
  (wienerStructure.energy_closed _ (wienerFirstSum_isCauchy a) _
    (wienerFirstSum_tendsto a)).choose

def wienerIntegralDom (a : Foundations.CameronMartinSpace) : wienerStructure.dom :=
  ⟨Foundations.wienerIntegral a, wienerIntegral_mem_wienerStructure_dom a⟩

/-- Γ is the constant Cameron--Martin scalar product. -/
theorem wienerStructure_Γ_wienerIntegral (a b : Foundations.CameronMartinSpace) :
    wienerStructure.Γ (wienerIntegralDom a) (wienerIntegralDom b) =
      Lp.const 1 wienerCoord ⟪a,b⟫_ℝ := by
  have h := wienerStructure.toErrorData.gamma_characterization
    (wienerStructure.energy_closed.isClosable _)
    (v := wienerIntegralDom a) (z := wienerIntegralDom b)
    ⟨wienerFirstSum_isCauchy a, wienerFirstSum_tendsto a⟩
    ⟨wienerFirstSum_isCauchy b, wienerFirstSum_tendsto b⟩
  have ht := (Lp.constL 1 wienerCoord ℝ (E := ℝ)).continuous.continuousAt.tendsto.comp
    ((wienerFirstSum_tendsto a).inner (𝕜 := ℝ) (wienerFirstSum_tendsto b))
  simp only [Lp.constL_apply, Foundations.wienerIntegral.inner_map_map] at ht
  simp only [wienerFirstSum_Γ] at h
  exact tendsto_nhds_unique h ht

theorem wienerStructure_energy_wienerIntegral (a b : Foundations.CameronMartinSpace) :
    wienerStructure.energy.E (wienerIntegralDom a) (wienerIntegralDom b) =
      (1/2 : ℝ) * ⟪a,b⟫_ℝ := by
  rw [ErrorData.energy_apply, wienerStructure_Γ_wienerIntegral,
    integral_congr_ae (Lp.coeFn_const _ _ _)]
  simp

end ErrorCalculus
