import ErrorCalculus.Dirichlet.DensityDIBP
import ErrorCalculus.Dirichlet.Extension

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
namespace ErrorCalculus
variable {d : ℕ}
variable (ρ : (Fin d → ℝ) → ℝ) [SmoothDensityD ρ] [IsProbabilityMeasure (densityMeasureD ρ)]

/-- The energy seminorm controls differences of gradients. -/
theorem grad_norm_le_seminormD (i : Fin d) (u : protoDomD ρ) :
    ‖gradD ρ i u‖ ≤ 2 * (protoFormD ρ).seminorm u := by
  have hs : (protoFormD ρ).seminorm u ^ 2 = (1/2:ℝ) * ∑ j, ‖gradD ρ j u‖ ^ 2 :=
    (Real.sq_sqrt ((protoFormD ρ).nonneg u)).trans (protoFormD_eq_grad ρ u)
  have hn : 0 ≤ (protoFormD ρ).seminorm u := Real.sqrt_nonneg _
  have hi : ‖gradD ρ i u‖ ^ 2 ≤ ∑ j, ‖gradD ρ j u‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖gradD ρ j u‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg (gradD ρ i u)]

/-- Y.3(1): form-Cauchy sequences have Cauchy gradients in L². -/
theorem cauchySeq_gradD (i : Fin d) {u : ℕ → protoDomD ρ} (hu : (protoFormD ρ).IsCauchy u) :
    CauchySeq (fun n => gradD ρ i (u n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := ((protoFormD ρ).isCauchy_iff u).mp hu |>.2 (ε/2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm, ← map_sub]
  calc
    _ ≤ 2 * (protoFormD ρ).seminorm (u m-u n) := grad_norm_le_seminormD ρ i _
    _ < 2 * (ε/2) := mul_lt_mul_of_pos_left (hN m hm n hn) (by norm_num)
    _ = ε := by ring

/-- Y.3(2)-(3): integration by parts and the dense smooth test set identify the limit. -/
theorem gradient_limit_zeroD (i : Fin d) {u : ℕ → protoDomD ρ} {w : Lp ℝ 2 (densityMeasureD ρ)}
    (hu : Tendsto (fun n => (u n : Lp ℝ 2 (densityMeasureD ρ))) atTop (𝓝 0))
    (hw : Tendsto (fun n => gradD ρ i (u n)) atTop (𝓝 w)) : w = 0 := by
  apply (Lp.dense_hasCompactSupport_contDiff (μ := densityMeasureD ρ) (E := Fin d → ℝ) (F := ℝ)
    (p := 2) (by norm_num)).eq_zero_of_inner_left ℝ
  rintro v ⟨φ, hv, hc, hφ⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  let t := protoOfFunctionD ρ φ (isC1Bounded_of_hasCompactSupportD hφ1 hc)
  have ht : (t : Lp ℝ 2 (densityMeasureD ρ)) = v :=
    Lp.ext (((isC1Bounded_of_hasCompactSupportD hφ1 hc).memLp (densityMeasureD ρ) 2).coeFn_toLp.trans hv.symm)
  have hleft := hw.inner (𝕜 := ℝ) (tendsto_const_nhds (x := v))
  have hright := (hu.inner (𝕜 := ℝ) (tendsto_const_nhds (x := testChiLpD ρ i φ hφ1 hc))).neg
  simp only [inner_zero_left, neg_zero] at hright
  have he : (fun n => inner ℝ (gradD ρ i (u n)) v) =
      fun n => - inner ℝ (u n : Lp ℝ 2 (densityMeasureD ρ)) (testChiLpD ρ i φ hφ1 hc) := by
    funext n
    rw [← ht]
    exact inner_gradD_test ρ i (u n) hφ1 hc
  rw [← he] at hright
  exact tendsto_nhds_unique hleft hright

/-- The gradient energy on the actual C¹_b domain is closable. -/
theorem protoFormD_isClosable : (protoFormD ρ).IsClosable := by
  intro u hu h0
  have hi : ∀ i, Tendsto (fun n => gradD ρ i (u n)) atTop (𝓝 0) := by
    intro i
    obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (cauchySeq_gradD ρ i hu)
    rwa [gradient_limit_zeroD ρ i h0 hw] at hw
  have he : Tendsto (fun n => (1/2:ℝ) * ∑ i, ‖gradD ρ i (u n)‖ ^ 2) atTop (𝓝 0) := by
    have hs := tendsto_finsetSum Finset.univ (fun i _ => (hi i).norm.pow 2)
    simpa using hs.const_mul (1/2:ℝ)
  simpa only [protoFormD_eq_grad] using he

/-- The density form, constructed by the closure theorem. -/
def dirichletFormD : QuadForm (Lp ℝ 2 (densityMeasureD ρ)) :=
  (protoFormD ρ).closure (protoFormD_isClosable ρ)

theorem dirichletForm_isClosedD : (dirichletFormD ρ).IsClosed :=
  (protoFormD ρ).closure_isClosed (protoFormD_isClosable ρ)

theorem dirichletForm_extendsD : (protoFormD ρ).Extends (dirichletFormD ρ) :=
  (protoFormD ρ).closure_extends (protoFormD_isClosable ρ)

theorem dense_dirichletForm_domD : Dense ((dirichletFormD ρ).dom : Set (Lp ℝ 2 (densityMeasureD ρ))) :=
  (dense_protoDomD ρ).mono (dirichletForm_extendsD ρ).dom_le

theorem dirichletForm_minimalD (R : QuadForm (Lp ℝ 2 (densityMeasureD ρ)))
    (hR : R.IsClosed) (he : (protoFormD ρ).Extends R) : (dirichletFormD ρ).Extends R :=
  (protoFormD ρ).closure_minimal R (protoFormD_isClosable ρ) hR he

end ErrorCalculus
