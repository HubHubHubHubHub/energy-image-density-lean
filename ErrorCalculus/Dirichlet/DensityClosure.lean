import ErrorCalculus.Dirichlet.DensityIBP
import ErrorCalculus.Dirichlet.Extension

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
namespace ErrorCalculus
variable (ρ : ℝ → ℝ) [SmoothDensity ρ] [IsProbabilityMeasure (densityMeasure ρ)]

/-- The energy seminorm controls differences of gradients. -/
theorem grad_norm_le_seminorm (u : protoDom ρ) :
    ‖grad ρ u‖ ≤ 2 * (protoForm ρ).seminorm u := by
  have hs : (protoForm ρ).seminorm u ^ 2 = (1/2:ℝ) * ‖grad ρ u‖ ^ 2 :=
    (Real.sq_sqrt ((protoForm ρ).nonneg u)).trans (protoForm_eq_grad ρ u)
  have hn : 0 ≤ (protoForm ρ).seminorm u := Real.sqrt_nonneg _
  nlinarith [norm_nonneg (grad ρ u)]

/-- X.3(1): form-Cauchy sequences have Cauchy gradients in L². -/
theorem cauchySeq_grad {u : ℕ → protoDom ρ} (hu : (protoForm ρ).IsCauchy u) :
    CauchySeq (fun n => grad ρ (u n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := ((protoForm ρ).isCauchy_iff u).mp hu |>.2 (ε/2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm, ← map_sub]
  calc
    _ ≤ 2 * (protoForm ρ).seminorm (u m-u n) := grad_norm_le_seminorm ρ _
    _ < 2 * (ε/2) := mul_lt_mul_of_pos_left (hN m hm n hn) (by norm_num)
    _ = ε := by ring

/-- X.3(2)-(3): integration by parts and the dense smooth test set identify the limit. -/
theorem gradient_limit_zero {u : ℕ → protoDom ρ} {w : Lp ℝ 2 (densityMeasure ρ)}
    (hu : Tendsto (fun n => (u n : Lp ℝ 2 (densityMeasure ρ))) atTop (𝓝 0))
    (hw : Tendsto (fun n => grad ρ (u n)) atTop (𝓝 w)) : w = 0 := by
  apply (Lp.dense_hasCompactSupport_contDiff (μ := densityMeasure ρ) (E := ℝ) (F := ℝ)
    (p := 2) (by norm_num)).eq_zero_of_inner_left ℝ
  rintro v ⟨φ, hv, hc, hφ⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  let t := protoOfFunction ρ φ (isC1Bounded_of_hasCompactSupport hφ1 hc)
  have ht : (t : Lp ℝ 2 (densityMeasure ρ)) = v :=
    Lp.ext (((isC1Bounded_of_hasCompactSupport hφ1 hc).memLp (densityMeasure ρ) 2).coeFn_toLp.trans hv.symm)
  have hleft := hw.inner (𝕜 := ℝ) (tendsto_const_nhds (x := v))
  have hright := (hu.inner (𝕜 := ℝ) (tendsto_const_nhds (x := testChiLp ρ φ hφ1 hc))).neg
  simp only [inner_zero_left, neg_zero] at hright
  have he : (fun n => inner ℝ (grad ρ (u n)) v) =
      fun n => - inner ℝ (u n : Lp ℝ 2 (densityMeasure ρ)) (testChiLp ρ φ hφ1 hc) := by
    funext n
    rw [← ht]
    exact inner_grad_test ρ (u n) hφ1 hc
  rw [← he] at hright
  exact tendsto_nhds_unique hleft hright

/-- The gradient energy on the actual C¹_b domain is closable. -/
theorem protoForm_isClosable : (protoForm ρ).IsClosable := by
  intro u hu h0
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (cauchySeq_grad ρ hu)
  have hz := gradient_limit_zero ρ h0 hw
  subst w
  have he := (hw.norm.pow 2).const_mul (1/2:ℝ)
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, protoForm_eq_grad] using he

/-- The density form, constructed by the closure theorem. -/
def dirichletForm : QuadForm (Lp ℝ 2 (densityMeasure ρ)) :=
  (protoForm ρ).closure (protoForm_isClosable ρ)

theorem dirichletForm_isClosed : (dirichletForm ρ).IsClosed :=
  (protoForm ρ).closure_isClosed (protoForm_isClosable ρ)

theorem dirichletForm_extends : (protoForm ρ).Extends (dirichletForm ρ) :=
  (protoForm ρ).closure_extends (protoForm_isClosable ρ)

theorem dense_dirichletForm_dom : Dense ((dirichletForm ρ).dom : Set (Lp ℝ 2 (densityMeasure ρ))) :=
  (dense_protoDom ρ).mono (dirichletForm_extends ρ).dom_le

theorem dirichletForm_minimal (R : QuadForm (Lp ℝ 2 (densityMeasure ρ)))
    (hR : R.IsClosed) (he : (protoForm ρ).Extends R) : (dirichletForm ρ).Extends R :=
  (protoForm ρ).closure_minimal R (protoForm_isClosable ρ) hR he

end ErrorCalculus
