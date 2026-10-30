import ErrorCalculus.Dirichlet.ResolventEquation
import Foundations.Semigroup.Resolvent

noncomputable section
open Filter Topology
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (Q : QuadForm H) (hQ : Q.IsClosed) (hd : Dense (Q.dom : Set H))

/-- resolvent, extended by zero outside positive parameters. -/
def formResolvent : Foundations.ContractionResolvent H where
  G b := if hb : 0 < b then Q.resolvent hQ b hb else 0
  resolvent_eq := by
    intro a b ha hb
    ext x
    simpa only [dif_pos ha, dif_pos hb, sub_apply,
      smul_apply, mul_apply_eq_comp] using
      Q.resolvent_eq_apply hQ a b ha hb x
  norm_le := by
    intro b hb
    simpa only [dif_pos hb] using Q.norm_beta_resolvent_op_le hQ b hb
  tendsto_id := by
    intro x
    have ht : Tendsto (fun b : ℝ => max b 1) atTop atTop :=
      tendsto_atTop_mono (fun b => le_max_left b 1) tendsto_id
    have hh := Q.tendsto_beta_resolvent hQ hd (fun b : ℝ => max b 1)
      (fun b => lt_of_lt_of_le zero_lt_one (le_max_right b 1)) ht x
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with b hb
    simp [max_eq_left hb.le, dif_pos (show 0 < b by linarith)]

@[simp] theorem formResolvent_G {b : ℝ} (hb : 0 < b) :
    (Q.formResolvent hQ hd).G b = Q.resolvent hQ b hb := by
  simp [formResolvent, hb]

/-- The common generator domain is the range at any positive parameter. -/
theorem formResolvent_dom {b : ℝ} (hb : 0 < b) :
    (Q.formResolvent hQ hd).dom = LinearMap.range (Q.resolvent hQ b hb).toLinearMap := by
  rw [Foundations.ContractionResolvent.dom,
    (Q.formResolvent hQ hd).range_eq zero_lt_one hb, Q.formResolvent_G hQ hd hb]

/-- Every generator-domain vector belongs to the form domain. -/
theorem formResolvent_dom_le : (Q.formResolvent hQ hd).dom ≤ Q.dom := by
  rw [Q.formResolvent_dom hQ hd zero_lt_one]
  rintro x ⟨y, rfl⟩
  exact (Q.resolventDom hQ 1 zero_lt_one y).property

theorem formResolvent_dense_dom : Dense ((Q.formResolvent hQ hd).dom : Set H) :=
  (Q.formResolvent hQ hd).dense_dom

end ErrorCalculus.QuadForm
