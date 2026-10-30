import ErrorCalculus.Dirichlet.SemigroupBasic

noncomputable section
open Filter Topology
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (Q : QuadForm H) (hQ : Q.IsClosed) (hd : Dense (Q.dom : Set H))

/-- The form agrees with minus its generator on the generator domain. -/
theorem energy_eq_neg_inner_generator (u : (Q.formResolvent hQ hd).dom) (v : Q.dom) :
    Q.E ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩ v =
      -inner ℝ ((Q.formResolvent hQ hd).generator u) (v : H) := by
  let f := (u : H) - (Q.formResolvent hQ hd).generator u
  have hu : Q.resolvent hQ 1 zero_lt_one f = (u : H) := by
    simpa only [Q.formResolvent_G hQ hd zero_lt_one, one_smul] using
      (Q.formResolvent hQ hd).G_generator zero_lt_one u
  have hu' : Q.resolventDom hQ 1 zero_lt_one f =
      ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩ := Subtype.ext hu
  have he := Q.resolvent_spec hQ 1 zero_lt_one f v
  rw [hu', hu] at he
  simp only [f, inner_sub_left, one_mul] at he
  linarith

/-- The semigroup energy quotient tends to the energy on D(A). -/
theorem tendsto_energy_approx_generator (u : (Q.formResolvent hQ hd).dom) :
    Tendsto (fun t : ℝ => (1/t) * inner ℝ ((u : H) - Q.semigroup hQ hd t u) (u : H))
      (𝓝[>] 0)
      (𝓝 (Q.E ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩
        ⟨u, Q.formResolvent_dom_le hQ hd u.property⟩)) := by
  rw [Q.energy_eq_neg_inner_generator hQ hd]
  have hh := ((Q.tendsto_semigroup_sub_div hQ hd u).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := (u : H)))).neg
  simpa only [real_inner_smul_left, inner_sub_left, one_div, mul_sub, neg_sub] using hh

end ErrorCalculus.QuadForm
