import ErrorCalculus.Dirichlet.Closure

noncomputable section
open Filter Topology
namespace ErrorCalculus.QuadForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (Q R S : QuadForm H)

/-- extension means domain inclusion and equality on the original domain. -/
structure Extends : Prop where
  dom_le : Q.dom ≤ R.dom
  energy_eq : ∀ u v : Q.dom,
    R.E (Submodule.inclusion dom_le u) (Submodule.inclusion dom_le v) = Q.E u v

/-- The closure extends the original form. -/
theorem closure_extends (h : Q.IsClosable) : Q.Extends (Q.closure h) := by
  refine ⟨Q.le_closureDom, ?_⟩
  intro u v
  change inner ℝ (Q.closureLift h (Q.inclusion u)) (Q.closureLift h (Q.inclusion v)) = _
  simp

/-- extension preserves form-Cauchy sequences. -/
theorem Extends.isCauchy (h : Q.Extends R) {u : ℕ → Q.dom} (hu : Q.IsCauchy u) :
    R.IsCauchy (fun n => Submodule.inclusion h.dom_le (u n)) := by
  rw [R.isCauchy_iff]
  refine ⟨hu.1, ?_⟩
  have hc := (Q.isCauchy_iff u).mp hu |>.2
  simpa only [seminorm, ← map_sub, h.energy_eq] using hc

/-- restriction of a closable form is closable. -/
theorem Extends.isClosable (h : Q.Extends R) (hR : R.IsClosable) : Q.IsClosable := by
  intro u hu hv
  simpa only [h.energy_eq] using hR (fun n => Submodule.inclusion h.dom_le (u n))
    (h.isCauchy Q R hu) hv

/-- Every closed extension contains the closure domain. -/
theorem closureDom_le (hR : R.IsClosed) (hQR : Q.Extends R) : Q.closureDom ≤ R.dom := by
  intro v hv
  obtain ⟨u, hu⟩ := (Q.mem_closureDom_iff v).mp hv
  exact (hR _ (hQR.isCauchy Q R hu.1) v hu.2).choose

/-- a closed form identifies all ambient limits of form-Cauchy sequences. -/
theorem IsClosed.energy_limit (hR : R.IsClosed) {u w : ℕ → R.dom} {v z : R.dom}
    (hu : R.Approaches u v) (hw : R.Approaches w z) :
    Tendsto (fun n => R.E (u n) (w n)) atTop (𝓝 (R.E v z)) := by
  obtain ⟨hv, hvE⟩ := hR u hu.1 v hu.2
  obtain ⟨hz, hzE⟩ := hR w hw.1 z hw.2
  have hvj := (R.energy_tendsto_zero_iff).mp hvE
  have hzj := (R.energy_tendsto_zero_iff).mp hzE
  have hv' : Tendsto (fun n => R.j (u n)) atTop (𝓝 (R.j v)) := by
    have ht := hvj.add_const (R.j v)
    simpa only [map_sub, sub_add_cancel, zero_add] using ht
  have hz' : Tendsto (fun n => R.j (w n)) atTop (𝓝 (R.j z)) := by
    have ht := hzj.add_const (R.j z)
    simpa only [map_sub, sub_add_cancel, zero_add] using ht
  simpa only [R.inner_j] using hv'.inner (𝕜 := ℝ) hz'

/-- The closure is the smallest closed extension. -/
theorem closure_minimal (h : Q.IsClosable) (hR : R.IsClosed) (hQR : Q.Extends R) :
    (Q.closure h).Extends R := by
  refine ⟨Q.closureDom_le R hR hQR, ?_⟩
  intro v z
  obtain ⟨u, hu⟩ := (Q.mem_closureDom_iff v).mp v.property
  obtain ⟨w, hw⟩ := (Q.mem_closureDom_iff z).mp z.property
  have ht := Q.closure_characterization h hu hw v.property z.property
  have hr := hR.energy_limit R
    (v := Submodule.inclusion (Q.closureDom_le R hR hQR) v)
    (z := Submodule.inclusion (Q.closureDom_le R hR hQR) z)
    (u := fun n => Submodule.inclusion hQR.dom_le (u n))
    (w := fun n => Submodule.inclusion hQR.dom_le (w n))
    ⟨hQR.isCauchy Q R hu.1, hu.2⟩ ⟨hQR.isCauchy Q R hw.1, hw.2⟩
  simp only [hQR.energy_eq] at hr
  exact tendsto_nhds_unique hr ht

/-- closability is exactly existence of a closed extension. -/
theorem isClosable_iff_exists_closed_extension : Q.IsClosable ↔ ∃ R : QuadForm H,
    R.IsClosed ∧ Q.Extends R := by
  constructor
  · intro h
    exact ⟨Q.closure h, Q.closure_isClosed h, Q.closure_extends h⟩
  · rintro ⟨R, hR, hQR⟩
    exact hQR.isClosable Q R (hR.isClosable R)

/-- two forms extending each other are equal. -/
theorem Extends.antisymm (hQR : Q.Extends R) (hRQ : R.Extends Q) : Q = R := by
  have hd := le_antisymm hQR.dom_le hRQ.dom_le
  cases Q with
  | mk D E symm nonneg =>
    cases R with
    | mk D' E' symm' nonneg' =>
      dsimp at hd
      subst D'
      have he : E = E' := by
        ext u v
        exact (hQR.energy_eq u v).symm
      subst E'
      rfl

/-- uniqueness of the least closed extension. -/
theorem closure_unique (h : Q.IsClosable) (hR : R.IsClosed) (hQR : Q.Extends R)
    (hmin : ∀ S : QuadForm H, S.IsClosed → Q.Extends S → R.Extends S) :
    R = Q.closure h :=
  Extends.antisymm R (Q.closure h) (hmin _ (Q.closure_isClosed h) (Q.closure_extends h))
    (Q.closure_minimal R h hR hQR)

end ErrorCalculus.QuadForm
