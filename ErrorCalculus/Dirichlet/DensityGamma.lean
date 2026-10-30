import ErrorCalculus.Dirichlet.DensityBasic

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
set_option linter.unusedSectionVars false
namespace ErrorCalculus

/-- A C¹ test function and its derivative are bounded. -/
theorem isC1Bounded_of_hasCompactSupport {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) : IsC1Bounded g :=
  ⟨hg, hc.exists_bound_of_continuous hg.continuous,
    hc.deriv.exists_bound_of_continuous (hg.continuous_deriv (by norm_num))⟩

variable (ρ : ℝ → ℝ) [IsProbabilityMeasure (densityMeasure ρ)]

/-- Canonical inclusion of an ordinary bounded C¹ function in the domain. -/
def protoOfFunction (g : ℝ → ℝ) (hg : IsC1Bounded g) : protoDom ρ :=
  ⟨(hg.memLp (densityMeasure ρ) 2).toLp g, g, hg, MemLp.coeFn_toLp _⟩

theorem dense_protoDom : Dense (protoDom ρ : Set (Lp ℝ 2 (densityMeasure ρ))) := by
  apply (Lp.dense_hasCompactSupport_contDiff (μ := densityMeasure ρ) (E := ℝ) (F := ℝ)
    (p := 2) (by norm_num)).mono
  rintro u ⟨g, hu, hc, hg⟩
  exact ⟨g, isC1Bounded_of_hasCompactSupport (hg.of_le (by simp)) hc, hu⟩

theorem const_mem_protoDom (c : ℝ) : Lp.const 2 (densityMeasure ρ) c ∈ protoDom ρ :=
  ⟨fun _ => c, IsC1Bounded.const c, Lp.coeFn_const _ _ _⟩

variable [SmoothDensity ρ]

theorem rep_protoOfFunction (g : ℝ → ℝ) (hg : IsC1Bounded g) :
    rep ρ (protoOfFunction ρ g hg) = g :=
  rep_unique ρ _ hg.1.continuous (hg.memLp (densityMeasure ρ) 2).coeFn_toLp

theorem derivRep_const (c : ℝ) : derivRep ρ ⟨Lp.const 2 (densityMeasure ρ) c, const_mem_protoDom ρ c⟩ = 0 := by
  change deriv (rep ρ _) = 0
  rw [rep_unique ρ _ continuous_const (Lp.coeFn_const _ _ _)]
  funext x
  exact deriv_const x c

theorem derivRep_memLp (u : protoDom ρ) : MemLp (derivRep ρ u) 2 (densityMeasure ρ) :=
  (rep_isC1Bounded ρ u).deriv_memLp (densityMeasure ρ) 2

/-- The carré du champ before bundling bilinearity. -/
def gammaValue (u v : protoDom ρ) : Lp ℝ 1 (densityMeasure ρ) :=
  ((derivRep_memLp ρ v).mul (derivRep_memLp ρ u)).toLp (fun x => derivRep ρ u x * derivRep ρ v x)

theorem coeFn_gammaValue (u v : protoDom ρ) :
    ⇑(gammaValue ρ u v) =ᵐ[densityMeasure ρ] fun x => derivRep ρ u x * derivRep ρ v x :=
  ((derivRep_memLp ρ v).mul (derivRep_memLp ρ u)).coeFn_toLp

theorem gammaValue_symm (u v : protoDom ρ) : gammaValue ρ u v = gammaValue ρ v u := by
  apply Lp.ext
  filter_upwards [coeFn_gammaValue ρ u v, coeFn_gammaValue ρ v u] with x h h'
  rw [h, h', mul_comm]

theorem gammaValue_add_right (u v w : protoDom ρ) :
    gammaValue ρ u (v + w) = gammaValue ρ u v + gammaValue ρ u w := by
  apply Lp.ext
  filter_upwards [coeFn_gammaValue ρ u (v+w), coeFn_gammaValue ρ u v,
    coeFn_gammaValue ρ u w, Lp.coeFn_add (gammaValue ρ u v) (gammaValue ρ u w)] with x h h' h'' ha
  simp only [Pi.add_apply] at ha
  rw [h, ha, h', h'', map_add, Pi.add_apply, mul_add]

theorem gammaValue_smul_right (c : ℝ) (u v : protoDom ρ) :
    gammaValue ρ u (c • v) = c • gammaValue ρ u v := by
  apply Lp.ext
  filter_upwards [coeFn_gammaValue ρ u (c • v), coeFn_gammaValue ρ u v,
    Lp.coeFn_smul c (gammaValue ρ u v)] with x h h' hs
  simp only [Pi.smul_apply] at hs
  rw [h, hs, h', map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The symmetric bilinear carré du champ Γ₀[u,v]=u'v'. -/
def gamma₀ : protoDom ρ →ₗ[ℝ] protoDom ρ →ₗ[ℝ] Lp ℝ 1 (densityMeasure ρ) where
  toFun u :=
    { toFun := gammaValue ρ u
      map_add' := gammaValue_add_right ρ u
      map_smul' := fun c v => gammaValue_smul_right ρ c u v }
  map_add' u v := by
    ext w : 1
    change gammaValue ρ (u+v) w = gammaValue ρ u w + gammaValue ρ v w
    rw [gammaValue_symm ρ (u+v), gammaValue_add_right]
    rw [gammaValue_symm ρ w u, gammaValue_symm ρ w v]
  map_smul' c u := by
    ext v : 1
    change gammaValue ρ (c • u) v = c • gammaValue ρ u v
    rw [gammaValue_symm ρ (c • u), gammaValue_smul_right, gammaValue_symm ρ v u]

theorem coeFn_gamma₀ (u v : protoDom ρ) :
    ⇑(gamma₀ ρ u v) =ᵐ[densityMeasure ρ] fun x => deriv (rep ρ u) x * deriv (rep ρ v) x :=
  coeFn_gammaValue ρ u v

/-- The pre-domain data; closedness has not been assumed. -/
def protoData : ErrorData ℝ (densityMeasure ρ) where
  dom := protoDom ρ
  Γ := gamma₀ ρ
  Γ_symm := gammaValue_symm ρ
  Γ_nonneg u := by
    filter_upwards [coeFn_gamma₀ ρ u u] with x hx
    rw [hx]
    exact mul_self_nonneg _

def protoForm : QuadForm (Lp ℝ 2 (densityMeasure ρ)) := (protoData ρ).energy

/-- The proto-form energy equals one half of the L² inner product of the gradients. -/
theorem protoForm_eq_inner_grad (u v : protoDom ρ) :
    (protoForm ρ).E u v = (1/2:ℝ) * inner ℝ (grad ρ u) (grad ρ v) := by
  change (1/2:ℝ) * (∫ x, gamma₀ ρ u v x ∂densityMeasure ρ) = _
  rw [L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [coeFn_gamma₀ ρ u v, coeFn_grad ρ u, coeFn_grad ρ v] with x h hu hv
  rw [h, hu, hv, real_inner_comm]
  rfl

theorem protoForm_eq_grad (u : protoDom ρ) :
    (protoForm ρ).E u u = (1/2:ℝ) * ‖grad ρ u‖ ^ 2 := by
  rw [protoForm_eq_inner_grad, real_inner_self_eq_norm_sq]

/-- Constants carry no error. -/
theorem gamma₀_const (c : ℝ) (v : protoDom ρ) :
    gamma₀ ρ ⟨Lp.const 2 (densityMeasure ρ) c, const_mem_protoDom ρ c⟩ v = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_gammaValue ρ ⟨_, const_mem_protoDom ρ c⟩ v,
    Lp.coeFn_zero ℝ 1 (densityMeasure ρ)] with x h hz
  change gammaValue ρ _ _ x = _
  rw [h, derivRep_const, Pi.zero_apply, zero_mul, hz]
  rfl

end ErrorCalculus
