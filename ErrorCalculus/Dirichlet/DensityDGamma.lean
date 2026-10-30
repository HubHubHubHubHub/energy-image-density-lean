import ErrorCalculus.Dirichlet.DensityDBasic

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
set_option linter.unusedSectionVars false

namespace ErrorCalculus
variable {d : ℕ}

/-- A compactly supported C¹ function and its differential are bounded. -/
theorem isC1Bounded_of_hasCompactSupportD {g : (Fin d → ℝ) → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) : IsC1BoundedD g :=
  ⟨hg, hc.exists_bound_of_continuous hg.continuous,
    (hc.fderiv ℝ).exists_bound_of_continuous (hg.continuous_fderiv (by norm_num))⟩

variable (ρ : (Fin d → ℝ) → ℝ) [IsProbabilityMeasure (densityMeasureD ρ)]

/-- Canonical inclusion of an ordinary bounded C¹ function in the domain. -/
def protoOfFunctionD (g : (Fin d → ℝ) → ℝ) (hg : IsC1BoundedD g) : protoDomD ρ :=
  ⟨(hg.memLp (densityMeasureD ρ) 2).toLp g, g, hg, MemLp.coeFn_toLp _⟩

theorem dense_protoDomD : Dense (protoDomD ρ : Set (Lp ℝ 2 (densityMeasureD ρ))) := by
  apply (Lp.dense_hasCompactSupport_contDiff (μ := densityMeasureD ρ) (E := Fin d → ℝ) (F := ℝ)
    (p := 2) (by norm_num)).mono
  rintro u ⟨g, hu, hc, hg⟩
  exact ⟨g, isC1Bounded_of_hasCompactSupportD (hg.of_le (by simp)) hc, hu⟩

theorem const_mem_protoDomD (c : ℝ) : Lp.const 2 (densityMeasureD ρ) c ∈ protoDomD ρ :=
  ⟨fun _ => c, IsC1BoundedD.const c, Lp.coeFn_const _ _ _⟩

variable [SmoothDensityD ρ]

theorem rep_protoOfFunctionD (g : (Fin d → ℝ) → ℝ) (hg : IsC1BoundedD g) :
    repD ρ (protoOfFunctionD ρ g hg) = g :=
  rep_uniqueD ρ _ hg.1.continuous (hg.memLp (densityMeasureD ρ) 2).coeFn_toLp

theorem partialRep_const (i : Fin d) (c : ℝ) :
    partialRep ρ i ⟨Lp.const 2 (densityMeasureD ρ) c, const_mem_protoDomD ρ c⟩ = 0 := by
  change (fun x => fderiv ℝ (repD ρ _) x (Pi.single i 1)) = 0
  rw [rep_uniqueD ρ _ continuous_const (Lp.coeFn_const _ _ _)]
  simp
  rfl

theorem partialRep_memLp (i : Fin d) (u : protoDomD ρ) :
    MemLp (partialRep ρ i u) 2 (densityMeasureD ρ) :=
  (rep_isC1BoundedD ρ u).partial_memLp i (densityMeasureD ρ) 2

theorem gammaD_memLp (u v : protoDomD ρ) :
    MemLp (fun x => ∑ i, partialRep ρ i u x * partialRep ρ i v x) 1 (densityMeasureD ρ) := by
  apply memLp_finsetSum
  intro i _
  exact (partialRep_memLp ρ i v).mul (partialRep_memLp ρ i u)

/-- The carré du champ before bundling bilinearity. -/
def gammaValueD (u v : protoDomD ρ) : Lp ℝ 1 (densityMeasureD ρ) :=
  (gammaD_memLp ρ u v).toLp (fun x => ∑ i, partialRep ρ i u x * partialRep ρ i v x)

theorem coeFn_gammaValueD (u v : protoDomD ρ) :
    ⇑(gammaValueD ρ u v) =ᵐ[densityMeasureD ρ] fun x => ∑ i, partialRep ρ i u x * partialRep ρ i v x :=
  (gammaD_memLp ρ u v).coeFn_toLp

theorem gammaValue_symmD (u v : protoDomD ρ) : gammaValueD ρ u v = gammaValueD ρ v u := by
  apply Lp.ext
  filter_upwards [coeFn_gammaValueD ρ u v, coeFn_gammaValueD ρ v u] with x h h'
  simp only [h, h', mul_comm]

theorem gammaValue_add_rightD (u v w : protoDomD ρ) :
    gammaValueD ρ u (v + w) = gammaValueD ρ u v + gammaValueD ρ u w := by
  apply Lp.ext
  filter_upwards [coeFn_gammaValueD ρ u (v+w), coeFn_gammaValueD ρ u v,
    coeFn_gammaValueD ρ u w, Lp.coeFn_add (gammaValueD ρ u v) (gammaValueD ρ u w)] with x h h' h'' ha
  simp only [Pi.add_apply] at ha
  simp only [h, ha, h', h'', map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem gammaValue_smul_rightD (c : ℝ) (u v : protoDomD ρ) :
    gammaValueD ρ u (c • v) = c • gammaValueD ρ u v := by
  apply Lp.ext
  filter_upwards [coeFn_gammaValueD ρ u (c • v), coeFn_gammaValueD ρ u v,
    Lp.coeFn_smul c (gammaValueD ρ u v)] with x h h' hs
  simp only [Pi.smul_apply] at hs
  simp only [h, hs, h', map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The symmetric bilinear carré du champ is the sum of products of partials. -/
def gammaD : protoDomD ρ →ₗ[ℝ] protoDomD ρ →ₗ[ℝ] Lp ℝ 1 (densityMeasureD ρ) where
  toFun u :=
    { toFun := gammaValueD ρ u
      map_add' := gammaValue_add_rightD ρ u
      map_smul' := fun c v => gammaValue_smul_rightD ρ c u v }
  map_add' u v := by
    ext w : 1
    change gammaValueD ρ (u+v) w = gammaValueD ρ u w + gammaValueD ρ v w
    rw [gammaValue_symmD ρ (u+v), gammaValue_add_rightD]
    rw [gammaValue_symmD ρ w u, gammaValue_symmD ρ w v]
  map_smul' c u := by
    ext v : 1
    change gammaValueD ρ (c • u) v = c • gammaValueD ρ u v
    rw [gammaValue_symmD ρ (c • u), gammaValue_smul_rightD, gammaValue_symmD ρ v u]

theorem coeFn_gammaD (u v : protoDomD ρ) :
    ⇑(gammaD ρ u v) =ᵐ[densityMeasureD ρ] fun x =>
      ∑ i, fderiv ℝ (repD ρ u) x (Pi.single i 1) * fderiv ℝ (repD ρ v) x (Pi.single i 1) :=
  coeFn_gammaValueD ρ u v

/-- The pre-domain data; closedness has not been assumed. -/
def protoDataD : ErrorData (Fin d → ℝ) (densityMeasureD ρ) where
  dom := protoDomD ρ
  Γ := gammaD ρ
  Γ_symm := gammaValue_symmD ρ
  Γ_nonneg u := by
    filter_upwards [coeFn_gammaD ρ u u] with x hx
    rw [hx]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

def protoFormD : QuadForm (Lp ℝ 2 (densityMeasureD ρ)) := (protoDataD ρ).energy

/-- energy is the sum of the coordinate gradient inner products. -/
theorem protoForm_eq_inner_gradD (u v : protoDomD ρ) :
    (protoFormD ρ).E u v = (1/2:ℝ) * ∑ i, inner ℝ (gradD ρ i u) (gradD ρ i v) := by
  change (1/2:ℝ) * (∫ x, gammaD ρ u v x ∂densityMeasureD ρ) = _
  congr 1
  change (∫ x, gammaValueD ρ u v x ∂densityMeasureD ρ) = _
  rw [integral_congr_ae (coeFn_gammaValueD ρ u v)]
  have hi : ∀ i : Fin d, Integrable (fun x => partialRep ρ i u x * partialRep ρ i v x) (densityMeasureD ρ) := by
    intro i
    exact (partialRep_memLp ρ i u).integrable_mul (partialRep_memLp ρ i v)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_gradD ρ i u, coeFn_gradD ρ i v] with x hu hv
  rw [hu, hv, real_inner_comm]
  rfl

theorem protoFormD_eq_grad (u : protoDomD ρ) :
    (protoFormD ρ).E u u = (1/2:ℝ) * ∑ i, ‖gradD ρ i u‖ ^ 2 := by
  simp only [protoForm_eq_inner_gradD, real_inner_self_eq_norm_sq]

/-- Constants carry no error. -/
theorem gammaD_const (c : ℝ) (v : protoDomD ρ) :
    gammaD ρ ⟨Lp.const 2 (densityMeasureD ρ) c, const_mem_protoDomD ρ c⟩ v = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_gammaValueD ρ ⟨_, const_mem_protoDomD ρ c⟩ v,
    Lp.coeFn_zero ℝ 1 (densityMeasureD ρ)] with x h hz
  change gammaValueD ρ _ _ x = _
  simp only [h, partialRep_const, Pi.zero_apply, zero_mul, Finset.sum_const_zero, hz]

end ErrorCalculus
