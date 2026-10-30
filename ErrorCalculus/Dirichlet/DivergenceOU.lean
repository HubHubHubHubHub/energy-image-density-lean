import ErrorCalculus.Dirichlet.GradientD
import ErrorCalculus.Dirichlet.GaussianD

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace ErrorCalculus
variable {d : ℕ}

/-- One coordinate of the Gaussian divergence as an ordinary function. -/
def ouAdjointFunctionD (i : Fin d) (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  x i * g x - fderiv ℝ g x (Pi.single i 1)

theorem ouAdjoint_memLpD (i : Fin d) {g : (Fin d → ℝ) → ℝ} (hg : IsC1BoundedD g) :
    MemLp (ouAdjointFunctionD i g) 2 (densityMeasureD (ouDensityD d)) :=
  ((hg.memLp _ ∞).mul (ou_memLp_coordinateD i)).sub (hg.partial_memLp i _ 2)

def ouAdjointLpD (i : Fin d) (g : (Fin d → ℝ) → ℝ) (hg : IsC1BoundedD g) :
    Lp ℝ 2 (densityMeasureD (ouDensityD d)) := (ouAdjoint_memLpD i hg).toLp _

theorem coeFn_ouAdjointLpD (i : Fin d) (g : (Fin d → ℝ) → ℝ) (hg : IsC1BoundedD g) :
    ouAdjointLpD i g hg =ᵐ[densityMeasureD (ouDensityD d)] ouAdjointFunctionD i g :=
  (ouAdjoint_memLpD i hg).coeFn_toLp

/-- divergence of a field with C¹_b components, as an actual L² class. -/
def divergenceOU (g : Fin d → (Fin d → ℝ) → ℝ) (hg : ∀ i, IsC1BoundedD (g i)) :
    Lp ℝ 2 (densityMeasureD (ouDensityD d)) := ∑ i, ouAdjointLpD i (g i) (hg i)

theorem coeFn_divergenceOU (g : Fin d → (Fin d → ℝ) → ℝ) (hg : ∀ i, IsC1BoundedD (g i)) :
    divergenceOU g hg =ᵐ[densityMeasureD (ouDensityD d)]
      fun x => ∑ i, (x i * g i x - fderiv ℝ (g i) x (Pi.single i 1)) := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => ouAdjointLpD i (g i) (hg i)),
    ae_all_iff.mpr (fun i => coeFn_ouAdjointLpD i (g i) (hg i))] with x hs he
  change (∑ i, ouAdjointLpD i (g i) (hg i)) x = _
  rw [hs]
  exact Finset.sum_congr rfl (fun i _ => he i)

/-- Weighted integrability expressed with the Lebesgue density. -/
theorem integrable_ou_weightD {f : (Fin d → ℝ) → ℝ}
    (hf : Integrable f (densityMeasureD (ouDensityD d))) :
    Integrable (fun x => ouDensityD d x * f x) := by
  have h := (integrable_withDensity_iff_integrable_smul'
    (SmoothDensityD.contDiff (ρ := ouDensityD d)).continuous.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hf
  simpa only [ENNReal.toReal_ofReal (SmoothDensityD.pos _).le, smul_eq_mul] using h

/-- Gaussian integration by parts for bounded C¹ functions, without compact support. -/
theorem integral_partial_mul_ouD (i : Fin d) {f g : (Fin d → ℝ) → ℝ}
    (hf : IsC1BoundedD f) (hg : IsC1BoundedD g) :
    (∫ x, fderiv ℝ f x (Pi.single i 1) * g x ∂densityMeasureD (ouDensityD d)) =
      ∫ x, f x * ouAdjointFunctionD i g x ∂densityMeasureD (ouDensityD d) := by
  have hd (x : Fin d → ℝ) :
      fderiv ℝ (g * ouDensityD d) x (Pi.single i 1) =
        -(ouDensityD d x * ouAdjointFunctionD i g x) := by
    rw [fderiv_mul (hg.differentiable x)
      ((SmoothDensityD.contDiff (ρ := ouDensityD d)).differentiable (by norm_num) x)]
    simp only [add_apply, smul_apply,
      smul_eq_mul, partial_ouDensityD, ouAdjointFunctionD]
    ring
  have h1 := integrable_ou_weightD ((hf.memLp _ 2).integrable_mul (ouAdjoint_memLpD i hg))
  have h2 := integrable_ou_weightD ((hf.partial_memLp i _ 2).integrable_mul (hg.memLp _ 2))
  have h3 := integrable_ou_weightD ((hf.memLp _ 2).integrable_mul (hg.memLp _ 2))
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := g * ouDensityD d) (g := f) (v := Pi.single i 1)
    (by convert h1.neg using 1; funext x; rw [hd]; simp only [Pi.neg_apply, Pi.mul_apply]; ring)
    (by convert h2 using 1; funext x; simp only [Pi.mul_apply]; ring)
    (by convert h3 using 1; funext x; simp only [Pi.mul_apply]; ring)
    (fun x _ => (hg.differentiable x).mul
      ((SmoothDensityD.contDiff (ρ := ouDensityD d)).differentiable (by norm_num) x))
    (fun x _ => hf.differentiable x)
  rw [integral_densityD, integral_densityD]
  convert hi using 1
  · congr 1; funext x; simp only [Pi.mul_apply]; ring
  · rw [← integral_neg]
    congr 1; funext x; rw [hd]; ring

theorem inner_gradD_eq_ouAdjoint (i : Fin d) (u : protoDomD (ouDensityD d))
    (g : (Fin d → ℝ) → ℝ) (hg : IsC1BoundedD g) :
    inner ℝ (gradD (ouDensityD d) i u) ((hg.memLp _ 2).toLp g) =
      inner ℝ (u : Lp ℝ 2 (densityMeasureD (ouDensityD d))) (ouAdjointLpD i g hg) := by
  simp only [L2.inner_def]
  calc
    _ = ∫ x, fderiv ℝ (repD (ouDensityD d) u) x (Pi.single i 1) * g x
        ∂densityMeasureD (ouDensityD d) := by
      apply integral_congr_ae
      filter_upwards [coeFn_gradD (ouDensityD d) i u, (hg.memLp _ 2).coeFn_toLp] with x hu hx
      rw [hu, hx, real_inner_comm]; rfl
    _ = _ := integral_partial_mul_ouD i (rep_isC1BoundedD (ouDensityD d) u) hg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [coeFn_repD (ouDensityD d) u, coeFn_ouAdjointLpD i g hg] with x hu hx
      rw [hu, hx, real_inner_comm]; rfl

/-- The finite sum integration-by-parts identity on the proto-domain. -/
theorem inner_gradD_eq_divergence (u : protoDomD (ouDensityD d))
    (g : Fin d → (Fin d → ℝ) → ℝ) (hg : ∀ i, IsC1BoundedD (g i)) :
    (∑ i, inner ℝ (gradD (ouDensityD d) i u) (((hg i).memLp _ 2).toLp (g i))) =
      inner ℝ (u : Lp ℝ 2 (densityMeasureD (ouDensityD d))) (divergenceOU g hg) := by
  rw [divergenceOU, inner_sum]
  exact Finset.sum_congr rfl (fun i _ => inner_gradD_eq_ouAdjoint i u (g i) (hg i))

/-- G.3(a), written as integrals of the representatives. -/
theorem integral_gradD_mul_eq_divergence (u : protoDomD (ouDensityD d))
    (g : Fin d → (Fin d → ℝ) → ℝ) (hg : ∀ i, IsC1BoundedD (g i)) :
    (∑ i, ∫ x, gradD (ouDensityD d) i u x * g i x ∂densityMeasureD (ouDensityD d)) =
      ∫ x, (u : Lp ℝ 2 (densityMeasureD (ouDensityD d))) x * divergenceOU g hg x
        ∂densityMeasureD (ouDensityD d) := by
  calc
    _ = ∑ i, inner ℝ (gradD (ouDensityD d) i u) (((hg i).memLp _ 2).toLp (g i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [((hg i).memLp (densityMeasureD (ouDensityD d)) 2).coeFn_toLp] with x hx
      rw [hx, real_inner_comm]; rfl
    _ = _ := inner_gradD_eq_divergence u g hg
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by simp [mul_comm]

/-- continuity extends integration by parts to the entire OU domain. -/
theorem inner_gradient_eq_inner_divergence (u : (ouStructureD d).dom)
    (g : Fin d → (Fin d → ℝ) → ℝ) (hg : ∀ i, IsC1BoundedD (g i)) :
    (∑ i, inner ℝ (gradientD (ouDensityD d) i u) (((hg i).memLp _ 2).toLp (g i))) =
      inner ℝ (u : Lp ℝ 2 (densityMeasureD (ouDensityD d))) (divergenceOU g hg) := by
  obtain ⟨s, hs⟩ := ((protoFormD (ouDensityD d)).mem_closureDom_iff u).mp u.property
  have hleft := tendsto_finsetSum Finset.univ fun i _ =>
    (tendsto_gradD_of_approaches (ouDensityD d) i hs).inner (𝕜 := ℝ)
      (tendsto_const_nhds (x := ((hg i).memLp _ 2).toLp (g i)))
  have hright := hs.2.inner (𝕜 := ℝ) (tendsto_const_nhds (x := divergenceOU g hg))
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Eventually.of_forall fun n => (inner_gradD_eq_divergence (s n) g hg).symm)

/-- A coordinate form of the closed-domain identity, useful for Stein's formula. -/
theorem inner_gradient_eq_ouAdjoint (i : Fin d) (u : (ouStructureD d).dom)
    (g : (Fin d → ℝ) → ℝ) (hg : IsC1BoundedD g) :
    inner ℝ (gradientD (ouDensityD d) i u) ((hg.memLp _ 2).toLp g) =
      inner ℝ (u : Lp ℝ 2 (densityMeasureD (ouDensityD d))) (ouAdjointLpD i g hg) := by
  obtain ⟨s, hs⟩ := ((protoFormD (ouDensityD d)).mem_closureDom_iff u).mp u.property
  have hl := (tendsto_gradD_of_approaches (ouDensityD d) i hs).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := (hg.memLp _ 2).toLp g))
  apply tendsto_nhds_unique hl
  exact (hs.2.inner (𝕜 := ℝ) (tendsto_const_nhds (x := ouAdjointLpD i g hg))).congr'
    (Eventually.of_forall fun n => (inner_gradD_eq_ouAdjoint i (s n) g hg).symm)

/-- The divergence of a constant basis field is the corresponding coordinate. -/
theorem divergenceOU_basis (i : Fin d) :
    divergenceOU (fun j _ => if j = i then 1 else 0)
      (fun j => IsC1BoundedD.const (if j = i then 1 else 0)) = ouCoordinateLpD i := by
  apply Lp.ext
  filter_upwards [coeFn_divergenceOU (fun j _ => if j = i then 1 else 0)
    (fun j => IsC1BoundedD.const (if j = i then 1 else 0)), coeFn_ouCoordinateLpD i]
      with x hg hx
  rw [hg, hx]
  simp [mul_ite]

/-- Stein's identity for every element of the closed OU domain. -/
theorem integral_gradient_eq_integral_mul_coordinate (i : Fin d) (u : (ouStructureD d).dom) :
    (∫ x, gradientD (ouDensityD d) i u x ∂densityMeasureD (ouDensityD d)) =
      ∫ x, (u : Lp ℝ 2 (densityMeasureD (ouDensityD d))) x * x i
        ∂densityMeasureD (ouDensityD d) := by
  have h := inner_gradient_eq_ouAdjoint i u (fun _ => 1) (IsC1BoundedD.const 1)
  simp only [L2.inner_def] at h
  calc
    _ = _ := integral_congr_ae (show (fun x => gradientD (ouDensityD d) i u x) =ᵐ[_]
        (fun x => inner ℝ (gradientD (ouDensityD d) i u x)
          (((IsC1BoundedD.const 1).memLp (densityMeasureD (ouDensityD d)) 2).toLp (fun _ => 1) x)) by
      filter_upwards [((IsC1BoundedD.const 1).memLp (densityMeasureD (ouDensityD d)) 2).coeFn_toLp]
        with x hx
      rw [hx]; simp)
    _ = _ := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [coeFn_ouAdjointLpD i (fun _ => 1) (IsC1BoundedD.const 1)] with x hx
      rw [hx, real_inner_comm]
      simp [ouAdjointFunctionD]

end ErrorCalculus
