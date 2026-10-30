import Foundations.CameronMartin.Cylinders

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Foundations

/-- Cameron–Martin on the countable product: the image by translation by `a` has density `D_a`. -/
theorem gaussianInf_map_add_eq_withDensity (a : CameronMartinSpace) :
    gaussianInf.map (fun x => x+(a : ℕ → ℝ)) =
      gaussianInf.withDensity (fun x => ENNReal.ofReal (cameronMartinDensity a x)) := by
  have he : ∀ C ∈ measurableCylinders (fun _ : ℕ => ℝ),
      (gaussianInf.map (fun x => x+(a : ℕ → ℝ))) C =
        (gaussianInf.withDensity (fun x => ENNReal.ofReal (cameronMartinDensity a x))) C := by
    intro C hC
    obtain ⟨s,A,hA,rfl⟩ := (mem_measurableCylinders C).mp hC
    rw [gaussianTranslation_cylinder_limit a s hA,
      withDensity_apply _ (MeasurableSet.of_mem_measurableCylinders hC),
      ← ofReal_integral_eq_lintegral_ofReal
        ((memLp_cameronMartinDensity a).integrable (by norm_num)).integrableOn
        (ae_of_all _ (fun x => (Real.exp_pos _).le))]
  exact ext_of_generate_finite (measurableCylinders (fun _ : ℕ => ℝ))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders he
    (he univ (univ_mem_measurableCylinders _))

theorem gaussianInf_map_add_absolutelyContinuous (a : CameronMartinSpace) :
    gaussianInf.map (fun x => x+(a : ℕ → ℝ)) ≪ gaussianInf := by
  rw [gaussianInf_map_add_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

theorem gaussianInf_absolutelyContinuous_map_add (a : CameronMartinSpace) :
    gaussianInf ≪ gaussianInf.map (fun x => x+(a : ℕ → ℝ)) := by
  rw [gaussianInf_map_add_eq_withDensity]
  exact withDensity_absolutelyContinuous' (aemeasurable_cameronMartinDensity a).ennreal_ofReal
    (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'))

/--
Totalized Bochner integral identity; for integrable functions this is the usual change of variables.
-/
theorem integral_add_eq_integral_mul_cameronMartinDensity (a : CameronMartinSpace)
    (F : (ℕ → ℝ) → ℝ) (hF : Measurable F) :
    (∫ x, F (x+(a : ℕ → ℝ)) ∂gaussianInf) =
      ∫ x, F x*cameronMartinDensity a x ∂gaussianInf := by
  rw [← integral_map (measurable_gaussianTranslation a).aemeasurable hF.aestronglyMeasurable,
    gaussianInf_map_add_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul₀
      (aemeasurable_cameronMartinDensity a).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    have hp : 0 ≤ cameronMartinDensity a x := (Real.exp_pos _).le
    simp only [ENNReal.toReal_ofReal hp,smul_eq_mul,mul_comm])

/-- The sign is fixed by the preimage: the translated law at `A` is `γ(A-a)`. -/
theorem gaussianInf_preimage_add (a : CameronMartinSpace) {A : Set (ℕ → ℝ)}
    (hA : MeasurableSet A) :
    gaussianInf ((fun x => x+(a : ℕ → ℝ)) ⁻¹' A) =
      ENNReal.ofReal (∫ x in A, cameronMartinDensity a x ∂gaussianInf) := by
  rw [← Measure.map_apply (measurable_gaussianTranslation a) hA,
    gaussianInf_map_add_eq_withDensity,withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal
      ((memLp_cameronMartinDensity a).integrable (by norm_num)).integrableOn
      (ae_of_all _ (fun x => (Real.exp_pos _).le))]

theorem integrable_add_iff_mul_cameronMartinDensity (a : CameronMartinSpace)
    (F : (ℕ → ℝ) → ℝ) (hF : Measurable F) :
    Integrable (fun x => F (x+(a : ℕ → ℝ))) gaussianInf ↔
      Integrable (fun x => F x*cameronMartinDensity a x) gaussianInf := by
  have hm := integrable_map_measure (μ := gaussianInf) hF.aestronglyMeasurable
    (measurable_gaussianTranslation (a : ℕ → ℝ)).aemeasurable
  simp only [Function.comp_def] at hm
  rw [← hm,gaussianInf_map_add_eq_withDensity]
  have hp (x : ℕ → ℝ) : 0 ≤ cameronMartinDensity a x := (Real.exp_pos _).le
  have hw := integrable_withDensity_iff_integrable_smul₀' (g := F)
    (aemeasurable_cameronMartinDensity a).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))
  simpa only [ENNReal.toReal_ofReal (hp _),smul_eq_mul,mul_comm] using hw

/-- The integral form of the finite-dimensional formula. -/
theorem integral_finiteLevel_cameronMartin {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (F : (ι → ℝ) → ℝ) (hF : Measurable F) :
    (∫ x, F (x+a) ∂gaussianProduct ι) =
      ∫ x, F x*finiteGaussianShiftDensity a x ∂gaussianProduct ι := by
  rw [← integral_map (measurable_gaussianTranslation a).aemeasurable hF.aestronglyMeasurable,
    finiteLevel_cameronMartin,
    integral_withDensity_eq_integral_toReal_smul (by
      unfold finiteGaussianShiftDensity gaussianShiftDensity; fun_prop)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    have hp : 0 ≤ finiteGaussianShiftDensity a x :=
      Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)
    simp only [ENNReal.toReal_ofReal hp,smul_eq_mul,mul_comm])

end Foundations
