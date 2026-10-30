import Foundations.CameronMartin.DensityLimit

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Foundations

theorem measurable_gaussianTranslation {ι : Type*} (a : ι → ℝ) : Measurable (fun x : ι → ℝ => x+a) := by
  fun_prop

theorem gaussianTranslation_cylinder (a : ℕ → ℝ) (s : Finset ℕ) {A : Set (s → ℝ)}
    (hA : MeasurableSet A) :
    (gaussianInf.map (fun x => x+a)) (cylinder s A) =
      ENNReal.ofReal (∫ x in cylinder s A, cameronMartinDensitySet a s x ∂gaussianInf) := by
  have hm : (gaussianInf.map (fun x => x+a)).map s.restrict =
      (gaussianProduct s).map (fun x => x+s.restrict a) := by
    rw [Measure.map_map (measurable_gaussianRestrict s) (measurable_gaussianTranslation a),
      ← (gaussianInf_restrict_preserving s).map_eq,
      Measure.map_map (measurable_gaussianTranslation (s.restrict a))]
    · rfl
    · exact measurable_gaussianRestrict s
  have hs : (gaussianInf.map (fun x => x+a)) (cylinder s A) =
      ((gaussianProduct s).map (fun x => x+s.restrict a)) A := by
    rw [← hm,Measure.map_apply (measurable_gaussianRestrict s) hA]
    rfl
  rw [hs,finiteLevel_cameronMartin,withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_finiteGaussianShiftDensity (s.restrict a)).integrableOn
      (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)))]
  congr 1
  rw [← (gaussianInf_restrict_preserving s).map_eq,
    setIntegral_map hA (show AEStronglyMeasurable (finiteGaussianShiftDensity (s.restrict a)) _ from
      (show Measurable (finiteGaussianShiftDensity (s.restrict a)) from by
        unfold finiteGaussianShiftDensity gaussianShiftDensity; fun_prop).aestronglyMeasurable)
      (measurable_gaussianRestrict s).aemeasurable]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => (cameronMartinDensitySet_eq a s x).symm)

theorem gaussianTranslation_cylinder_limit (a : CameronMartinSpace) (s : Finset ℕ)
    {A : Set (s → ℝ)} (hA : MeasurableSet A) :
    (gaussianInf.map (fun x => x+(a : ℕ → ℝ))) (cylinder s A) =
      ENNReal.ofReal (∫ x in cylinder s A, cameronMartinDensity a x ∂gaussianInf) := by
  obtain ⟨N,hN⟩ := s.exists_nat_subset_range
  have he : ∀ᶠ n in atTop,
      ENNReal.ofReal (∫ x in cylinder s A, cameronMartinDensityFin a n x ∂gaussianInf) =
        (gaussianInf.map (fun x => x+(a : ℕ → ℝ))) (cylinder s A) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hsn : s ⊆ Finset.range n := hN.trans (Finset.range_mono hn)
    let q : (Finset.range n → ℝ) → (s → ℝ) := fun x i => x ⟨i,hsn i.property⟩
    have hq : Measurable q := by fun_prop
    have hC : cylinder (α := fun _ : ℕ => ℝ) s A =
        cylinder (α := fun _ : ℕ => ℝ) (Finset.range n) (q ⁻¹' A) := by
      ext x
      simp only [mem_cylinder,mem_preimage,Finset.restrict_def,q]
    rw [hC]
    exact (gaussianTranslation_cylinder a (Finset.range n) (hA.preimage hq)).symm
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_setIntegral_cameronMartinDensity a (cylinder s A))
  exact (tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he))).symm

end Foundations
