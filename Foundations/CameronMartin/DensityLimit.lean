import Foundations.CameronMartin.Density

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology
namespace Foundations

private theorem norm_exp_le {X : Lp ℝ 2 gaussianInf} {D : (ℕ → ℝ) → ℝ}
    (hD : MemLp D 2 gaussianInf) (he : (fun x => Real.exp (X x)) =ᵐ[gaussianInf] D)
    {C : ℝ} (hC : 0 ≤ C) (hs : (∫ x, (D x)^2 ∂gaussianInf) ≤ C) :
    ‖((memLp_congr_ae he).mpr hD).toLp (fun x => Real.exp (X x))‖ ≤ C+1 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_toLp_sq]
  calc
    _ = ∫ x, (D x)^2 ∂gaussianInf := integral_congr_ae (he.pow_const 2)
    _ ≤ C := hs
    _ ≤ (C+1)^2 := by nlinarith [sq_nonneg C]

/--
An explicit L¹ error bound, obtained from the exponential difference estimate and Cauchy–Schwarz.
-/
theorem integral_abs_cameronMartinDensity_sub_le (a : CameronMartinSpace) (n : ℕ) :
    (∫ x, |cameronMartinDensityFin a n x-cameronMartinDensity a x| ∂gaussianInf) ≤
      ‖cameronMartinExponentFin a n-cameronMartinExponent a‖ *
        (2*(Real.exp (‖a‖^2)+1)) := by
  let hX := (memLp_congr_ae (exp_cameronMartinExponentFin a n)).mpr
    (memLp_cameronMartinDensitySet a (Finset.range n))
  let hY := (memLp_congr_ae (exp_cameronMartinExponent a)).mpr (memLp_cameronMartinDensity a)
  have hx := norm_exp_le (memLp_cameronMartinDensitySet a (Finset.range n))
    (exp_cameronMartinExponentFin a n) (Real.exp_pos _).le
    (integral_sq_cameronMartinDensityFin_le a n)
  have hy := norm_exp_le (memLp_cameronMartinDensity a)
    (exp_cameronMartinExponent a) (Real.exp_pos _).le
    (integral_sq_cameronMartinDensity a).le
  calc
    _ = ∫ x, |Real.exp (cameronMartinExponentFin a n x)-Real.exp (cameronMartinExponent a x)|
        ∂gaussianInf := by
      apply integral_congr_ae
      filter_upwards [exp_cameronMartinExponentFin a n,exp_cameronMartinExponent a] with x hn h
      rw [hn,h]
    _ ≤ ‖cameronMartinExponentFin a n-cameronMartinExponent a‖ *
        (‖hX.toLp _‖+‖hY.toLp _‖) := integral_abs_exp_sub_le _ _ hX hY
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)

theorem tendsto_cameronMartinDensity (a : CameronMartinSpace) :
    Tendsto (fun n => ∫ x, |cameronMartinDensityFin a n x-cameronMartinDensity a x| ∂gaussianInf)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _))
    (integral_abs_cameronMartinDensity_sub_le a)
  have h := ((tendsto_cameronMartinExponentFin a).sub (tendsto_const_nhds (x := cameronMartinExponent a))).norm.mul_const
    (2*(Real.exp (‖a‖^2)+1))
  simpa using h

/-- L¹ convergence also controls every measurable set integral, uniformly in the set. -/
theorem tendsto_setIntegral_cameronMartinDensity (a : CameronMartinSpace) (A : Set (ℕ → ℝ)) :
    Tendsto (fun n => ∫ x in A, cameronMartinDensityFin a n x ∂gaussianInf) atTop
      (𝓝 (∫ x in A, cameronMartinDensity a x ∂gaussianInf)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm (a := fun n => ∫ x, |cameronMartinDensityFin a n x-cameronMartinDensity a x| ∂gaussianInf)
  · intro n
    unfold cameronMartinDensityFin
    rw [← integral_sub ((memLp_cameronMartinDensitySet a (Finset.range n)).integrable
      (by norm_num)).integrableOn ((memLp_cameronMartinDensity a).integrable (by norm_num)).integrableOn]
    exact (norm_integral_le_integral_norm _).trans (integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ (fun x => norm_nonneg _))
      (((memLp_cameronMartinDensitySet a (Finset.range n)).integrable (by norm_num)).sub
        ((memLp_cameronMartinDensity a).integrable (by norm_num))).norm)
  · simpa only [Real.norm_eq_abs] using tendsto_cameronMartinDensity a

end Foundations
