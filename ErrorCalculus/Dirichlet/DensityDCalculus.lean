import ErrorCalculus.Dirichlet.DensityDGamma
import ErrorCalculus.Dirichlet.DensityCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators NNReal
namespace ErrorCalculus
variable {d : ℕ}

/-- A finite family of bounded functions is bounded in the product norm. -/
theorem finite_tuple_boundD {X V : Type*} [SeminormedAddCommGroup V]
    {m : ℕ} {g : Fin m → X → V}
    (hg : ∀ i, ∃ C, ∀ x, ‖g i x‖ ≤ C) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖fun i => g i x‖ ≤ C := by
  choose C hC using hg
  refine ⟨∑ i, |C i|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), fun x => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mpr
  intro i
  exact (hC i x).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)))

/-- Fréchet chain rule for a tuple of functions on ℝᵈ. -/
theorem fderiv_comp_tupleD {m : ℕ} {g : Fin m → (Fin d → ℝ) → ℝ}
    (hg : ∀ j, ContDiff ℝ 1 (g j)) {F : (Fin m → ℝ) → ℝ}
    (hF : ContDiff ℝ 1 F) (x : Fin d → ℝ) :
    fderiv ℝ (fun y => F (fun j => g j y)) x =
      (fderiv ℝ F (fun j => g j x)).comp (ContinuousLinearMap.pi (fun j => fderiv ℝ (g j) x)) := by
  exact ((hF.differentiable (by norm_num) _).hasFDerivAt.comp x
    (hasFDerivAt_pi.mpr fun j => ((hg j).differentiable (by norm_num) x).hasFDerivAt)).fderiv

/-- Coordinate chain rule, with the sum over the arguments of F. -/
theorem partial_comp_tupleD {m : ℕ} {g : Fin m → (Fin d → ℝ) → ℝ}
    (hg : ∀ j, ContDiff ℝ 1 (g j)) {F : (Fin m → ℝ) → ℝ}
    (hF : ContDiff ℝ 1 F) (i : Fin d) (x : Fin d → ℝ) :
    fderiv ℝ (fun y => F (fun j => g j y)) x (Pi.single i 1) =
      ∑ j, fderiv ℝ F (fun k => g k x) (Pi.single j 1) * fderiv ℝ (g j) x (Pi.single i 1) := by
  rw [fderiv_comp_tupleD hg hF]
  exact fderiv_tuple_sum F _ _

/-- C¹ Lipschitz compositions preserve C¹_b. -/
theorem IsC1BoundedD.comp_tuple {m : ℕ} {g : Fin m → (Fin d → ℝ) → ℝ}
    (hg : ∀ i, IsC1BoundedD (g i)) {F : (Fin m → ℝ) → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) :
    IsC1BoundedD (fun x => F (fun i => g i x)) := by
  obtain ⟨C, hC0, hC⟩ := finite_tuple_boundD (fun i => (hg i).2.1)
  obtain ⟨D, hD0, hD⟩ := finite_tuple_boundD (fun i => (hg i).2.2)
  refine ⟨hF.comp (contDiff_pi.mpr fun i => (hg i).1), ⟨(L:ℝ)*C + ‖F 0‖, fun x => ?_⟩,
    ⟨(L:ℝ)*D, fun x => ?_⟩⟩
  · have hb := hL.dist_le_mul (fun i => g i x) 0
    simp only [dist_eq_norm, sub_zero] at hb
    have ha := norm_add_le (F (fun i => g i x)-F 0) (F 0)
    rw [sub_add_cancel] at ha
    exact ha.trans (add_le_add (hb.trans (mul_le_mul_of_nonneg_left (hC x) L.coe_nonneg)) le_rfl)
  · rw [fderiv_comp_tupleD (fun i => (hg i).1) hF]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hL) _ (norm_nonneg _) L.coe_nonneg
    exact ContinuousLinearMap.norm_pi_le_of_le
      (fun j => (norm_le_pi_norm (fun i => fderiv ℝ (g i) x) j).trans (hD x)) hD0

variable (ρ : (Fin d → ℝ) → ℝ) [SmoothDensityD ρ] [IsProbabilityMeasure (densityMeasureD ρ)]

/--
A C¹ Lipschitz composition of finitely many finite-dimensional proto-domain elements belongs to that
domain and satisfies the multivariate carré-du-champ chain rule for every domain test.
-/
theorem protoData_calculusD (m : ℕ) (_hm : 0 < m) (u : Fin m → protoDomD ρ)
    (F : (Fin m → ℝ) → ℝ) (L : ℝ≥0) (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F)
    (w : Lp ℝ 2 (densityMeasureD ρ))
    (hw : ⇑w =ᵐ[densityMeasureD ρ] fun x => F (fun i => (u i : Lp ℝ 2 (densityMeasureD ρ)) x)) :
    ∃ hd : w ∈ (protoDataD ρ).dom, ∀ v : (protoDataD ρ).dom,
      ⇑((protoDataD ρ).Γ ⟨w, hd⟩ v) =ᵐ[densityMeasureD ρ] fun x => ∑ i,
        fderiv ℝ F (fun j => (u j : Lp ℝ 2 (densityMeasureD ρ)) x) (Pi.single i 1) *
          (protoDataD ρ).Γ (u i) v x := by
  let g := fun x => F (fun i => repD ρ (u i) x)
  have hg : IsC1BoundedD g := IsC1BoundedD.comp_tuple (fun i => rep_isC1BoundedD ρ (u i)) hF hL
  have hu : ∀ᵐ x ∂densityMeasureD ρ, ∀ i, (u i : Lp ℝ 2 (densityMeasureD ρ)) x = repD ρ (u i) x :=
    ae_all_iff.mpr (fun i => coeFn_repD ρ (u i))
  have hwg : ⇑w =ᵐ[densityMeasureD ρ] g := by
    filter_upwards [hw, hu] with x hx hux
    rw [hx]
    exact congrArg F (funext hux)
  have hd : w ∈ protoDomD ρ := ⟨g, hg, hwg⟩
  refine ⟨hd, fun v => ?_⟩
  change protoDomD ρ at v
  have hrep := rep_uniqueD ρ ⟨w, hd⟩ hg.1.continuous hwg
  have hΓ : ∀ᵐ x ∂densityMeasureD ρ, ∀ i,
      gammaD ρ (u i) v x = ∑ k, fderiv ℝ (repD ρ (u i)) x (Pi.single k 1) * fderiv ℝ (repD ρ v) x (Pi.single k 1) :=
    ae_all_iff.mpr (fun i => coeFn_gammaD ρ (u i) v)
  filter_upwards [coeFn_gammaD ρ ⟨w, hd⟩ v, hu, hΓ] with x hx hux hgam
  change gammaD ρ ⟨w, hd⟩ v x = _
  rw [hx, hrep]
  have htuple : (fun j => (u j : Lp ℝ 2 (densityMeasureD ρ)) x) = fun j => repD ρ (u j) x := funext hux
  change (∑ k, fderiv ℝ g x (Pi.single k 1) * fderiv ℝ (repD ρ v) x (Pi.single k 1)) = _
  dsimp only [g]
  simp_rw [partial_comp_tupleD (fun j => (rep_isC1BoundedD ρ (u j)).1) hF, Finset.sum_mul]
  rw [Finset.sum_comm, htuple]
  apply Finset.sum_congr rfl
  intro j _
  change _ = _ * gammaD ρ (u j) v x
  rw [hgam j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The probability density proto-structure with its full calculus. -/
def densityProtoD : ProtoErrorStructure (Fin d → ℝ) (densityMeasureD ρ) where
  toErrorData := protoDataD ρ
  dense := dense_protoDomD ρ
  «calc» := protoData_calculusD ρ
  one_mem := const_mem_protoDomD ρ 1

end ErrorCalculus
