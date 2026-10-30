import ErrorCalculus.Dirichlet.DensityDStructure

noncomputable section
open MeasureTheory Filter
namespace ErrorCalculus
variable {d : ℕ}

/-- Each coordinate derivative is controlled by the operator norm for the sup norm. -/
theorem partial_norm_le_fderivD (g : (Fin d → ℝ) → ℝ) (i : Fin d) (x : Fin d → ℝ) :
    ‖fderiv ℝ g x (Pi.single i 1)‖ ≤ ‖fderiv ℝ g x‖ := by
  simpa only [Pi.norm_single, norm_one, mul_one] using
    ContinuousLinearMap.le_opNorm (fderiv ℝ g x) (Pi.single i 1)

/-- Conversely, the sum of the coordinate bounds controls the differential. -/
theorem fderiv_norm_le_sum_partialsD (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    ‖fderiv ℝ g x‖ ≤ ∑ i, ‖fderiv ℝ g x (Pi.single i 1)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  rw [fderiv_tuple_sum]
  calc
    _ ≤ ∑ i, ‖fderiv ℝ g x (Pi.single i 1) * v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖fderiv ℝ g x (Pi.single i 1)‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

/--
The two boundedness conventions for coordinate derivatives are equivalent, including dimension zero.
-/
theorem bounded_fderiv_iff_partialsD (g : (Fin d → ℝ) → ℝ) :
    (∃ C, ∀ x, ‖fderiv ℝ g x‖ ≤ C) ↔
      ∀ i : Fin d, ∃ C, ∀ x, ‖fderiv ℝ g x (Pi.single i 1)‖ ≤ C := by
  constructor
  · rintro ⟨C, hC⟩ i
    exact ⟨C, fun x => (partial_norm_le_fderivD g i x).trans (hC x)⟩
  · intro h
    choose C hC using h
    exact ⟨∑ i, C i, fun x => (fderiv_norm_le_sum_partialsD g x).trans
      (Finset.sum_le_sum fun i _ => hC i x)⟩

/-- Differential of a function depending on one coordinate only. -/
theorem fderiv_coordinateD {g : ℝ → ℝ} (hg : Differentiable ℝ g) (i : Fin d) (x : Fin d → ℝ) :
    fderiv ℝ (fun y : Fin d → ℝ => g (y i)) x =
      deriv g (x i) • ContinuousLinearMap.proj i :=
  ((hg (x i)).hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_apply i x)).fderiv

/-- The one-dimensional C¹_b class embeds through any coordinate. -/
theorem IsC1Bounded.coordinateD {g : ℝ → ℝ} (hg : IsC1Bounded g) (i : Fin d) :
    IsC1BoundedD (fun x : Fin d → ℝ => g (x i)) := by
  obtain ⟨C, hC⟩ := hg.2.1
  obtain ⟨D, hD⟩ := hg.2.2
  refine ⟨hg.1.comp (by fun_prop), ⟨C, fun x => hC (x i)⟩, ⟨max D 0, fun x => ?_⟩⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _)
  intro v
  rw [fderiv_coordinateD hg.differentiable i x]
  change ‖deriv g (x i) * v i‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul ((hD (x i)).trans (le_max_left _ _)) (norm_le_pi_norm v i)
    (norm_nonneg _) (le_max_right _ _)

/-- The sum of squared partials of a coordinate function has just one nonzero term. -/
theorem sum_sq_partials_coordinateD {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    (i : Fin d) (x : Fin d → ℝ) :
    (∑ j, (fderiv ℝ (fun y : Fin d → ℝ => g (y i)) x (Pi.single j 1))^2) =
      (deriv g (x i))^2 := by
  simp [fderiv_coordinateD hg, Pi.single_apply, eq_comm]

/-- The carré du champ of a function of one coordinate. -/
theorem densityStructureD_Γ_coordinate
    (ρ : (Fin d → ℝ) → ℝ) [IsProbabilityMeasure (densityMeasureD ρ)] [SmoothDensityD ρ]
    {g : ℝ → ℝ} (hg : IsC1Bounded g) (i : Fin d) :
    ⇑((densityStructureD ρ).Γ
      ((protoFormD ρ).inclusion (protoOfFunctionD ρ (fun x => g (x i)) (hg.coordinateD i)))
      ((protoFormD ρ).inclusion (protoOfFunctionD ρ (fun x => g (x i)) (hg.coordinateD i))))
      =ᵐ[densityMeasureD ρ] fun x => (deriv g (x i))^2 := by
  filter_upwards [densityStructureD_Γ_ofFunction ρ (fun x => g (x i)) (hg.coordinateD i)] with x hx
  exact hx.trans (sum_sq_partials_coordinateD hg.differentiable i x)

end ErrorCalculus
