import ErrorCalculus.Dirichlet.ProductDensityMeasure

noncomputable section
open MeasureTheory Filter
namespace ErrorCalculus
variable {d₁ d₂ : ℕ}
variable {g₁ h₁ : (Fin d₁ → ℝ) → ℝ} {g₂ h₂ : (Fin d₂ → ℝ) → ℝ}

/-- Differential of an elementary tensor. -/
theorem fderiv_tensorFun (hg₁ : Differentiable ℝ g₁) (hg₂ : Differentiable ℝ g₂)
    (z : Fin (d₁ + d₂) → ℝ) :
    fderiv ℝ (tensorFun g₁ g₂) z =
      g₁ (prodProj₁ d₁ d₂ z) • (fderiv ℝ g₂ (prodProj₂ d₁ d₂ z)).comp (prodProj₂ d₁ d₂) +
      g₂ (prodProj₂ d₁ d₂ z) • (fderiv ℝ g₁ (prodProj₁ d₁ d₂ z)).comp (prodProj₁ d₁ d₂) :=
  (((hg₁ _).hasFDerivAt.comp z (prodProj₁ d₁ d₂).hasFDerivAt).mul
    ((hg₂ _).hasFDerivAt.comp z (prodProj₂ d₁ d₂).hasFDerivAt)).fderiv

/-- bounded C¹ functions with bounded differential are stable under tensors. -/
theorem IsC1BoundedD.tensor (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂) :
    IsC1BoundedD (tensorFun g₁ g₂) := by
  obtain ⟨C, hC⟩ := hg₁.2.1
  obtain ⟨D, hD⟩ := hg₂.2.1
  obtain ⟨C', hC'⟩ := hg₁.2.2
  obtain ⟨D', hD'⟩ := hg₂.2.2
  have hC0 : 0 ≤ C := (norm_nonneg (g₁ 0)).trans (hC 0)
  have hD0 : 0 ≤ D := (norm_nonneg (g₂ 0)).trans (hD 0)
  have hC'0 : 0 ≤ C' := (norm_nonneg (fderiv ℝ g₁ 0)).trans (hC' 0)
  have hD'0 : 0 ≤ D' := (norm_nonneg (fderiv ℝ g₂ 0)).trans (hD' 0)
  refine ⟨(hg₁.1.comp (prodProj₁ d₁ d₂).contDiff).mul
    (hg₂.1.comp (prodProj₂ d₁ d₂).contDiff), ⟨C * D, fun z => ?_⟩,
    ⟨C * D' + D * C', fun z => ?_⟩⟩
  · exact (norm_mul _ _).le.trans (mul_le_mul (hC _) (hD _) (norm_nonneg _) hC0)
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [fderiv_tensorFun hg₁.differentiable hg₂.differentiable]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    calc
      _ ≤ ‖g₁ (prodProj₁ d₁ d₂ z)‖ * ‖fderiv ℝ g₂ (prodProj₂ d₁ d₂ z) (prodProj₂ d₁ d₂ v)‖ +
          ‖g₂ (prodProj₂ d₁ d₂ z)‖ * ‖fderiv ℝ g₁ (prodProj₁ d₁ d₂ z) (prodProj₁ d₁ d₂ v)‖ := by
        rw [← norm_mul, ← norm_mul]
        exact norm_add_le _ _
      _ ≤ C * (D' * ‖v‖) + D * (C' * ‖v‖) := by
        apply add_le_add
        · exact mul_le_mul (hC _) ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul (hD' _) (prodProj₂_norm_le v) (norm_nonneg _) hD'0)) (norm_nonneg _) hC0
        · exact mul_le_mul (hD _) ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul (hC' _) (prodProj₁_norm_le v) (norm_nonneg _) hC'0)) (norm_nonneg _) hD0
      _ = _ := by ring

@[simp] theorem prodProj₁_single_castAdd (j : Fin d₁) :
    prodProj₁ d₁ d₂ (Pi.single (Fin.castAdd d₂ j) 1) = Pi.single j 1 := by
  ext i
  simp [Pi.single_apply]
@[simp] theorem prodProj₂_single_castAdd (j : Fin d₁) :
    prodProj₂ d₁ d₂ (Pi.single (Fin.castAdd d₂ j) 1) = 0 := by
  ext i
  simp only [prodProj₂_apply, Pi.single_apply, Pi.zero_apply]
  split_ifs with h
  · have := congrArg Fin.val h; simp at this; omega
  · rfl
@[simp] theorem prodProj₁_single_natAdd (j : Fin d₂) :
    prodProj₁ d₁ d₂ (Pi.single (Fin.natAdd d₁ j) 1) = 0 := by
  ext i
  simp only [prodProj₁_apply, Pi.single_apply, Pi.zero_apply]
  split_ifs with h
  · have := congrArg Fin.val h; simp at this; omega
  · rfl
@[simp] theorem prodProj₂_single_natAdd (j : Fin d₂) :
    prodProj₂ d₁ d₂ (Pi.single (Fin.natAdd d₁ j) 1) = Pi.single j 1 := by
  ext i
  simp [Pi.single_apply]

theorem partial_tensor_castAdd (hg₁ : Differentiable ℝ g₁) (hg₂ : Differentiable ℝ g₂)
    (j : Fin d₁) (z : Fin (d₁ + d₂) → ℝ) :
    fderiv ℝ (tensorFun g₁ g₂) z (Pi.single (Fin.castAdd d₂ j) 1) =
      fderiv ℝ g₁ (prodProj₁ d₁ d₂ z) (Pi.single j 1) * g₂ (prodProj₂ d₁ d₂ z) := by
  simp [fderiv_tensorFun hg₁ hg₂, mul_comm]

theorem partial_tensor_natAdd (hg₁ : Differentiable ℝ g₁) (hg₂ : Differentiable ℝ g₂)
    (j : Fin d₂) (z : Fin (d₁ + d₂) → ℝ) :
    fderiv ℝ (tensorFun g₁ g₂) z (Pi.single (Fin.natAdd d₁ j) 1) =
      g₁ (prodProj₁ d₁ d₂ z) * fderiv ℝ g₂ (prodProj₂ d₁ d₂ z) (Pi.single j 1) := by
  simp [fderiv_tensorFun hg₁ hg₂]

/-- The canonical continuous representative of the mixed carré du champ. -/
def pointGammaD {d : ℕ} (g h : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, fderiv ℝ g x (Pi.single i 1) * fderiv ℝ h x (Pi.single i 1)

/-- P.2(b,c), pointwise, before choosing any L¹ representatives. -/
theorem pointGammaD_tensor (hg₁ : Differentiable ℝ g₁) (hg₂ : Differentiable ℝ g₂)
    (hh₁ : Differentiable ℝ h₁) (hh₂ : Differentiable ℝ h₂) (z : Fin (d₁ + d₂) → ℝ) :
    pointGammaD (tensorFun g₁ g₂) (tensorFun h₁ h₂) z =
      pointGammaD g₁ h₁ (prodProj₁ d₁ d₂ z) * (g₂ (prodProj₂ d₁ d₂ z) * h₂ (prodProj₂ d₁ d₂ z)) +
      (g₁ (prodProj₁ d₁ d₂ z) * h₁ (prodProj₁ d₁ d₂ z)) * pointGammaD g₂ h₂ (prodProj₂ d₁ d₂ z) := by
  unfold pointGammaD
  rw [Fin.sum_univ_add]
  simp only [partial_tensor_castAdd hg₁ hg₂, partial_tensor_castAdd hh₁ hh₂,
    partial_tensor_natAdd hg₁ hg₂, partial_tensor_natAdd hh₁ hh₂,
    Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

variable (ρ₁ : (Fin d₁ → ℝ) → ℝ) (ρ₂ : (Fin d₂ → ℝ) → ℝ)
    [SmoothDensityD ρ₁] [SmoothDensityD ρ₂]
    [IsProbabilityMeasure (densityMeasureD ρ₁)] [IsProbabilityMeasure (densityMeasureD ρ₂)]

/-- The mixed carré du champ of ordinary C¹_b functions. -/
theorem gammaD_ofFunction {d : ℕ} (ρ : (Fin d → ℝ) → ℝ) [SmoothDensityD ρ]
    [IsProbabilityMeasure (densityMeasureD ρ)] {g h : (Fin d → ℝ) → ℝ}
    (hg : IsC1BoundedD g) (hh : IsC1BoundedD h) :
    ⇑(gammaD ρ (protoOfFunctionD ρ g hg) (protoOfFunctionD ρ h hh)) =ᵐ[densityMeasureD ρ] pointGammaD g h := by
  unfold pointGammaD
  simpa only [rep_protoOfFunctionD] using
    coeFn_gammaD ρ (protoOfFunctionD ρ g hg) (protoOfFunctionD ρ h hh)

/-- B19's mixed formula, using the canonical derivative representatives on the right. -/
theorem gammaD_tensor (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂)
    (hh₁ : IsC1BoundedD h₁) (hh₂ : IsC1BoundedD h₂) :
    ⇑(gammaD (prodDensity ρ₁ ρ₂)
      (protoOfFunctionD _ (tensorFun g₁ g₂) (hg₁.tensor hg₂))
      (protoOfFunctionD _ (tensorFun h₁ h₂) (hh₁.tensor hh₂))) =ᵐ[densityMeasureD (prodDensity ρ₁ ρ₂)]
      fun z => pointGammaD g₁ h₁ (prodProj₁ d₁ d₂ z) * (g₂ (prodProj₂ d₁ d₂ z) * h₂ (prodProj₂ d₁ d₂ z)) +
        (g₁ (prodProj₁ d₁ d₂ z) * h₁ (prodProj₁ d₁ d₂ z)) * pointGammaD g₂ h₂ (prodProj₂ d₁ d₂ z) := by
  filter_upwards [gammaD_ofFunction (prodDensity ρ₁ ρ₂) (hg₁.tensor hg₂) (hh₁.tensor hh₂)] with z hz
  exact hz.trans (pointGammaD_tensor hg₁.differentiable hg₂.differentiable hh₁.differentiable hh₂.differentiable z)

theorem gammaD_tensor_diag (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂) :
    ⇑(gammaD (prodDensity ρ₁ ρ₂)
      (protoOfFunctionD _ (tensorFun g₁ g₂) (hg₁.tensor hg₂))
      (protoOfFunctionD _ (tensorFun g₁ g₂) (hg₁.tensor hg₂))) =ᵐ[densityMeasureD (prodDensity ρ₁ ρ₂)]
      fun z => pointGammaD g₁ g₁ (prodProj₁ d₁ d₂ z) * g₂ (prodProj₂ d₁ d₂ z)^2 +
        g₁ (prodProj₁ d₁ d₂ z)^2 * pointGammaD g₂ g₂ (prodProj₂ d₁ d₂ z) := by
  simpa only [pow_two] using gammaD_tensor ρ₁ ρ₂ hg₁ hg₂ hg₁ hg₂

theorem gammaD_tensor_one (hg₁ : IsC1BoundedD g₁) (hh₁ : IsC1BoundedD h₁) :
    ⇑(gammaD (prodDensity ρ₁ ρ₂)
      (protoOfFunctionD _ (tensorFun g₁ (fun _ => 1)) (hg₁.tensor (IsC1BoundedD.const 1)))
      (protoOfFunctionD _ (tensorFun h₁ (fun _ => 1)) (hh₁.tensor (IsC1BoundedD.const 1))))
      =ᵐ[densityMeasureD (prodDensity ρ₁ ρ₂)] fun z => pointGammaD g₁ h₁ (prodProj₁ d₁ d₂ z) := by
  simpa [pointGammaD] using gammaD_tensor ρ₁ ρ₂ hg₁ (IsC1BoundedD.const 1) hh₁ (IsC1BoundedD.const 1)

/-- The same mixed formula with the actual L¹ representatives of both factor forms. -/
theorem gammaD_tensor_classes (hg₁ : IsC1BoundedD g₁) (hg₂ : IsC1BoundedD g₂)
    (hh₁ : IsC1BoundedD h₁) (hh₂ : IsC1BoundedD h₂) :
    ⇑(gammaD (prodDensity ρ₁ ρ₂)
      (protoOfFunctionD _ (tensorFun g₁ g₂) (hg₁.tensor hg₂))
      (protoOfFunctionD _ (tensorFun h₁ h₂) (hh₁.tensor hh₂))) =ᵐ[densityMeasureD (prodDensity ρ₁ ρ₂)]
      fun z => gammaD ρ₁ (protoOfFunctionD _ g₁ hg₁) (protoOfFunctionD _ h₁ hh₁) (prodProj₁ d₁ d₂ z) *
        (g₂ (prodProj₂ d₁ d₂ z) * h₂ (prodProj₂ d₁ d₂ z)) +
        (g₁ (prodProj₁ d₁ d₂ z) * h₁ (prodProj₁ d₁ d₂ z)) *
        gammaD ρ₂ (protoOfFunctionD _ g₂ hg₂) (protoOfFunctionD _ h₂ hh₂) (prodProj₂ d₁ d₂ z) := by
  filter_upwards [gammaD_tensor ρ₁ ρ₂ hg₁ hg₂ hh₁ hh₂,
    (prodProj₁_density_preserving ρ₁ ρ₂).quasiMeasurePreserving.ae (gammaD_ofFunction ρ₁ hg₁ hh₁),
    (prodProj₂_density_preserving ρ₁ ρ₂).quasiMeasurePreserving.ae (gammaD_ofFunction ρ₂ hg₂ hh₂)] with z hz h₁ h₂
  rw [hz, h₁, h₂]

end ErrorCalculus
