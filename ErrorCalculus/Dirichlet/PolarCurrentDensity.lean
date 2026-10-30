import ErrorCalculus.Dirichlet.PolarCurrent

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
namespace ErrorCalculus
variable {n : ℕ}

/-- A vector L¹ density defines the mass by its Euclidean length. -/
def polarMass (μ : Measure (Fin n → ℝ)) (w : (Fin n → ℝ) → (Fin n → ℝ)) :
    Measure (Fin n → ℝ) := μ.withDensity (fun y => ENNReal.ofReal (polarNorm (w y)))

/-- A zero density is assigned the specified canonical direction. This set has zero mass. -/
def polarDirection (w : (Fin n → ℝ) → (Fin n → ℝ)) (i : Fin n)
    (y : Fin n → ℝ) : Fin n → ℝ :=
  if w y = 0 then Pi.single i 1 else (polarNorm (w y))⁻¹ • w y

theorem measurable_polarDirection {w : (Fin n → ℝ) → (Fin n → ℝ)}
    (hw : Measurable w) (i : Fin n) : Measurable (polarDirection w i) := by
  apply Measurable.ite (measurableSet_eq_fun hw measurable_const) measurable_const
  exact (((continuous_polarNorm n).measurable.comp hw).inv).smul hw

theorem polarNorm_direction {w : (Fin n → ℝ) → (Fin n → ℝ)}
    (hw : Measurable w) (i : Fin n) (μ : Measure (Fin n → ℝ)) :
    ∀ᵐ y ∂polarMass μ w, polarNorm (polarDirection w i y) = 1 := by
  apply (ae_withDensity_iff (((continuous_polarNorm n).measurable.comp hw).ennreal_ofReal)).mpr
  apply ae_of_all
  intro y hy
  have hpos : 0 < polarNorm (w y) := ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hy)
  have hw0 : w y ≠ 0 := by simpa using (ne_of_gt hpos)
  simp [polarDirection, hw0, polarNorm_smul, abs_of_pos (inv_pos.mpr hpos),
    inv_mul_cancel₀ hpos.ne']

theorem polarNorm_mul_direction (w : (Fin n → ℝ) → (Fin n → ℝ))
    (i j : Fin n) (y : Fin n → ℝ) :
    polarNorm (w y) * polarDirection w i y j = w y j := by
  by_cases h : w y = 0
  · simp [polarDirection, h, polarNorm]
  · simp [polarDirection, h, Pi.smul_apply, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ (polarNorm_eq_zero.not.mpr h)]

theorem polarMass_finite (μ : Measure (Fin n → ℝ))
    (w : (Fin n → ℝ) → (Fin n → ℝ))
    (hi : Integrable (fun y => polarNorm (w y)) μ) : IsFiniteMeasure (polarMass μ w) :=
  isFiniteMeasure_withDensity ((hasFiniteIntegral_iff_ofReal
    (ae_of_all _ (fun y => polarNorm_nonneg (w y)))).mp hi.hasFiniteIntegral).ne

/-- Polar current associated with an integrable measurable vector density. -/
def PolarCurrent.ofDensity (μ : Measure (Fin n → ℝ))
    (w : (Fin n → ℝ) → (Fin n → ℝ)) (hw : Measurable w)
    (hi : Integrable (fun y => polarNorm (w y)) μ) (i : Fin n) : PolarCurrent n where
  mass := polarMass μ w
  finite_mass := polarMass_finite μ w hi
  direction := polarDirection w i
  measurable_direction := measurable_polarDirection hw i
  norm_direction := polarNorm_direction hw i μ

/-- Cancellation of the polar normalization inside the integral; valid even on the zero set. -/
theorem PolarCurrent.ofDensity_action (μ : Measure (Fin n → ℝ))
    (w : (Fin n → ℝ) → (Fin n → ℝ)) (hw : Measurable w)
    (hi : Integrable (fun y => polarNorm (w y)) μ) (i : Fin n)
    (h : Fin n → (Fin n → ℝ) → ℝ) :
    (PolarCurrent.ofDensity μ w hw hi i).action h = ∫ y, ∑ j, h j y * w y j ∂μ := by
  change (∫ y, ∑ j, h j y * polarDirection w i y j
    ∂μ.withDensity (fun y => ENNReal.ofReal (polarNorm (w y)))) = _
  refine (integral_withDensity_eq_integral_toReal_smul (μ := μ)
    (f := fun y => ENNReal.ofReal (polarNorm (w y)))
    (((continuous_polarNorm n).measurable.comp hw).ennreal_ofReal)
    (ae_of_all μ (fun _ => ENNReal.ofReal_lt_top)) _).trans ?_
  apply integral_congr_ae
  apply ae_of_all
  intro y
  simp only [ENNReal.toReal_ofReal (polarNorm_nonneg _), smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_left_comm, polarNorm_mul_direction]

end ErrorCalculus
