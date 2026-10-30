import ErrorCalculus.Dirichlet.WienerBasic

noncomputable section
open MeasureTheory Filter

namespace ErrorCalculus
variable {N M K : ℕ} {f g : (Fin N → ℝ) → ℝ}

/-- lifting a bounded C¹ function preserves its bounds. -/
theorem IsC1BoundedD.comp_projLE (hf : IsC1BoundedD f) (h : N ≤ M) :
    IsC1BoundedD (f ∘ projLE h) := by
  obtain ⟨C, hC⟩ := hf.2.2
  refine ⟨hf.1.comp (projLE h).contDiff, hf.2.1.imp (fun C hC x => hC _),
    ⟨C, fun x => ?_⟩⟩
  rw [fderiv_comp x (hf.differentiable _) (projLE h).differentiableAt,
    ContinuousLinearMap.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (projLE_opNorm_le h) (norm_nonneg (fderiv ℝ f (projLE h x)))).trans (by simpa using hC (projLE h x)))

@[simp] theorem projLE_single_lt (h : N ≤ M) (i : Fin N) :
    projLE h (Pi.single (Fin.castLE h i) 1) = Pi.single i 1 := by
  ext j
  simp [Pi.single_apply, Fin.castLE_injective h |>.eq_iff]

@[simp] theorem projLE_single_ge (h : N ≤ M) (i : Fin M) (hi : N ≤ i.val) :
    projLE h (Pi.single i 1) = 0 := by
  ext j
  simp only [projLE_apply, Pi.single_apply, Pi.zero_apply]
  split_ifs with he
  · have := congrArg Fin.val he
    simp only [Fin.val_castLE] at this
    omega
  · rfl

theorem partial_comp_projLE_lt (hf : Differentiable ℝ f) (h : N ≤ M)
    (i : Fin N) (x : Fin M → ℝ) :
    fderiv ℝ (f ∘ projLE h) x (Pi.single (Fin.castLE h i) 1) =
      fderiv ℝ f (projLE h x) (Pi.single i 1) := by
  rw [fderiv_comp x (hf _) (projLE h).differentiableAt]
  simp

theorem partial_comp_projLE_ge (hf : Differentiable ℝ f) (h : N ≤ M)
    (i : Fin M) (hi : N ≤ i.val) (x : Fin M → ℝ) :
    fderiv ℝ (f ∘ projLE h) x (Pi.single i 1) = 0 := by
  rw [fderiv_comp x (hf _) (projLE h).differentiableAt]
  simp [projLE_single_ge h i hi]

/-- all new derivative coordinates vanish. -/
theorem pointGammaD_comp_projLE (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (h : N ≤ M) (x : Fin M → ℝ) :
    pointGammaD (f ∘ projLE h) (g ∘ projLE h) x = pointGammaD f g (projLE h x) := by
  classical
  unfold pointGammaD
  symm
  apply Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
  · intro i hi
    have hi' : N ≤ i.val := by
      by_contra hn
      exact hi ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
    rw [partial_comp_projLE_ge hf h i hi', zero_mul]
  · intro i
    rw [partial_comp_projLE_lt hf, partial_comp_projLE_lt hg]

/-- The finite-level pullback preserves the actual pre-domain. -/
theorem liftLp_mem_protoDomD (h : N ≤ M) (u : protoDomD (ouDensityD N)) :
    liftLp h 2 (u : Lp ℝ 2 _) ∈ protoDomD (ouDensityD M) := by
  refine ⟨repD _ u ∘ projLE h, (rep_isC1BoundedD _ u).comp_projLE h, ?_⟩
  exact (coeFn_liftLp h 2 _).trans
    ((projLE_preserving h).quasiMeasurePreserving.ae_eq_comp (coeFn_repD _ u))

/-- A lift retaining the pre-domain subtype. -/
def liftProto (h : N ≤ M) : protoDomD (ouDensityD N) →ₗ[ℝ] protoDomD (ouDensityD M) :=
  ((liftLp h 2).toLinearMap.comp (protoDomD (ouDensityD N)).subtype).codRestrict
    (protoDomD (ouDensityD M)) (fun u => liftLp_mem_protoDomD h u)

@[simp] theorem coe_liftProto (h : N ≤ M) (u : protoDomD (ouDensityD N)) :
    (liftProto h u : Lp ℝ 2 _) = liftLp h 2 (u : Lp ℝ 2 _) := rfl

theorem rep_liftProto (h : N ≤ M) (u : protoDomD (ouDensityD N)) :
    repD _ (liftProto h u) = repD _ u ∘ projLE h := by
  apply rep_uniqueD _ _ ((rep_isC1BoundedD _ u).1.continuous.comp (projLE h).continuous)
  exact (coeFn_liftLp h 2 _).trans
    ((projLE_preserving h).quasiMeasurePreserving.ae_eq_comp (coeFn_repD _ u))

/-- Equality of L¹ classes, stronger than representative a.e. invariance. -/
theorem gammaD_comp_projLE (h : N ≤ M) (u v : protoDomD (ouDensityD N)) :
    gammaD (ouDensityD M) (liftProto h u) (liftProto h v) =
      liftLp h 1 (gammaD (ouDensityD N) u v) := by
  apply Lp.ext
  filter_upwards [coeFn_gammaD _ (liftProto h u) (liftProto h v),
    coeFn_liftLp h 1 (gammaD _ u v),
    (projLE_preserving h).quasiMeasurePreserving.ae (coeFn_gammaD _ u v)] with x ha hb hc
  rw [ha, hb, Function.comp_apply, hc]
  change pointGammaD (repD _ (liftProto h u)) (repD _ (liftProto h v)) x = _
  rw [rep_liftProto, rep_liftProto]
  exact pointGammaD_comp_projLE (rep_isC1BoundedD _ u).differentiable
    (rep_isC1BoundedD _ v).differentiable h x

/-- The OU energy is independent of the finite level. -/
theorem protoFormD_comp_projLE (h : N ≤ M) (u v : protoDomD (ouDensityD N)) :
    (protoFormD (ouDensityD M)).E (liftProto h u) (liftProto h v) =
      (protoFormD (ouDensityD N)).E u v := by
  change (1/2:ℝ) * (∫ x, gammaD _ (liftProto h u) (liftProto h v) x ∂_) =
    (1/2:ℝ) * (∫ x, gammaD _ u v x ∂_)
  rw [gammaD_comp_projLE, integral_congr_ae (coeFn_liftLp h 1 _)]
  congr 1
  have hu : AEStronglyMeasurable (⇑(gammaD (ouDensityD N) u v))
      ((densityMeasureD (ouDensityD M)).map (projLE h)) := by
    rw [(projLE_preserving h).map_eq]
    exact Lp.aestronglyMeasurable _
  exact (integral_map (projLE_preserving h).measurable.aemeasurable hu).symm.trans
    (by rw [(projLE_preserving h).map_eq])

theorem gradD_liftProto (h : N ≤ M) (i : Fin N) (u : protoDomD (ouDensityD N)) :
    gradD (ouDensityD M) (Fin.castLE h i) (liftProto h u) =
      liftLp h 2 (gradD (ouDensityD N) i u) := by
  apply Lp.ext
  filter_upwards [coeFn_gradD _ (Fin.castLE h i) (liftProto h u),
    coeFn_liftLp h 2 (gradD _ i u),
    (projLE_preserving h).quasiMeasurePreserving.ae (coeFn_gradD _ i u)] with x ha hb hc
  rw [ha, hb, Function.comp_apply, hc]
  change fderiv ℝ (repD _ (liftProto h u)) x _ = fderiv ℝ (repD _ u) _ _
  rw [rep_liftProto]
  exact partial_comp_projLE_lt (rep_isC1BoundedD _ u).differentiable h i x

theorem gradD_liftProto_ge (h : N ≤ M) (i : Fin M) (hi : N ≤ i.val)
    (u : protoDomD (ouDensityD N)) : gradD (ouDensityD M) i (liftProto h u) = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_gradD _ i (liftProto h u), Lp.coeFn_zero ℝ 2 (densityMeasureD (ouDensityD M))]
    with x ha hz
  rw [ha, hz]
  change fderiv ℝ (repD _ (liftProto h u)) x _ = 0
  rw [rep_liftProto]
  exact partial_comp_projLE_ge (rep_isC1BoundedD _ u).differentiable h i hi x

end ErrorCalculus
