import ErrorCalculus.Dirichlet.WienerProto

noncomputable section
open MeasureTheory Filter Topology

namespace ErrorCalculus

/-- The energy at a specified cylindrical level is half the sum of squared L² gradients. -/
theorem wienerEnergy_cyl_eq_sum (N : ℕ) (u : protoDomD (ouDensityD N)) :
    wienerProto.energy.E (cylProto N u) (cylProto N u) =
      (1/2:ℝ) * ∑ i ∈ Finset.range N, ‖wienerPartial i (cylProto N u)‖^2 := by
  rw [wienerProto_energy_cyl, protoFormD_eq_grad, ← Fin.sum_univ_eq_sum_range]
  simp only [wienerPartial_cyl, (cylLp N 2).norm_map]

/-- Finite-coordinate energy, defined without choosing a level. -/
def partialEnergy (K : ℕ) (F : wienerDom) : ℝ :=
  (1/2:ℝ) * ∑ i ∈ Finset.range K, ‖wienerPartial i F‖^2

theorem partialEnergy_nonneg (K : ℕ) (F : wienerDom) : 0 ≤ partialEnergy K F := by
  unfold partialEnergy
  positivity

theorem partialEnergy_mono (F : wienerDom) : Monotone (fun K => partialEnergy K F) := by
  intro K M h
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _ => sq_nonneg _)

/-- W2.1(a), at every level above the chosen cylindrical representation. -/
theorem wienerEnergy_eq_sum_partial (F : wienerDom) {K : ℕ} (hK : level F ≤ K) :
    wienerProto.energy.E F F = partialEnergy K F := by
  have h := wienerEnergy_cyl_eq_sum K (cylRepAt F hK)
  simpa only [cylRepAt_spec, partialEnergy] using h

theorem partialEnergy_le (K : ℕ) (F : wienerDom) :
    partialEnergy K F ≤ wienerProto.energy.E F F := by
  rw [wienerEnergy_eq_sum_partial F (le_max_right K (level F))]
  exact partialEnergy_mono F (le_max_left _ _)

/-- The energy carried by coordinates with index at least K. -/
def tail (K : ℕ) (F : wienerDom) : ℝ := wienerProto.energy.E F F - partialEnergy K F

theorem tail_nonneg (K : ℕ) (F : wienerDom) : 0 ≤ tail K F :=
  sub_nonneg.mpr (partialEnergy_le K F)

theorem tail_le_energy (K : ℕ) (F : wienerDom) : tail K F ≤ wienerProto.energy.E F F :=
  sub_le_self _ (partialEnergy_nonneg K F)

/-- The essential finite-support fact for the tail argument. -/
theorem tail_eq_zero_of_level (F : wienerDom) {K : ℕ} (hK : level F ≤ K) : tail K F = 0 := by
  rw [tail, wienerEnergy_eq_sum_partial F hK, sub_self]

theorem tail_cyl_eq_zero {N K : ℕ} (h : N ≤ K) (u : protoDomD (ouDensityD N)) :
    tail K (cylProto N u) = 0 := by
  have he : partialEnergy K (cylProto N u) = partialEnergy N (cylProto N u) := by
    unfold partialEnergy
    congr 1
    symm
    apply Finset.sum_subset (Finset.range_mono h)
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    rw [wienerPartial_cyl_ge hi, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [tail, he, wienerEnergy_cyl_eq_sum]
  exact sub_self _

theorem tail_eq_sum (F : wienerDom) {K M : ℕ} (hKM : K ≤ M) (hM : level F ≤ M) :
    tail K F = (1/2:ℝ) * ∑ i ∈ Finset.range M \ Finset.range K, ‖wienerPartial i F‖^2 := by
  rw [tail, wienerEnergy_eq_sum_partial F hM, partialEnergy, partialEnergy,
    ← mul_sub]
  congr 1
  have h := Finset.sum_sdiff (f := fun i => ‖wienerPartial i F‖^2) (Finset.range_mono hKM)
  linarith

/-- Bilinear finite-coordinate energy. -/
def partialEnergyBilin (K : ℕ) : wienerDom →ₗ[ℝ] wienerDom →ₗ[ℝ] ℝ :=
  (1/2:ℝ) • ∑ i ∈ Finset.range K,
    (innerₗ (Lp ℝ 2 wienerCoord)).compl₁₂ (wienerPartial i) (wienerPartial i)

theorem partialEnergyBilin_apply (K : ℕ) (F G : wienerDom) :
    partialEnergyBilin K F G =
      (1/2:ℝ) * ∑ i ∈ Finset.range K, inner ℝ (wienerPartial i F) (wienerPartial i G) := by
  simp [partialEnergyBilin]

/-- The tail is itself a nonnegative quadratic form on the cylindrical domain. -/
def tailForm (K : ℕ) : QuadForm (Lp ℝ 2 wienerCoord) where
  dom := wienerDom
  E := (show wienerDom →ₗ[ℝ] wienerDom →ₗ[ℝ] ℝ from wienerProto.energy.E) - partialEnergyBilin K
  symm F G := by
    change wienerProto.energy.E F G - partialEnergyBilin K F G =
      wienerProto.energy.E G F - partialEnergyBilin K G F
    simp only [partialEnergyBilin_apply]
    rw [wienerProto.energy.symm F G]
    simp only [real_inner_comm]
  nonneg F := by
    change 0 ≤ wienerProto.energy.E F F - partialEnergyBilin K F F
    simpa only [partialEnergyBilin_apply, real_inner_self_eq_norm_sq, tail, partialEnergy]
      using tail_nonneg K F

theorem tailForm_diag (K : ℕ) (F : wienerDom) : (tailForm K).E F F = tail K F := by
  change wienerProto.energy.E F F - partialEnergyBilin K F F = _
  simp only [partialEnergyBilin_apply, real_inner_self_eq_norm_sq, tail, partialEnergy]

/-- The triangle inequality follows from the quadratic-form seminorm. -/
theorem sqrt_tail_add_le (K : ℕ) (F G : wienerDom) :
    Real.sqrt (tail K (F+G)) ≤ Real.sqrt (tail K F) + Real.sqrt (tail K G) := by
  have h := (tailForm K).seminorm_add F G
  change Real.sqrt ((tailForm K).E (F+G) (F+G)) ≤
    Real.sqrt ((tailForm K).E F F) + Real.sqrt ((tailForm K).E G G) at h
  simpa only [tailForm_diag] using h

theorem sqrt_tail_sub_le (K : ℕ) (F G : wienerDom) :
    Real.sqrt (tail K F) ≤ Real.sqrt (wienerProto.energy.E (F-G) (F-G)) +
      Real.sqrt (tail K G) := by
  calc
    _ = Real.sqrt (tail K ((F-G)+G)) := by rw [sub_add_cancel]
    _ ≤ Real.sqrt (tail K (F-G)) + Real.sqrt (tail K G) := sqrt_tail_add_le K _ _
    _ ≤ _ := add_le_add (Real.sqrt_le_sqrt (tail_le_energy K (F-G))) le_rfl

end ErrorCalculus
