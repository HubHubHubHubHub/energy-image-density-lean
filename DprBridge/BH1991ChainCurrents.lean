import DprBridge.BH1991ResolventCore
import DprBridge.BH1991ChainRules
import DprBridge.BH1991LevelCancellation
import DprBridge.BH1991GammaLocality
import DprBridge.BH1991NormalContractions
import DprBridge.BH1991Printed
import ErrorCalculus.Dirichlet.PolarCurrentNormal

/-!
# Centered BH chains and normal currents

## Main results
On the original arbitrary measure, tensor interpolation and coefficient closure give centered
multivariate chains in the BH domain. The resulting normal currents retain the Dirac correction at
zero from Eriksson-Bique–Murugan, Section 4.2, Remark 4.12, p. 38. Gamma has the BH normalization, Γ
= 2γ.

References: Bouleau–Hirsch (1991), ch. I, I.6.1.2–3, pp. 36–37; the EID formulation in ch. V, p.
185, and Notes, p. 302. The sigma-finite EID conclusion is proved in `DprBridge.BH1991PrintedProof`,
following the normal-current method of Eriksson-Bique–Murugan (Section 4.2, Remark 4.12) and
the structure theorem of De Philippis–Rindler.
-/
noncomputable section
set_option autoImplicit false
-- Elaboration through the form-space/domain linear equivalence needs this budget.
set_option maxHeartbeats 1200000
open MeasureTheory Filter Topology ErrorCalculus
open scoped NNReal ENNReal ContDiff
universe u

namespace DprBridge.BH1991.DirichletForm
variable {X : Type u} [MeasurableSpace X] {m : Measure X} (D : DirichletForm m)

/-- Finite linear combinations preserve centered representatives and their chain coefficients. -/
theorem centered_chain_sum (G : D.CarreDuChamp) {n : ℕ} {ι : Type*}
    (s : Finset ι) (f : Fin n → D.toCapacity.Space) (p : ι → D.toCapacity.Space)
    (A : ι → ℝ) (P : ι → (Fin n → ℝ) → ℝ)
    (c : ι → Fin n → (Fin n → ℝ) → ℝ)
    (hp : ∀ z ∈ s, ⇑(D.toCapacity.toLp (p z)) =ᵐ[m] fun x =>
      P z (fun i => D.toCapacity.toLp (f i) x) - P z 0)
    (hγ : ∀ z ∈ s, ∀ v, ⇑(G.Γ (p z) v) =ᵐ[m] fun x =>
      ∑ i, c z i (fun j => D.toCapacity.toLp (f j) x) * G.Γ (f i) v x) :
    (⇑(D.toCapacity.toLp (∑ z ∈ s, A z • p z)) =ᵐ[m] fun x =>
      (∑ z ∈ s, A z * P z (fun i => D.toCapacity.toLp (f i) x)) -
        ∑ z ∈ s, A z * P z 0) ∧
    ∀ v, ⇑(G.Γ (∑ z ∈ s, A z • p z) v) =ᵐ[m] fun x =>
      ∑ i, (∑ z ∈ s, A z * c z i (fun j => D.toCapacity.toLp (f j) x)) *
        G.Γ (f i) v x := by
  classical
  constructor
  · simp only [map_sum, map_smul]
    filter_upwards [lp_coeFn_sum s (fun z => A z • D.toCapacity.toLp (p z)),
      (ae_all_iff.2 fun z : s => hp z z.2),
      (ae_all_iff.2 fun z : s => Lp.coeFn_smul (A z) (D.toCapacity.toLp (p z)))]
      with x hs hr hm
    rw [hs, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hm ⟨z, hz⟩, Pi.smul_apply, smul_eq_mul, hr ⟨z, hz⟩, mul_sub]
  · intro v
    simp only [map_sum, map_smul, sum_apply, smul_apply]
    filter_upwards [lp_coeFn_sum s (fun z => A z • G.Γ (p z) v),
      (ae_all_iff.2 fun z : s => hγ z z.2 v),
      (ae_all_iff.2 fun z : s => Lp.coeFn_smul (A z) (G.Γ (p z) v))]
      with x hs hr hm
    rw [hs]
    calc
      _ = ∑ z ∈ s, ∑ i, A z * c z i (fun j => D.toCapacity.toLp (f j) x) *
          G.Γ (f i) v x := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hm ⟨z, hz⟩, Pi.smul_apply, smul_eq_mul, hr ⟨z, hz⟩, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.sum_mul]

/-- Centered products can be assembled from scalar chain identities, with no domain constants. -/
theorem centered_chain_tensor (hL : D.Local) (G : D.CarreDuChamp) {n : ℕ}
    (f p : Fin n → D.toCapacity.Space) (H H' : Fin n → ℝ → ℝ)
    (hp : ∀ i, p i ∈ D.toCapacity.bddSpace)
    (hr : ∀ i, ⇑(D.toCapacity.toLp (p i)) =ᵐ[m] fun x =>
      H i (D.toCapacity.toLp (f i) x) - H i 0)
    (hγ : ∀ i v, ⇑(G.Γ (p i) v) =ᵐ[m] fun x =>
      H' i (D.toCapacity.toLp (f i) x) * G.Γ (f i) v x) :
    ∃ w : D.toCapacity.Space, w ∈ D.toCapacity.bddSpace ∧
      (⇑(D.toCapacity.toLp w) =ᵐ[m] fun x =>
        (∏ i, H i (D.toCapacity.toLp (f i) x)) - ∏ i, H i 0) ∧
      ∀ v, ⇑(G.Γ w v) =ᵐ[m] fun x =>
        ∑ i, ((∏ j ∈ Finset.univ.erase i, H j (D.toCapacity.toLp (f j) x)) *
          H' i (D.toCapacity.toLp (f i) x)) * G.Γ (f i) v x := by
  classical
  obtain ⟨w, hw, hwrep, hwγ⟩ := D.centered_translated_product hL G Finset.univ p
    (fun i _ => hp i) (fun i => H i 0)
  refine ⟨w, hw, ?_, fun v => ?_⟩
  · filter_upwards [hwrep, ae_all_iff.2 hr] with x hx hrx
    simpa only [hrx, sub_add_cancel] using hx
  · filter_upwards [hwγ v, ae_all_iff.2 hr, ae_all_iff.2 fun i => hγ i v]
      with x hx hrx hγx
    rw [hx]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hrx, sub_add_cancel, hγx]
    ring

/-- The centered clamp satisfies the mixed Gamma identity with its right-hand coefficient. -/
theorem gamma_centeredClamp_right (hL : D.Local) (G : D.CarreDuChamp)
    (a b : ℝ) (hab : a ≤ b) (v w : D.toCapacity.Space) :
    ⇑(G.Γ (D.centeredClamp a b v) w) =ᵐ[m] fun x =>
      (Set.Ico a b).indicator 1 (D.toCapacity.toLp v x) * G.Γ v w x := by
  filter_upwards [D.gamma_centeredClamp hL G a b hab v w,
    D.gamma_eq_zero_on_level_space hL G v w a] with x hx hz
  rw [hx]
  by_cases he : D.toCapacity.toLp v x = a
  · rw [hz he]; simp only [mul_zero]
  · have hm : D.toCapacity.toLp v x ∈ Set.Ioo a b ↔
        D.toCapacity.toLp v x ∈ Set.Ico a b := by
      simp only [Set.mem_Ioo, Set.mem_Ico]
      exact and_congr_left fun _ => ⟨le_of_lt, fun h => lt_of_le_of_ne h (Ne.symm he)⟩
    by_cases ht : D.toCapacity.toLp v x ∈ Set.Ioo a b
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (hm.mp ht)]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (mt hm.mpr ht)]

/-- The centered scalar hat is the inverse mesh times the difference of two centered clamps. -/
def centeredHat (a δ : ℝ) (v : D.toCapacity.Space) : D.toCapacity.Space :=
  δ⁻¹ • (D.centeredClamp (a - δ) a v - D.centeredClamp a (a + δ) v)

/-- The real hat is centered before it is represented in L2. -/
theorem coe_centeredHat (a δ : ℝ) (v : D.toCapacity.Space) :
    ⇑(D.toCapacity.toLp (D.centeredHat a δ v)) =ᵐ[m] fun x =>
      gridHat a δ (D.toCapacity.toLp v x) - gridHat a δ 0 := by
  simp only [centeredHat, map_smul, map_sub]
  filter_upwards [Lp.coeFn_smul δ⁻¹
      (D.toCapacity.toLp (D.centeredClamp (a - δ) a v) -
        D.toCapacity.toLp (D.centeredClamp a (a + δ) v)),
    Lp.coeFn_sub (D.toCapacity.toLp (D.centeredClamp (a - δ) a v))
      (D.toCapacity.toLp (D.centeredClamp a (a + δ) v)),
    D.coe_centeredClamp (a - δ) a v, D.coe_centeredClamp a (a + δ) v]
      with x h1 h2 h3 h4
  rw [h1, Pi.smul_apply, smul_eq_mul, h2, Pi.sub_apply, h3, h4]
  unfold gridHat
  ring

/-- Centered hats belong to the bounded form domain when the mesh is positive. -/
theorem centeredHat_bounded (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (v : D.toCapacity.Space) :
    D.centeredHat a δ v ∈ D.toCapacity.bddSpace := by
  refine ⟨1, ?_⟩
  filter_upwards [D.coe_centeredHat a δ v] with x hx
  rw [hx, abs_le]
  constructor <;> linarith [gridHat_nonneg hδ a (D.toCapacity.toLp v x),
    gridHat_nonneg hδ a 0, gridHat_le_one hδ a (D.toCapacity.toLp v x),
    gridHat_le_one hδ a 0]

/-- Right-hand slopes of compact hats, including their left and central nodes. -/
def rightHatSlope (a δ t : ℝ) : ℝ :=
  ((Set.Ico (a - δ) a).indicator 1 t - (Set.Ico a (a + δ)).indicator 1 t) / δ

/-- Right-hand hat slopes are measurable, without restrictions on the mesh. -/
theorem measurable_rightHatSlope (a δ : ℝ) : Measurable (rightHatSlope a δ) := by
  exact ((measurable_one.indicator measurableSet_Ico).sub
    (measurable_one.indicator measurableSet_Ico)).div_const δ

/-- The centered hat chain identity uses the prescribed right-hand slopes. -/
theorem gamma_centeredHat_right (hL : D.Local) (G : D.CarreDuChamp)
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (v w : D.toCapacity.Space) :
    ⇑(G.Γ (D.centeredHat a δ v) w) =ᵐ[m] fun x =>
      rightHatSlope a δ (D.toCapacity.toLp v x) * G.Γ v w x := by
  simp only [centeredHat, map_smul, map_sub, smul_apply, sub_apply]
  filter_upwards [Lp.coeFn_smul δ⁻¹
      (G.Γ (D.centeredClamp (a - δ) a v) w - G.Γ (D.centeredClamp a (a + δ) v) w),
    Lp.coeFn_sub (G.Γ (D.centeredClamp (a - δ) a v) w)
      (G.Γ (D.centeredClamp a (a + δ) v) w),
    D.gamma_centeredClamp_right hL G (a - δ) a (by linarith) v w,
    D.gamma_centeredClamp_right hL G a (a + δ) (by linarith) v w]
      with x h1 h2 h3 h4
  rw [h1, Pi.smul_apply, smul_eq_mul, h2, Pi.sub_apply, h3, h4]
  unfold rightHatSlope
  ring

/-- A tensor cell coefficient multiplies one right-hand hat slope by the other scalar hats. -/
def rightCellSlope {n K : ℕ} (a δ : ℝ) (z : Fin n → Fin (K + 1))
    (i : Fin n) (y : Fin n → ℝ) : ℝ :=
  (∏ j ∈ Finset.univ.erase i, gridHat (gridNode a δ z j) δ (y j)) *
    rightHatSlope (gridNode a δ z i) δ (y i)

/-- Each tensor cell has an actual bounded centered representative in the BH domain. -/
theorem centered_cell (hL : D.Local) (G : D.CarreDuChamp) {n K : ℕ}
    (f : Fin n → D.toCapacity.Space) (a : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (z : Fin n → Fin (K + 1)) :
    ∃ w : D.toCapacity.Space, w ∈ D.toCapacity.bddSpace ∧
      (⇑(D.toCapacity.toLp w) =ᵐ[m] fun x =>
        cellWeight a δ z (fun i => D.toCapacity.toLp (f i) x) - cellWeight a δ z 0) ∧
      ∀ v, ⇑(G.Γ w v) =ᵐ[m] fun x =>
        ∑ i, rightCellSlope a δ z i (fun j => D.toCapacity.toLp (f j) x) *
          G.Γ (f i) v x := by
  exact D.centered_chain_tensor hL G f (fun i => D.centeredHat (gridNode a δ z i) δ (f i))
    (fun i => gridHat (gridNode a δ z i) δ) (fun i => rightHatSlope (gridNode a δ z i) δ)
    (fun i => D.centeredHat_bounded _ hδ _)
    (fun i => D.coe_centeredHat _ _ _)
    (fun i v => D.gamma_centeredHat_right hL G _ hδ _ v)

/-- Finite multilinear interpolation from its nodal values. -/
def tensorInterp {n K : ℕ} (a δ : ℝ) (F : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ z : Fin n → Fin (K + 1), F (gridNode a δ z) * cellWeight a δ z y

/-- The right-hand coefficient of the finite tensor interpolant. -/
def tensorInterpCoeff {n K : ℕ} (a δ : ℝ) (F : (Fin n → ℝ) → ℝ)
    (i : Fin n) (y : Fin n → ℝ) : ℝ :=
  ∑ z : Fin n → Fin (K + 1), F (gridNode a δ z) * rightCellSlope a δ z i y

/-- Finite tensor interpolation is constructed in the domain before any limiting argument. -/
theorem centered_tensorInterp (hL : D.Local) (G : D.CarreDuChamp) {n K : ℕ}
    (f : Fin n → D.toCapacity.Space) (a : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (F : (Fin n → ℝ) → ℝ) :
    ∃ w : D.toCapacity.Space, w ∈ D.toCapacity.bddSpace ∧
      (⇑(D.toCapacity.toLp w) =ᵐ[m] fun x =>
        tensorInterp (K := K) a δ F (fun i => D.toCapacity.toLp (f i) x) -
          tensorInterp (K := K) a δ F 0) ∧
      ∀ v, ⇑(G.Γ w v) =ᵐ[m] fun x =>
        ∑ i, tensorInterpCoeff (K := K) a δ F i (fun j => D.toCapacity.toLp (f j) x) *
          G.Γ (f i) v x := by
  classical
  choose p hp hr hγ using fun z : Fin n → Fin (K + 1) => D.centered_cell hL G f a hδ z
  have hs := D.centered_chain_sum G Finset.univ f p (fun z => F (gridNode a δ z))
    (cellWeight a δ) (rightCellSlope a δ) (fun z _ => hr z) (fun z _ => hγ z)
  exact ⟨∑ z, F (gridNode a δ z) • p z,
    D.toCapacity.bddSpace.sum_mem (fun z _ => D.toCapacity.bddSpace.smul_mem _ (hp z)), hs⟩

/--
Closure of already constructed multivariate approximants, with all analytic obligations explicit.
-/
theorem centered_chainRule_of_approximants (hL : D.Local) (G : D.CarreDuChamp) {n : ℕ}
    (f : Fin n → D.form.dom) (F : (Fin n → ℝ) → ℝ)
    (p : ℕ → D.toCapacity.Space) (w : Lp ℝ 2 m)
    (hw : ⇑w =ᵐ[m] fun x => F (fun i => (f i : Lp ℝ 2 m) x) - F 0)
    (a : ℕ → Fin n → X → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hT : Tendsto (fun k => D.toCapacity.toLp (p k)) atTop (𝓝 w))
    (ha : ∀ k i, ∀ᵐ x ∂m, |a k i x| ≤ B)
    (hd : ∀ i, ∀ᵐ x ∂m, Tendsto (fun k => a k i x) atTop
      (𝓝 (fderiv ℝ F (fun j => (f j : Lp ℝ 2 m) x) (Pi.single i 1))))
    (hγ : ∀ k v, ⇑(G.Γ (p k) v) =ᵐ[m] fun x =>
      ∑ i, a k i x * G.Γ (D.form.formToDomain.symm (f i)) v x) :
    ∃ q : D.form.dom,
      (⇑(q : Lp ℝ 2 m) =ᵐ[m] fun x => F (fun i => (f i : Lp ℝ 2 m) x) - F 0) ∧
      Tendsto p atTop (𝓝 (D.form.formToDomain.symm q)) ∧
      ∀ v : D.form.dom,
        ⇑(G.Γ (D.form.formToDomain.symm q) (D.form.formToDomain.symm v)) =ᵐ[m]
          fun x => ∑ i, fderiv ℝ F (fun j => (f j : Lp ℝ 2 m) x) (Pi.single i 1) *
            G.Γ (D.form.formToDomain.symm (f i)) (D.form.formToDomain.symm v) x := by
  obtain ⟨q, hq, ht, hg⟩ := D.chain_coefficients_closed hL G
    (fun i => D.form.formToDomain.symm (f i)) p w a
    (fun i x => fderiv ℝ F (fun j => (f j : Lp ℝ 2 m) x) (Pi.single i 1))
    hB hT ha hd hγ
  refine ⟨D.form.formToDomain q, ?_, ?_, ?_⟩
  · change ⇑(D.toCapacity.toLp q) =ᵐ[m] _
    rwa [hq]
  · simpa only [LinearEquiv.symm_apply_apply] using ht
  · intro v
    simpa only [LinearEquiv.symm_apply_apply] using hg (D.form.formToDomain.symm v)

/-- A centered chain specifies both its domain representative and every mixed Gamma identity. -/
def CenteredGammaChain {n : ℕ} (G : D.CarreDuChamp) (f : Fin n → D.toCapacity.Space)
    (P : (Fin n → ℝ) → ℝ) (c : Fin n → (Fin n → ℝ) → ℝ) : Prop :=
  ∃ p : D.toCapacity.Space,
    (⇑(D.toCapacity.toLp p) =ᵐ[m] fun x => P (fun j => D.toCapacity.toLp (f j) x) - P 0) ∧
    ∀ v, ⇑(G.Γ p v) =ᵐ[m] fun x =>
      ∑ i, c i (fun j => D.toCapacity.toLp (f j) x) * G.Γ (f i) v x

/-- Centering any constant produces the zero element of the original domain. -/
theorem centeredGammaChain_const {n : ℕ} (G : D.CarreDuChamp)
    (f : Fin n → D.toCapacity.Space) (r : ℝ) :
    D.CenteredGammaChain G f (fun _ => r) (fun _ _ => 0) := by
  refine ⟨0, ?_, fun v => ?_⟩
  · simp only [map_zero, sub_self]
    filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx
    exact hx
  · simp only [map_zero, zero_apply, zero_mul, Finset.sum_const_zero]
    filter_upwards [Lp.coeFn_zero ℝ 1 m] with x hx
    exact hx

/-- Coordinate evaluation is already centered at the origin. -/
theorem centeredGammaChain_coord {n : ℕ} (G : D.CarreDuChamp)
    (f : Fin n → D.toCapacity.Space) (i : Fin n) :
    D.CenteredGammaChain G f (fun y => y i) (fun j _ => if j = i then 1 else 0) := by
  refine ⟨f i, ae_of_all _ (fun x => by simp), fun v => ae_of_all _ (fun x => ?_)⟩
  simp

/-- Addition of centered chains preserves their explicit coefficient functions. -/
theorem CenteredGammaChain.add {n : ℕ} {G : D.CarreDuChamp} {f : Fin n → D.toCapacity.Space}
    {P Q : (Fin n → ℝ) → ℝ} {c d : Fin n → (Fin n → ℝ) → ℝ}
    (hP : D.CenteredGammaChain G f P c) (hQ : D.CenteredGammaChain G f Q d) :
    D.CenteredGammaChain G f (fun y => P y + Q y) (fun i y => c i y + d i y) := by
  obtain ⟨p, hp, hpg⟩ := hP
  obtain ⟨q, hq, hqg⟩ := hQ
  refine ⟨p + q, ?_, fun v => ?_⟩
  · rw [map_add]
    filter_upwards [Lp.coeFn_add (D.toCapacity.toLp p) (D.toCapacity.toLp q), hp, hq]
      with x hx h1 h2
    rw [hx, Pi.add_apply, h1, h2]
    ring
  · simp only [map_add, add_apply]
    filter_upwards [Lp.coeFn_add (G.Γ p v) (G.Γ q v), hpg v, hqg v] with x hx h1 h2
    rw [hx, Pi.add_apply, h1, h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Scalar multiplication commutes with centering and the chain coefficients. -/
theorem CenteredGammaChain.const_mul {n : ℕ} {G : D.CarreDuChamp} {f : Fin n → D.toCapacity.Space}
    {P : (Fin n → ℝ) → ℝ} {c : Fin n → (Fin n → ℝ) → ℝ}
    (hP : D.CenteredGammaChain G f P c) (r : ℝ) :
    D.CenteredGammaChain G f (fun y => r * P y) (fun i y => r * c i y) := by
  obtain ⟨p, hp, hpg⟩ := hP
  refine ⟨r • p, ?_, fun v => ?_⟩
  · rw [map_smul]
    filter_upwards [Lp.coeFn_smul r (D.toCapacity.toLp p), hp] with x hx h1
    rw [hx, Pi.smul_apply, smul_eq_mul, h1]
    ring
  · simp only [map_smul, smul_apply]
    filter_upwards [Lp.coeFn_smul r (G.Γ p v), hpg v] with x hx h1
    rw [hx, Pi.smul_apply, smul_eq_mul, h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Equal profiles and coefficients give the same centered chain assertion. -/
theorem CenteredGammaChain.congr {n : ℕ} {G : D.CarreDuChamp} {f : Fin n → D.toCapacity.Space}
    {P Q : (Fin n → ℝ) → ℝ} {c d : Fin n → (Fin n → ℝ) → ℝ}
    (hP : D.CenteredGammaChain G f P c) (hPQ : ∀ y, P y = Q y) (hcd : ∀ i y, c i y = d i y) :
    D.CenteredGammaChain G f Q d := by
  have eP : P = Q := funext hPQ
  have ec : c = d := funext fun i => funext (hcd i)
  subst eP ec
  exact hP

/-- A finite sum of centered chains is formed inside the original domain. -/
theorem CenteredGammaChain.sum {n : ℕ} {G : D.CarreDuChamp} {f : Fin n → D.toCapacity.Space}
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {P : ι → (Fin n → ℝ) → ℝ} {c : ι → Fin n → (Fin n → ℝ) → ℝ}
    (hP : ∀ j ∈ s, D.CenteredGammaChain G f (P j) (c j)) :
    D.CenteredGammaChain G f (fun y => ∑ j ∈ s, P j y) (fun i y => ∑ j ∈ s, c j i y) := by
  induction s using Finset.induction_on with
  | empty => exact (D.centeredGammaChain_const G f 0).congr D (by simp) (by simp)
  | @insert j s hj ih =>
    exact ((hP j (Finset.mem_insert_self _ _)).add D
      (ih fun k hk => hP k (Finset.mem_insert_of_mem hk))).congr D
        (fun y => by rw [Finset.sum_insert hj]) (fun i y => by rw [Finset.sum_insert hj])

/-- Bounded translated products yield the centered Leibniz rule for arbitrary profiles. -/
theorem CenteredGammaChain.mul {n : ℕ} {G : D.CarreDuChamp} {f : Fin n → D.toCapacity.Space}
    (hL : D.Local) {P Q : (Fin n → ℝ) → ℝ} {c d : Fin n → (Fin n → ℝ) → ℝ}
    (hP : D.CenteredGammaChain G f P c) (hQ : D.CenteredGammaChain G f Q d)
    {C E : ℝ} (hC : ∀ᵐ x ∂m, |P (fun i => D.toCapacity.toLp (f i) x)| ≤ C)
    (hE : ∀ᵐ x ∂m, |Q (fun i => D.toCapacity.toLp (f i) x)| ≤ E) :
    D.CenteredGammaChain G f (fun y => P y * Q y) (fun i y => P y * d i y + Q y * c i y) := by
  obtain ⟨p, hp, hpg⟩ := hP
  obtain ⟨q, hq, hqg⟩ := hQ
  have hpb : p ∈ D.toCapacity.bddSpace := by
    refine ⟨C + |P 0|, ?_⟩
    filter_upwards [hp, hC] with x hx hb
    rw [hx]
    exact (abs_sub _ _).trans (add_le_add hb le_rfl)
  have hqb : q ∈ D.toCapacity.bddSpace := by
    refine ⟨E + |Q 0|, ?_⟩
    filter_upwards [hq, hE] with x hx hb
    rw [hx]
    exact (abs_sub _ _).trans (add_le_add hb le_rfl)
  obtain ⟨w, -, hw, hwg⟩ := D.centered_translated_mul hL G p q hpb hqb (P 0) (Q 0)
  refine ⟨w, ?_, fun v => ?_⟩
  · filter_upwards [hw, hp, hq] with x hx h1 h2
    simpa only [h1, h2, sub_add_cancel] using hx
  · filter_upwards [hwg v, hp, hq, hpg v, hqg v] with x hx h1 h2 h3 h4
    rw [hx, h1, h2, sub_add_cancel, sub_add_cancel, h3, h4,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The open-slope hat identity is retained for the affine-corrected tensor interpolants. -/
theorem gamma_centeredHat (hL : D.Local) (G : D.CarreDuChamp)
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (v w : D.toCapacity.Space) :
    ⇑(G.Γ (D.centeredHat a δ v) w) =ᵐ[m] fun x =>
      gridHatSlope a δ (D.toCapacity.toLp v x) * G.Γ v w x := by
  simp only [centeredHat, map_smul, map_sub, smul_apply, sub_apply]
  filter_upwards [Lp.coeFn_smul δ⁻¹
      (G.Γ (D.centeredClamp (a - δ) a v) w - G.Γ (D.centeredClamp a (a + δ) v) w),
    Lp.coeFn_sub (G.Γ (D.centeredClamp (a - δ) a v) w)
      (G.Γ (D.centeredClamp a (a + δ) v) w),
    D.gamma_centeredClamp hL G (a - δ) a (by linarith) v w,
    D.gamma_centeredClamp hL G a (a + δ) (by linarith) v w]
      with x h1 h2 h3 h4
  rw [h1, Pi.smul_apply, smul_eq_mul, h2, Pi.sub_apply, h3, h4]
  unfold gridHatSlope
  ring

/--
Tensor cells also have the open-slope identity used by the existing real approximation estimates.
-/
theorem centeredGammaChain_cell (hL : D.Local) (G : D.CarreDuChamp) {n K : ℕ}
    (f : Fin n → D.toCapacity.Space) (a : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (z : Fin n → Fin (K + 1)) :
    D.CenteredGammaChain G f (cellWeight a δ z) (cellSlope a δ z) := by
  classical
  obtain ⟨w, -, hw, hγ⟩ := D.centered_chain_tensor hL G f
    (fun i => D.centeredHat (gridNode a δ z i) δ (f i))
    (fun i => gridHat (gridNode a δ z i) δ) (fun i => gridHatSlope (gridNode a δ z i) δ)
    (fun i => D.centeredHat_bounded _ hδ _)
    (fun i => D.coe_centeredHat _ _ _) (fun i v => D.gamma_centeredHat hL G _ hδ _ v)
  refine ⟨w, hw, fun v => ?_⟩
  filter_upwards [hγ v] with x hx
  rw [hx]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [cellSlope, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl]
  have he : (∏ j ∈ Finset.univ.erase i,
      if j = i then gridHatSlope (gridNode a δ z j) δ (D.toCapacity.toLp (f j) x)
      else gridHat (gridNode a δ z j) δ (D.toCapacity.toLp (f j) x)) =
      ∏ j ∈ Finset.univ.erase i, gridHat (gridNode a δ z j) δ (D.toCapacity.toLp (f j) x) :=
    Finset.prod_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)
  rw [he, mul_comm]

/-- Affine profiles center to finite linear combinations of the coordinates. -/
theorem centeredGammaChain_affine {n : ℕ} (G : D.CarreDuChamp)
    (f : Fin n → D.toCapacity.Space) (A : ℝ) (B z : Fin n → ℝ) :
    D.CenteredGammaChain G f (fun y => A + ∑ i, B i * (y i - z i)) (fun i _ => B i) := by
  classical
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      D.CenteredGammaChain G f (fun y => B i * (y i - z i))
        (fun j _ => B i * (if j = i then 1 else 0)) := fun i _ =>
    ((((D.centeredGammaChain_coord G f i).add D (D.centeredGammaChain_const G f (-z i))).const_mul D
      (B i)).congr D (fun y => by ring) (fun j y => by ring))
  exact ((D.centeredGammaChain_const G f A).add D (CenteredGammaChain.sum D Finset.univ hi)).congr D
    (fun y => rfl) (fun j y => by simp)

/-- The existing affine-corrected tensor interpolant has a centered domain representative. -/
theorem centeredGammaChain_boxApprox (hL : D.Local) (G : D.CarreDuChamp) {n K : ℕ}
    (f : Fin n → D.toCapacity.Space) {M : ℝ}
    (hf : ∀ i, ∀ᵐ x ∂m, |D.toCapacity.toLp (f i) x| ≤ M)
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (A : (Fin n → Fin (K + 1)) → ℝ) (B : (Fin n → Fin (K + 1)) → Fin n → ℝ) :
    D.CenteredGammaChain G f (boxApprox a δ A B) (boxApproxCoeff a δ A B) := by
  classical
  have hk : ∀ z ∈ (Finset.univ : Finset (Fin n → Fin (K + 1))),
      D.CenteredGammaChain G f (fun y => cellWeight a δ z y * cellAffine a δ A B z y)
        (fun i y => cellWeight a δ z y * B z i + cellAffine a δ A B z y * cellSlope a δ z i y) := by
    intro z _
    apply (D.centeredGammaChain_cell hL G f a hδ z).mul D hL
      (D.centeredGammaChain_affine G f (A z) (B z) (gridNode a δ z))
    · apply ae_of_all
      intro x
      rw [cellWeight, abs_of_nonneg (Finset.prod_nonneg fun i _ => gridHat_nonneg hδ _ _)]
      exact Finset.prod_le_one (fun i _ => gridHat_nonneg hδ _ _) (fun i _ => gridHat_le_one hδ _ _)
    · filter_upwards [ae_all_iff.2 hf] with x hx
      exact abs_affine_le (A z) (B z) (gridNode a δ z) _ hx
  exact (CenteredGammaChain.sum D Finset.univ hk).congr D (fun y => rfl)
    (fun i y => Finset.sum_congr rfl fun z _ => by ring)

/-- Every centered Lipschitz composition has an L2 class on an arbitrary source measure. -/
theorem exists_centered_composition {n : ℕ} (f : Fin n → D.toCapacity.Space)
    {F : (Fin n → ℝ) → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) :
    ∃ w : Lp ℝ 2 m, ⇑w =ᵐ[m] fun x => F (fun i => D.toCapacity.toLp (f i) x) - F 0 := by
  classical
  let q : Lp ℝ 2 m := (L : ℝ) • ∑ i, |D.toCapacity.toLp (f i)|
  have hq : ⇑q =ᵐ[m] fun x => (L : ℝ) * ∑ i, |D.toCapacity.toLp (f i) x| := by
    filter_upwards [Lp.coeFn_smul (L : ℝ) (∑ i, |D.toCapacity.toLp (f i)|),
      lp_coeFn_sum Finset.univ (fun i => |D.toCapacity.toLp (f i)|),
      ae_all_iff.2 fun i => Lp.coeFn_abs (D.toCapacity.toLp (f i))] with x h1 h2 h3
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
    simp only [h3]
  have hm : MemLp (fun x => F (fun i => D.toCapacity.toLp (f i) x) - F 0) 2 m := by
    apply (Lp.memLp q).mono
      ((hF.continuous.measurable.comp (measurable_pi_lambda _ fun i =>
        (Lp.stronglyMeasurable _).measurable)).sub measurable_const).aestronglyMeasurable
    filter_upwards [hq] with x hx
    change |F (fun i => D.toCapacity.toLp (f i) x) - F 0| ≤ |q x|
    rw [hx, abs_of_nonneg (show 0 ≤ (L : ℝ) * ∑ i, |D.toCapacity.toLp (f i) x| by positivity)]
    have hb := hF.dist_le_mul (fun i => D.toCapacity.toLp (f i) x) 0
    rw [Real.dist_eq] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ L.2)
    apply (dist_pi_le_iff (by positivity)).2
    intro i
    simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using
      Finset.single_le_sum (fun j _ => abs_nonneg (D.toCapacity.toLp (f j) x)) (Finset.mem_univ i)
  exact ⟨hm.toLp _, hm.coeFn_toLp⟩

/-- Tensor approximation closes on bounded coordinates with an L2 control of their nonzero set. -/
theorem centeredGammaChain_of_support_control (hLocal : D.Local) (G : D.CarreDuChamp)
    {n : ℕ} (f : Fin n → D.toCapacity.Space) {M : ℝ}
    (hf : ∀ i, ∀ᵐ x ∂m, |D.toCapacity.toLp (f i) x| ≤ M)
    (q : Lp ℝ 2 m)
    (hq : ∀ᵐ x ∂m, (∀ i, D.toCapacity.toLp (f i) x = 0) ∨ 1 ≤ |q x|)
    {F : (Fin n → ℝ) → ℝ} {L : ℝ≥0} (hC : ContDiff ℝ 1 F) (hLip : LipschitzWith L F) :
    D.CenteredGammaChain G f F (fun i y => fderiv ℝ F y (Pi.single i 1)) := by
  have hR : (0 : ℝ) < |M| + 1 := by positivity
  have hbox : ∀ᵐ x ∂m, ∀ i, |D.toCapacity.toLp (f i) x| ≤ |M| + 1 := by
    filter_upwards [ae_all_iff.2 hf] with x hx i
    linarith [hx i, le_abs_self M]
  have hzero : ∀ i : Fin n, |(0 : Fin n → ℝ) i| ≤ |M| + 1 := fun i => by simp; positivity
  obtain ⟨N, hN⟩ := exists_abs_gridBoxApproxCoeff_sub_le hC hR one_pos
  have hch : ∀ k, D.CenteredGammaChain G f (gridBoxApprox F (|M| + 1) k)
      (gridBoxApproxCoeff F (|M| + 1) k) :=
    fun k => D.centeredGammaChain_boxApprox hLocal G f hf _ (boxGridStep_pos hR k) _ _
  choose p hp hγ using hch
  obtain ⟨w, hw⟩ := D.exists_centered_composition f hLip
  have hdelta : ∀ k, boxGridStep (|M| + 1) k ≤ 2 * (|M| + 1) := by
    intro k
    unfold boxGridStep
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).2
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have herr : ∀ k, ∀ᵐ x ∂m,
      |D.toCapacity.toLp (p (k + N)) x - w x| ≤ 2 * boxGridStep (|M| + 1) (k + N) := by
    intro k
    filter_upwards [hp (k + N), hw, hbox] with x hx hwx hb
    rw [hx, hwx]
    have h1 := (hN (k + N) (Nat.le_add_left _ _) _ hb).2
    have h2 := (hN (k + N) (Nat.le_add_left _ _) 0 hzero).2
    have he := abs_sub
      (gridBoxApprox F (|M| + 1) (k + N) (fun i => D.toCapacity.toLp (f i) x) -
        F (fun i => D.toCapacity.toLp (f i) x))
      (gridBoxApprox F (|M| + 1) (k + N) 0 - F 0)
    have heq : gridBoxApprox F (|M| + 1) (k + N) (fun i => D.toCapacity.toLp (f i) x) -
          gridBoxApprox F (|M| + 1) (k + N) 0 -
          (F (fun i => D.toCapacity.toLp (f i) x) - F 0) =
        (gridBoxApprox F (|M| + 1) (k + N) (fun i => D.toCapacity.toLp (f i) x) -
          F (fun i => D.toCapacity.toLp (f i) x)) -
          (gridBoxApprox F (|M| + 1) (k + N) 0 - F 0) := by ring
    rw [heq]
    linarith
  have hT0 : Tendsto (fun k => D.toCapacity.toLp (p (k + N)) - w) atTop (𝓝 0) := by
    apply lp_two_tendsto_zero_of_dominated _ ((4 * (|M| + 1)) • q)
    · intro k
      filter_upwards [Lp.coeFn_sub (D.toCapacity.toLp (p (k + N))) w,
        Lp.coeFn_smul (4 * (|M| + 1)) q, hp (k + N), hw, herr k, hq]
          with x hs hsm hpw hww her hsupp
      rw [hs, Pi.sub_apply, hsm, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ 4 * (|M| + 1))]
      rcases hsupp with hz | hq1
      · have hvec : (fun i => D.toCapacity.toLp (f i) x) = 0 := funext hz
        rw [hpw, hww, hvec, sub_self, sub_self, sub_self, abs_zero]
        positivity
      · calc
          _ ≤ 2 * boxGridStep (|M| + 1) (k + N) := her
          _ ≤ 4 * (|M| + 1) := by linarith [hdelta (k + N)]
          _ ≤ 4 * (|M| + 1) * |q x| := le_mul_of_one_le_right (by positivity) hq1
    · filter_upwards [ae_all_iff.2 herr,
        ae_all_iff.2 fun k => Lp.coeFn_sub (D.toCapacity.toLp (p (k + N))) w]
          with x her hs
      have hz : Tendsto (fun k => 2 * boxGridStep (|M| + 1) (k + N)) atTop (𝓝 0) := by
        simpa using ((tendsto_boxGridStep (|M| + 1)).comp (tendsto_add_atTop_nat N)).const_mul 2
      have hzneg : Tendsto (fun k => -(2 * boxGridStep (|M| + 1) (k + N))) atTop (𝓝 0) := by
        simpa only [neg_zero] using hz.neg
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le hzneg hz
      · intro k
        dsimp only
        rw [hs k, Pi.sub_apply]
        exact (abs_le.1 (her k)).1
      · intro k
        dsimp only
        rw [hs k, Pi.sub_apply]
        exact (abs_le.1 (her k)).2
  have hT : Tendsto (fun k => D.toCapacity.toLp (p (k + N))) atTop (𝓝 w) := by
    simpa only [sub_add_cancel, zero_add] using hT0.add_const w
  have ha : ∀ k i, ∀ᵐ x ∂m,
      |gridBoxApproxCoeff F (|M| + 1) (k + N) i
        (fun j => D.toCapacity.toLp (f j) x)| ≤ (L : ℝ) + 3 := by
    intro k i
    filter_upwards [hbox] with x hx
    have h1 := (hN (k + N) (Nat.le_add_left _ _) _ hx).1 i
    have h2 := fderiv_coefficient_bound hLip (fun j => D.toCapacity.toLp (f j) x) i
    have h3 := abs_sub_abs_le_abs_sub
      (gridBoxApproxCoeff F (|M| + 1) (k + N) i (fun j => D.toCapacity.toLp (f j) x))
      (fderiv ℝ F (fun j => D.toCapacity.toLp (f j) x) (Pi.single i 1))
    linarith
  obtain ⟨v, hv, -, hvg⟩ := D.chain_coefficients_closed hLocal G f (fun k => p (k + N)) w
    (fun k i x => gridBoxApproxCoeff F (|M| + 1) (k + N) i (fun j => D.toCapacity.toLp (f j) x))
    (fun i x => fderiv ℝ F (fun j => D.toCapacity.toLp (f j) x) (Pi.single i 1))
    (by positivity : 0 ≤ (L : ℝ) + 3) hT ha
    (fun i => by
      filter_upwards [hbox] with x hx
      exact (tendsto_gridBoxApproxCoeff hC hR hx i).comp (tendsto_add_atTop_nat N))
    (fun k v => hγ (k + N) v)
  exact ⟨v, by rwa [hv], hvg⟩

/--
The residual has the expected chain coefficient, with arbitrary values at its two corner levels.
-/
theorem gamma_residual (hL : D.Local) (G : D.CarreDuChamp)
    (k : ℕ) (f g : D.toCapacity.Space) :
    ⇑(G.Γ (D.residual k f) g) =ᵐ[m] fun x =>
      (1 - (Set.Ioo (-((k : ℝ) + 1)⁻¹) ((k : ℝ) + 1)⁻¹).indicator 1
        (D.toCapacity.toLp f x)) * G.Γ f g x := by
  let ε : ℝ := ((k : ℝ) + 1)⁻¹
  have hε : 0 ≤ ε := by positivity
  have hzero : max (-ε) (min (0 : ℝ) ε) = 0 := by
    rw [min_eq_left hε, max_eq_right (neg_nonpos.mpr hε)]
  have he : D.residual k f = f - D.centeredClamp (-ε) ε f := by
    apply D.toCapacity.eq_of_ae
    rw [map_sub]
    filter_upwards [D.coe_residual k f, D.coe_centeredClamp (-ε) ε f,
      Lp.coeFn_sub (D.toCapacity.toLp f) (D.toCapacity.toLp (D.centeredClamp (-ε) ε f))]
        with x h1 h2 h3
    rw [h1, h3, Pi.sub_apply, h2, hzero, sub_zero]
    simp only [softThreshold, ε, max_comm]
  rw [he, map_sub, sub_apply]
  filter_upwards [Lp.coeFn_sub (G.Γ f g) (G.Γ (D.centeredClamp (-ε) ε f) g),
    D.gamma_centeredClamp hL G (-ε) ε (by linarith) f g] with x h1 h2
  rw [h1, Pi.sub_apply, h2]
  ring

/-- The scalar cutoff removes a neighborhood of zero and clips large values. -/
def trimProfile (k : ℕ) (t : ℝ) : ℝ :=
  max (-((k : ℝ) + 1)) (min (softThreshold ((k : ℝ) + 1)⁻¹ t) ((k : ℝ) + 1))

/-- The scalar cutoff coefficient is a product of two factors in the unit interval. -/
def trimSlope (k : ℕ) (t : ℝ) : ℝ :=
  (Set.Ioo (-((k : ℝ) + 1)) ((k : ℝ) + 1)).indicator 1
    (softThreshold ((k : ℝ) + 1)⁻¹ t) *
    (1 - (Set.Ioo (-((k : ℝ) + 1)⁻¹) ((k : ℝ) + 1)⁻¹).indicator 1 t)

/-- The cutoff is zero on a nontrivial interval around the origin. -/
theorem trimProfile_zero_of_abs_le (k : ℕ) {t : ℝ} (ht : |t| ≤ ((k : ℝ) + 1)⁻¹) :
    trimProfile k t = 0 := by
  have hM : 0 ≤ (k : ℝ) + 1 := by positivity
  have hz : softThreshold ((k : ℝ) + 1)⁻¹ t = 0 := by
    rw [softThreshold, min_eq_left (abs_le.1 ht).2, max_eq_left (abs_le.1 ht).1, sub_self]
  rw [trimProfile, hz, min_eq_left hM, max_eq_right (neg_nonpos.mpr hM)]

/-- Both the source magnitude and the clipping height bound the cutoff. -/
theorem trimProfile_bounds (k : ℕ) (t : ℝ) :
    |trimProfile k t| ≤ |t| ∧ |trimProfile k t| ≤ (k : ℝ) + 1 := by
  have hM : 0 ≤ (k : ℝ) + 1 := by positivity
  have he : |max (-((k : ℝ) + 1)) (min (softThreshold ((k : ℝ) + 1)⁻¹ t) ((k : ℝ) + 1))| ≤
      |softThreshold ((k : ℝ) + 1)⁻¹ t| := by
    rw [abs_le]
    constructor
    · exact (le_min (neg_abs_le _) ((neg_nonpos.mpr (abs_nonneg _)).trans hM)).trans
        (le_max_right _ _)
    · apply max_le
      · exact (neg_nonpos.mpr hM).trans (abs_nonneg _)
      · exact (min_le_left _ _).trans (le_abs_self _)
  refine ⟨he.trans (abs_softThreshold_le (by positivity) t), ?_⟩
  rw [trimProfile, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/-- Cutoff coefficients are bounded by one without a restriction on the source measure. -/
theorem abs_trimSlope_le (k : ℕ) (t : ℝ) : |trimSlope k t| ≤ 1 := by
  unfold trimSlope
  simp only [Set.indicator]
  split_ifs <;> norm_num

/-- At each fixed point, the cutoff values converge to that point. -/
theorem tendsto_trimProfile (t : ℝ) : Tendsto (fun k => trimProfile k t) atTop (𝓝 t) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |t|
  refine (tendsto_softThreshold t).congr' ?_
  filter_upwards [eventually_ge_atTop N] with k hk
  have hb : |softThreshold ((k : ℝ) + 1)⁻¹ t| ≤ (k : ℝ) + 1 := by
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith [abs_softThreshold_le (by positivity : (0 : ℝ) ≤ ((k : ℝ) + 1)⁻¹) t]
  rw [trimProfile, min_eq_left (abs_le.1 hb).2, max_eq_right (abs_le.1 hb).1]

/-- Away from zero the cutoff coefficient is eventually one. -/
theorem eventually_trimSlope_eq_one {t : ℝ} (ht : t ≠ 0) :
    ∀ᶠ k in atTop, trimSlope k t = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt |t|
  have he : ∀ᶠ k : ℕ in atTop, ((k : ℝ) + 1)⁻¹ < |t| := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds (abs_pos.mpr ht))
    simpa only [one_div] using h
  filter_upwards [eventually_ge_atTop N, he] with k hk he
  have hb : |softThreshold ((k : ℝ) + 1)⁻¹ t| < (k : ℝ) + 1 := by
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith [abs_softThreshold_le (by positivity : (0 : ℝ) ≤ ((k : ℝ) + 1)⁻¹) t]
  have hn : t ∉ Set.Ioo (-((k : ℝ) + 1)⁻¹) ((k : ℝ) + 1)⁻¹ := by
    intro h
    have h' := abs_lt.mpr h
    linarith
  rw [trimSlope, Set.indicator_of_mem (show softThreshold ((k : ℝ) + 1)⁻¹ t ∈
    Set.Ioo (-((k : ℝ) + 1)) ((k : ℝ) + 1) from abs_lt.mp hb), Set.indicator_of_notMem hn]
  norm_num

/-- The two scalar cutoff operations are carried out in the original BH form space. -/
def trimElem (k : ℕ) (f : D.toCapacity.Space) : D.toCapacity.Space :=
  D.centeredClamp (-((k : ℝ) + 1)) ((k : ℝ) + 1) (D.residual k f)

/-- The form cutoff has the prescribed pointwise representative. -/
theorem coe_trimElem (k : ℕ) (f : D.toCapacity.Space) :
    ⇑(D.toCapacity.toLp (D.trimElem k f)) =ᵐ[m] fun x => trimProfile k (D.toCapacity.toLp f x) := by
  have hM : 0 ≤ (k : ℝ) + 1 := by positivity
  filter_upwards [D.coe_centeredClamp (-((k : ℝ) + 1)) ((k : ℝ) + 1) (D.residual k f),
    D.coe_residual k f] with x h1 h2
  change D.toCapacity.toLp (D.trimElem k f) x = _ at h1
  rw [h1, h2, min_eq_left hM, max_eq_right (neg_nonpos.mpr hM), sub_zero]
  rfl

/-- The two scalar chain identities give the cutoff coefficient exactly. -/
theorem gamma_trimElem (hL : D.Local) (G : D.CarreDuChamp)
    (k : ℕ) (f g : D.toCapacity.Space) :
    ⇑(G.Γ (D.trimElem k f) g) =ᵐ[m] fun x => trimSlope k (D.toCapacity.toLp f x) * G.Γ f g x := by
  filter_upwards [D.gamma_centeredClamp hL G (-((k : ℝ) + 1)) ((k : ℝ) + 1)
    (by linarith [Nat.cast_nonneg (α := ℝ) k]) (D.residual k f) g,
    D.coe_residual k f, D.gamma_residual hL G k f g]
      with x h1 h2 h3
  change G.Γ (D.trimElem k f) g x = _ at h1
  rw [h1, h2, h3, trimSlope, mul_assoc]

/-- A finite family of cutoffs admits an L2 majorant of the indicator of its nonzero set. -/
theorem trimElem_support_control {n : ℕ} (f : Fin n → D.toCapacity.Space) (k : ℕ) :
    ∃ q : Lp ℝ 2 m, ∀ᵐ x ∂m,
      (∀ i, D.toCapacity.toLp (D.trimElem k (f i)) x = 0) ∨ 1 ≤ |q x| := by
  classical
  let q : Lp ℝ 2 m := ((k : ℝ) + 1) • ∑ i, |D.toCapacity.toLp (f i)|
  refine ⟨q, ?_⟩
  filter_upwards [Lp.coeFn_smul ((k : ℝ) + 1) (∑ i, |D.toCapacity.toLp (f i)|),
    lp_coeFn_sum Finset.univ (fun i => |D.toCapacity.toLp (f i)|),
    ae_all_iff.2 fun i => Lp.coeFn_abs (D.toCapacity.toLp (f i)),
    ae_all_iff.2 fun i => D.coe_trimElem k (f i)] with x h1 h2 h3 h4
  by_cases h : ∀ i, |D.toCapacity.toLp (f i) x| ≤ ((k : ℝ) + 1)⁻¹
  · exact Or.inl fun i => (h4 i).trans (trimProfile_zero_of_abs_le k (h i))
  · push Not at h
    obtain ⟨i, hi⟩ := h
    right
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
    simp only [h3]
    rw [abs_of_nonneg (by positivity)]
    have hsum := Finset.single_le_sum
      (fun j _ => abs_nonneg (D.toCapacity.toLp (f j) x)) (Finset.mem_univ i)
    have hM : 0 < (k : ℝ) + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_left (hi.le.trans hsum) hM.le
    simpa only [mul_inv_cancel₀ hM.ne'] using hmul

/--
Centered C1 Lipschitz chains on the arbitrary BH measure, after removing the scalar cutoffs.

Bouleau--Hirsch (1991), chapter I, pp. 36--37; EID formulation in ch. V, p. 185; Notes p. 302.
-/
theorem centeredGammaChain_fderiv (hLocal : D.Local) (G : D.CarreDuChamp)
    {n : ℕ} (f : Fin n → D.toCapacity.Space)
    {F : (Fin n → ℝ) → ℝ} {L : ℝ≥0} (hC : ContDiff ℝ 1 F) (hLip : LipschitzWith L F) :
    D.CenteredGammaChain G f F (fun i y => fderiv ℝ F y (Pi.single i 1)) := by
  classical
  let u : ℕ → Fin n → D.toCapacity.Space := fun k i => D.trimElem k (f i)
  have hu : ∀ k i, ⇑(D.toCapacity.toLp (u k i)) =ᵐ[m]
      fun x => trimProfile k (D.toCapacity.toLp (f i) x) :=
    fun k i => D.coe_trimElem k (f i)
  have hch : ∀ k, D.CenteredGammaChain G (u k) F (fun i y => fderiv ℝ F y (Pi.single i 1)) := by
    intro k
    obtain ⟨q, hq⟩ := D.trimElem_support_control f k
    apply D.centeredGammaChain_of_support_control hLocal G (u k) (M := (k : ℝ) + 1) _ q hq hC hLip
    intro i
    filter_upwards [hu k i] with x hx
    rw [hx]
    exact (trimProfile_bounds k _).2
  choose p hp hγ using hch
  obtain ⟨w, hw⟩ := D.exists_centered_composition f hLip
  let b : ℕ → Fin n → X → ℝ := fun k i x =>
    if D.toCapacity.toLp (f i) x = 0 then
      fderiv ℝ F (fun j => D.toCapacity.toLp (f j) x) (Pi.single i 1)
    else fderiv ℝ F (fun j => D.toCapacity.toLp (u k j) x) (Pi.single i 1) *
      trimSlope k (D.toCapacity.toLp (f i) x)
  have hb : ∀ k i, ∀ᵐ x ∂m, |b k i x| ≤ (L : ℝ) := by
    intro k i
    apply ae_of_all
    intro x
    dsimp only [b]
    split_ifs with hz
    · exact fderiv_coefficient_bound hLip _ i
    · rw [abs_mul]
      exact (mul_le_mul (fderiv_coefficient_bound hLip _ i) (abs_trimSlope_le k _)
        (abs_nonneg _) L.2).trans_eq (mul_one _)
  have hbγ : ∀ k v, ⇑(G.Γ (p k) v) =ᵐ[m] fun x => ∑ i, b k i x * G.Γ (f i) v x := by
    intro k v
    filter_upwards [hγ k v, ae_all_iff.2 fun i => D.gamma_trimElem hLocal G k (f i) v,
      ae_all_iff.2 fun i => D.gamma_eq_zero_on_level_space hLocal G (f i) v 0]
        with x hx hg hz
    rw [hx]
    apply Finset.sum_congr rfl
    intro i _
    change fderiv ℝ F (fun j => D.toCapacity.toLp (u k j) x) (Pi.single i 1) *
      G.Γ (D.trimElem k (f i)) v x = _
    rw [hg i]
    dsimp only [b]
    by_cases hi : D.toCapacity.toLp (f i) x = 0
    · rw [if_pos hi, hz i hi]; ring
    · rw [if_neg hi, mul_assoc]
  have hulim : ∀ᵐ x ∂m, Tendsto (fun k => fun j => D.toCapacity.toLp (u k j) x) atTop
      (𝓝 (fun j => D.toCapacity.toLp (f j) x)) := by
    filter_upwards [ae_all_iff.2 fun k => ae_all_iff.2 (hu k)] with x hx
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [hx] using tendsto_trimProfile (D.toCapacity.toLp (f j) x)
  have hblim : ∀ i, ∀ᵐ x ∂m, Tendsto (fun k => b k i x) atTop
      (𝓝 (fderiv ℝ F (fun j => D.toCapacity.toLp (f j) x) (Pi.single i 1))) := by
    intro i
    filter_upwards [hulim] with x hx
    by_cases hi : D.toCapacity.toLp (f i) x = 0
    · simpa only [b, if_pos hi] using
        (tendsto_const_nhds (x := fderiv ℝ F (fun j => D.toCapacity.toLp (f j) x) (Pi.single i 1)))
    · have hd : Continuous (fun y => fderiv ℝ F y (Pi.single i 1)) :=
        (hC.continuous_fderiv one_ne_zero).clm_apply continuous_const
      have hc : Tendsto (fun k => trimSlope k (D.toCapacity.toLp (f i) x)) atTop (𝓝 (1 : ℝ)) :=
        tendsto_const_nhds.congr' ((eventually_trimSlope_eq_one hi).mono fun k hk => hk.symm)
      simpa only [b, if_neg hi, mul_one, Function.comp_apply] using ((hd.tendsto _).comp hx).mul hc
  have hdom : MemLp (fun x => (L : ℝ) * ∑ i, |D.toCapacity.toLp (f i) x|) 2 m := by
    have hs : MemLp (fun x => ∑ i, |D.toCapacity.toLp (f i) x|) 2 m := by
      have he : ⇑(∑ i, |D.toCapacity.toLp (f i)| : Lp ℝ 2 m) =ᵐ[m]
          fun x => ∑ i, |D.toCapacity.toLp (f i) x| := by
        filter_upwards [lp_coeFn_sum Finset.univ (fun i => |D.toCapacity.toLp (f i)|),
          ae_all_iff.2 fun i => Lp.coeFn_abs (D.toCapacity.toLp (f i))] with x h1 h2
        rw [h1]
        simp only [h2]
      exact (memLp_congr_ae he).mp (Lp.memLp _)
    exact hs.const_mul _
  have hT : Tendsto (fun k => D.toCapacity.toLp (p k)) atTop (𝓝 w) := by
    have ht := Foundations.tendsto_toLp_dominated m
      (fun k => Lp.memLp (D.toCapacity.toLp (p k))) (Lp.memLp w) hdom
      (fun k => ?_) ?_
    · have he : ∀ z : Lp ℝ 2 m, (Lp.memLp z).toLp z = z := fun z => Lp.ext (Lp.memLp z).coeFn_toLp
      simpa only [he] using ht
    · filter_upwards [hp k, ae_all_iff.2 (hu k)] with x hx hux
      rw [hx, Real.norm_eq_abs]
      have hd := hLip.dist_le_mul (fun j => D.toCapacity.toLp (u k j) x) 0
      rw [Real.dist_eq] at hd
      refine hd.trans (mul_le_mul_of_nonneg_left ?_ L.2)
      apply (dist_pi_le_iff (by positivity)).2
      intro i
      rw [Real.dist_eq, Pi.zero_apply, sub_zero, hux i]
      exact (trimProfile_bounds k _).1.trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (D.toCapacity.toLp (f j) x))
          (Finset.mem_univ i))
    · filter_upwards [hw, ae_all_iff.2 hp, hulim] with x hwx hpx hx
      simpa only [hpx, hwx, Function.comp_apply] using
        ((hLip.continuous.tendsto _).comp hx).sub_const (F 0)
  obtain ⟨v, hv, -, hvg⟩ := D.chain_coefficients_closed hLocal G f p w b
    (fun i x => fderiv ℝ F (fun j => D.toCapacity.toLp (f j) x) (Pi.single i 1))
    L.2 hT hb hblim hbγ
  exact ⟨v, by rwa [hv], hvg⟩

/--
The exact centered multivariate BH chain rule, without a finiteness assumption on the measure.

Bouleau--Hirsch (1991), chapter I, pp. 36--37; EID formulation in ch. V, p. 185; Notes p. 302.
-/
theorem centered_chainRule :
  D.Local → ∀ (G : D.CarreDuChamp) {n : ℕ}, 0 < n →
    ∀ (f : Fin n → D.form.dom) (F : (Fin n → ℝ) → ℝ) (L : ℝ≥0),
      ContDiff ℝ 1 F → LipschitzWith L F →
      ∃ w : D.form.dom,
        (⇑(w : Lp ℝ 2 m) =ᵐ[m] fun x => F (fun i => (f i : Lp ℝ 2 m) x) - F 0) ∧
        ∀ g : D.form.dom,
          ⇑(G.Γ (D.form.formToDomain.symm w) (D.form.formToDomain.symm g)) =ᵐ[m]
            fun x => ∑ i, fderiv ℝ F (fun j => (f j : Lp ℝ 2 m) x) (Pi.single i 1) *
              G.Γ (D.form.formToDomain.symm (f i)) (D.form.formToDomain.symm g) x := by
  intro hL G n _hn f F L hC hLip
  obtain ⟨w, hw, hγ⟩ := D.centeredGammaChain_fderiv hL G
    (fun i => D.form.formToDomain.symm (f i)) hC hLip
  refine ⟨D.form.formToDomain w, hw, fun g => ?_⟩
  change ⇑(G.Γ w (D.form.formToDomain.symm g)) =ᵐ[m] _
  exact hγ (D.form.formToDomain.symm g)

/-- A C1 Lipschitz function agrees in value and differential with the given C1 function on a box. -/
theorem exists_centered_box_cutoff {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : ContDiff ℝ 1 F) (M : ℝ) (hM : 0 ≤ M) :
    ∃ Q : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 Q ∧ (∃ L, LipschitzWith L Q) ∧
      ∀ y, (∀ i, |y i| ≤ M) → Q y = F y ∧ fderiv ℝ Q y = fderiv ℝ F y := by
  let χ : ContDiffBump (0 : Fin n → ℝ) := ⟨M + 1, M + 2, by linarith, by linarith⟩
  let Q : (Fin n → ℝ) → ℝ := fun y => χ y * F y
  have hQ : ContDiff ℝ 1 Q := χ.contDiff.mul hF
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport χ.hasCompactSupport.mul_right hQ
    (by norm_num)
  refine ⟨Q, hQ, ⟨L, hL⟩, fun y hy => ?_⟩
  have hn : ‖y‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr fun i => by
    simpa only [Real.norm_eq_abs] using hy i
  have hb : y ∈ Metric.ball 0 χ.rIn := by
    simp only [Metric.mem_ball, dist_zero_right]
    change ‖y‖ < M + 1
    linarith
  have he : Q =ᶠ[𝓝 y] F := by
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hb] with z hz
    change χ z * F z = F z
    change χ z = 1 at hz
    rw [hz, one_mul]
  exact ⟨he.eq_of_nhds, he.fderiv_eq⟩

/--
The bounded-coordinate chain rule needs C1 regularity only; a compact cutoff supplies Lipschitzness.

Bouleau--Hirsch (1991), chapter I, pp. 36--37; EID formulation in ch. V, p. 185; Notes p. 302.
-/
theorem centered_bounded_chainRule :
  D.Local → ∀ (G : D.CarreDuChamp) {n : ℕ}, 0 < n →
    ∀ (f : Fin n → D.form.dom), (∀ i, D.Bounded (f i)) →
    ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 F →
      ∃ w : D.form.dom,
        (⇑(w : Lp ℝ 2 m) =ᵐ[m] fun x => F (fun i => (f i : Lp ℝ 2 m) x) - F 0) ∧
        ∀ g : D.form.dom,
          ⇑(G.Γ (D.form.formToDomain.symm w) (D.form.formToDomain.symm g)) =ᵐ[m]
            fun x => ∑ i, fderiv ℝ F (fun j => (f j : Lp ℝ 2 m) x) (Pi.single i 1) *
              G.Γ (D.form.formToDomain.symm (f i)) (D.form.formToDomain.symm g) x := by
  intro hL G n hn f hb F hF
  classical
  choose C hC using hb
  let M : ℝ := ∑ i, |C i|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hbox : ∀ᵐ x ∂m, ∀ i, |(f i : Lp ℝ 2 m) x| ≤ M := by
    filter_upwards [ae_all_iff.2 hC] with x hx i
    have hi : C i ≤ M := (le_abs_self _).trans
      (Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i))
    have hxi : |(f i : Lp ℝ 2 m) x| ≤ C i := by simpa only [Real.norm_eq_abs] using hx i
    exact hxi.trans hi
  obtain ⟨Q, hQ, ⟨L, hLip⟩, hsame⟩ := exists_centered_box_cutoff F hF M hM
  have h0 := (hsame 0 (fun i => by simpa using hM)).1
  obtain ⟨w, hw, hγ⟩ := D.centered_chainRule hL G hn f Q L hQ hLip
  refine ⟨w, ?_, fun g => ?_⟩
  · filter_upwards [hw, hbox] with x hx hbx
    rw [hx, (hsame _ hbx).1, h0]
  · filter_upwards [hγ g, hbox] with x hx hbx
    rw [hx, (hsame _ hbx).2]

end DprBridge.BH1991.DirichletForm

namespace ErrorCalculus.PolarCurrent
variable {X : Type u} [MeasurableSpace X] {m : Measure X} {n : ℕ}

/-- A positive integrable source density defines a finite image measure. -/
theorem finite_image_density (f : X → (Fin n → ℝ)) (b : X → ℝ)
    (hb : Integrable b m) (hpos : ∀ x, 0 ≤ b x) :
    IsFiniteMeasure ((m.withDensity (fun x => ENNReal.ofReal (b x))).map f) := by
  haveI : IsFiniteMeasure (m.withDensity (fun x => ENNReal.ofReal (b x))) :=
    isFiniteMeasure_withDensity
      ((hasFiniteIntegral_iff_ofReal (ae_of_all _ hpos)).mp hb.hasFiniteIntegral).ne
  infer_instance

/-- Integration against a positive weighted image uses the original measure. -/
theorem integral_image_density (f : X → (Fin n → ℝ)) (hf : Measurable f)
    (b : X → ℝ) (hb : Measurable b) (hpos : ∀ x, 0 ≤ b x)
    (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ) :
    (∫ y, φ y ∂(m.withDensity (fun x => ENNReal.ofReal (b x))).map f) =
      ∫ x, φ (f x) * b x ∂m := by
  rw [integral_map hf.aemeasurable hφ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (μ := m)
      (f := fun x => ENNReal.ofReal (b x)) hb.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hpos x), smul_eq_mul, mul_comm]

/-- The total mass of the positive weighted image is its source integral. -/
theorem image_density_univ (f : X → (Fin n → ℝ)) (hf : Measurable f)
    (b : X → ℝ) (hb : Integrable b m) (hpos : ∀ x, 0 ≤ b x) :
    ((m.withDensity (fun x => ENNReal.ofReal (b x))).map f) Set.univ =
      ENNReal.ofReal (∫ x, b x ∂m) := by
  rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hb (ae_of_all _ hpos)]

/--
The positive divergence witness includes the negative part of the total mass at zero.

Eriksson-Bique--Murugan, Section 4.2 and Remark 4.12, p. 38; the boundary includes the Dirac
correction at zero.
-/
def recenteredPositive (f : X → (Fin n → ℝ)) (a : X → ℝ) (m : Measure X) :
    Measure (Fin n → ℝ) :=
  (m.withDensity (fun x => ENNReal.ofReal (max (a x) 0))).map f +
    ENNReal.ofReal (max (-(∫ x, a x ∂m)) 0) • Measure.dirac 0

/--
The negative divergence witness includes the positive part of the total mass at zero.

Eriksson-Bique--Murugan, Section 4.2 and Remark 4.12, p. 38; the boundary includes the Dirac
correction at zero.
-/
def recenteredNegative (f : X → (Fin n → ℝ)) (a : X → ℝ) (m : Measure X) :
    Measure (Fin n → ℝ) :=
  (m.withDensity (fun x => ENNReal.ofReal (max (-a x) 0))).map f +
    ENNReal.ofReal (max (∫ x, a x ∂m) 0) • Measure.dirac 0

/-- The nonnegative part of a real weight times a Dirac measure is finite. -/
theorem finite_dirac_real_weight (q : ℝ) (z : Fin n → ℝ) :
    IsFiniteMeasure (ENNReal.ofReal q • Measure.dirac z) := by
  constructor
  simp

/--
Both measures representing the recentered divergence are finite.

Eriksson-Bique--Murugan, Section 4.2 and Remark 4.12, p. 38; the boundary includes the Dirac
correction at zero.
-/
theorem recentered_finite (f : X → (Fin n → ℝ)) (a : X → ℝ) (ha : Integrable a m) :
    IsFiniteMeasure (recenteredPositive f a m) ∧
      IsFiniteMeasure (recenteredNegative f a m) := by
  haveI := finite_image_density f (fun x => max (a x) 0)
    (ha.sup (integrable_zero _ _ _)) (fun x => le_max_right _ _)
  haveI := finite_image_density f (fun x => max (-a x) 0)
    (ha.neg.sup (integrable_zero _ _ _)) (fun x => le_max_right _ _)
  haveI := finite_dirac_real_weight (max (-(∫ x, a x ∂m)) 0) (0 : Fin n → ℝ)
  haveI := finite_dirac_real_weight (max (∫ x, a x ∂m) 0) (0 : Fin n → ℝ)
  constructor
  · unfold recenteredPositive
    infer_instance
  · unfold recenteredNegative
    infer_instance

/--
The divergence witnesses have combined mass at most twice the L1 source mass.

Eriksson-Bique--Murugan, Section 4.2 and Remark 4.12, p. 38; the boundary includes the Dirac
correction at zero.
-/
theorem recentered_mass_bound (f : X → (Fin n → ℝ)) (hf : Measurable f)
    (a : X → ℝ) (ha : Integrable a m) :
    recenteredPositive f a m Set.univ + recenteredNegative f a m Set.univ ≤
      ENNReal.ofReal (2 * ∫ x, |a x| ∂m) := by
  have hp : Integrable (fun x => max (a x) 0) m := ha.sup (integrable_zero _ _ _)
  have hm : Integrable (fun x => max (-a x) 0) m := ha.neg.sup (integrable_zero _ _ _)
  have hsum : (∫ x, max (a x) 0 ∂m) + (∫ x, max (-a x) 0 ∂m) =
      ∫ x, |a x| ∂m := by
    rw [← integral_add hp hm]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rcases le_total 0 (a x) with h | h
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h, add_zero]
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h, zero_add]
  have hq : max (-(∫ x, a x ∂m)) 0 + max (∫ x, a x ∂m) 0 = |∫ x, a x ∂m| := by
    rcases le_total 0 (∫ x, a x ∂m) with h | h
    · rw [max_eq_right (neg_nonpos.mpr h), max_eq_left h, abs_of_nonneg h, zero_add]
    · rw [max_eq_left (neg_nonneg.mpr h), max_eq_right h, abs_of_nonpos h, add_zero]
  have hpn : 0 ≤ ∫ x, max (a x) 0 ∂m := integral_nonneg (fun x => le_max_right _ _)
  have hmn : 0 ≤ ∫ x, max (-a x) 0 ∂m := integral_nonneg (fun x => le_max_right _ _)
  have hnorm : |∫ x, a x ∂m| ≤ ∫ x, |a x| ∂m := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm a
  simp only [recenteredPositive, recenteredNegative, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ (0 : Fin n → ℝ)), mul_one]
  rw [image_density_univ f hf _ hp (fun x => le_max_right _ _),
    image_density_univ f hf _ hm (fun x => le_max_right _ _)]
  rw [← ENNReal.ofReal_add hpn (le_max_right _ _),
    ← ENNReal.ofReal_add hmn (le_max_right _ _),
    ← ENNReal.ofReal_add (add_nonneg hpn (le_max_right _ _))
      (add_nonneg hmn (le_max_right _ _))]
  apply ENNReal.ofReal_le_ofReal
  linarith

/--
EBM Remark 4.12: the recentered source identity proves normality of the given current.

Eriksson-Bique--Murugan, Section 4.2 and Remark 4.12, p. 38; the boundary includes the Dirac
correction at zero.
-/
theorem isNormal_of_centered_source_density (T : PolarCurrent n)
    (f : X → (Fin n → ℝ)) (hf : Measurable f)
    (a : X → ℝ) (ham : Measurable a) (ha : Integrable a m)
    (hb : ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      T.boundary φ = -(∫ x, φ (f x) * a x ∂m) + φ 0 * ∫ x, a x ∂m) :
    T.IsNormal := by
  have hfin := recentered_finite f a ha
  refine ⟨recenteredPositive f a m, recenteredNegative f a m, hfin.1, hfin.2, ?_⟩
  intro φ hφ hk
  have hp : Integrable (fun x => max (a x) 0) m := ha.sup (integrable_zero _ _ _)
  have hm : Integrable (fun x => max (-a x) 0) m := ha.neg.sup (integrable_zero _ _ _)
  haveI := finite_image_density f (fun x => max (a x) 0) hp (fun x => le_max_right _ _)
  haveI := finite_image_density f (fun x => max (-a x) 0) hm (fun x => le_max_right _ _)
  obtain ⟨C, hC⟩ := hk.exists_bound_of_continuous hφ.continuous
  have htest : ∀ (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν], Integrable φ ν := by
    intro ν _
    exact Integrable.of_bound hφ.continuous.aestronglyMeasurable C (ae_of_all _ hC)
  haveI := finite_dirac_real_weight (max (-(∫ x, a x ∂m)) 0) (0 : Fin n → ℝ)
  haveI := finite_dirac_real_weight (max (∫ x, a x ∂m) 0) (0 : Fin n → ℝ)
  rw [hb φ hφ hk, recenteredPositive, recenteredNegative,
    integral_add_measure (htest _) (htest _), integral_add_measure (htest _) (htest _),
    integral_smul_measure, integral_smul_measure,
    integral_dirac,
    ENNReal.toReal_ofReal (le_max_right _ _), ENNReal.toReal_ofReal (le_max_right _ _),
    smul_eq_mul, smul_eq_mul,
    integral_image_density f hf _ (ham.max measurable_const)
      (fun x => le_max_right _ _) φ hφ.continuous,
    integral_image_density f hf (fun x => max (-a x) 0) (ham.neg.max measurable_const)
      (fun x => le_max_right _ _) φ hφ.continuous]
  have hip := hp.bdd_mul (hφ.continuous.measurable.comp hf).aestronglyMeasurable
    (ae_of_all _ fun x => hC (f x))
  have him := hm.bdd_mul (hφ.continuous.measurable.comp hf).aestronglyMeasurable
    (ae_of_all _ fun x => hC (f x))
  have he : (∫ x, φ (f x) * a x ∂m) =
      (∫ x, φ (f x) * max (a x) 0 ∂m) - ∫ x, φ (f x) * max (-a x) 0 ∂m := by
    change Integrable (fun x => φ (f x) * max (a x) 0) m at hip
    change Integrable (fun x => φ (f x) * max (-a x) 0) m at him
    rw [← integral_sub hip him]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    rcases le_total 0 (a x) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
  rw [he]
  rcases le_total 0 (∫ x, a x ∂m) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring

/--
A direct bound on every bounded boundary test, with the same factor two.

Eriksson-Bique--Murugan, Section 4.2 and Remark 4.12, p. 38; the boundary includes the Dirac
correction at zero.
-/
theorem boundary_bound_of_centered_source (T : PolarCurrent n)
    (f : X → (Fin n → ℝ)) (hf : Measurable f)
    (a : X → ℝ) (ha : Integrable a m)
    (φ : (Fin n → ℝ) → ℝ) (hφ : Measurable φ) {C : ℝ} (hC : 0 ≤ C)
    (hφC : ∀ y, |φ y| ≤ C)
    (hb : T.boundary φ = -(∫ x, φ (f x) * a x ∂m) + φ 0 * ∫ x, a x ∂m) :
    |T.boundary φ| ≤ 2 * C * ∫ x, |a x| ∂m := by
  have hi := ha.bdd_mul (hφ.comp hf).aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hφC (f x))
  have h1 : |∫ x, φ (f x) * a x ∂m| ≤ C * ∫ x, |a x| ∂m := by
    calc
      _ ≤ ∫ x, |φ (f x) * a x| ∂m := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => φ (f x) * a x)
      _ ≤ ∫ x, C * |a x| ∂m := integral_mono_ae hi.abs (ha.abs.const_mul C)
        (ae_of_all _ fun x => by
          dsimp only
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hφC (f x)) (abs_nonneg _))
      _ = _ := integral_const_mul _ _
  have h2 : |∫ x, a x ∂m| ≤ ∫ x, |a x| ∂m := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm a
  rw [hb]
  calc
    _ ≤ |∫ x, φ (f x) * a x ∂m| + |φ 0| * |∫ x, a x ∂m| := by
      simpa only [abs_neg, abs_mul] using abs_add_le (-(∫ x, φ (f x) * a x ∂m))
        (φ 0 * ∫ x, a x ∂m)
    _ ≤ C * ∫ x, |a x| ∂m + C * ∫ x, |a x| ∂m :=
      add_le_add h1 (mul_le_mul (hφC 0) h2 (abs_nonneg _) hC)
    _ = _ := by ring

/--
A finite collection of integrable signed source densities has a common finite image reference.
-/
theorem exists_image_vector_density (f : X → (Fin n → ℝ)) (hf : Measurable f)
    (b : Fin n → X → ℝ) (hbm : ∀ i, Measurable (b i)) (hbi : ∀ i, Integrable (b i) m) :
    ∃ (ν : Measure (Fin n → ℝ)) (c : (Fin n → ℝ) → (Fin n → ℝ)),
      IsFiniteMeasure ν ∧ Measurable c ∧ Integrable (fun y => polarNorm (c y)) ν ∧
      ∀ h : Fin n → (Fin n → ℝ) → ℝ,
        (∀ i, Measurable (h i)) → (∃ C : ℝ, ∀ i y, |h i y| ≤ C) →
        (∫ y, ∑ i, h i y * c y i ∂ν) = ∫ x, ∑ i, h i (f x) * b i x ∂m := by
  classical
  let μp : Fin n → Measure (Fin n → ℝ) := fun i =>
    (m.withDensity (fun x => ENNReal.ofReal (max (b i x) 0))).map f
  let μm : Fin n → Measure (Fin n → ℝ) := fun i =>
    (m.withDensity (fun x => ENNReal.ofReal (max (-b i x) 0))).map f
  haveI (i : Fin n) : IsFiniteMeasure (μp i) := finite_image_density f _
    ((hbi i).sup (integrable_zero _ _ _)) (fun x => le_max_right _ _)
  haveI (i : Fin n) : IsFiniteMeasure (μm i) := finite_image_density f _
    ((hbi i).neg.sup (integrable_zero _ _ _)) (fun x => le_max_right _ _)
  let ν : Measure (Fin n → ℝ) := ∑ i, (μp i + μm i)
  haveI : IsFiniteMeasure ν := by dsimp only [ν]; infer_instance
  have hple (i : Fin n) : μp i ≤ ν :=
    (le_add_of_nonneg_right (show 0 ≤ μm i from bot_le)).trans
      (Finset.single_le_sum (fun j _ => show 0 ≤ μp j + μm j from bot_le) (Finset.mem_univ i))
  have hmle (i : Fin n) : μm i ≤ ν :=
    (le_add_of_nonneg_left (show 0 ≤ μp i from bot_le)).trans
      (Finset.single_le_sum (fun j _ => show 0 ≤ μp j + μm j from bot_le) (Finset.mem_univ i))
  let cp : Fin n → (Fin n → ℝ) → ℝ := fun i y => ((μp i).rnDeriv ν y).toReal
  let cm : Fin n → (Fin n → ℝ) → ℝ := fun i y => ((μm i).rnDeriv ν y).toReal
  let c : (Fin n → ℝ) → (Fin n → ℝ) := fun y i => cp i y - cm i y
  have hcp (i : Fin n) : Integrable (cp i) ν := Measure.integrable_toReal_rnDeriv
  have hcm (i : Fin n) : Integrable (cm i) ν := Measure.integrable_toReal_rnDeriv
  have hc (i : Fin n) : Integrable (fun y => c y i) ν := (hcp i).sub (hcm i)
  have hcmear : Measurable c := measurable_pi_lambda _ fun i =>
    ((μp i).measurable_rnDeriv ν).ennreal_toReal.sub ((μm i).measurable_rnDeriv ν).ennreal_toReal
  have hcnorm : Integrable (fun y => polarNorm (c y)) ν :=
    ((ErrorStructure.euclideanEquiv n).toContinuousLinearMap.integrable_comp
      (integrable_pi_iff.mpr hc)).norm
  refine ⟨ν, c, inferInstance, hcmear, hcnorm, fun h hh hb => ?_⟩
  obtain ⟨C, hC⟩ := hb
  have hip (i : Fin n) : Integrable (fun y => h i y * cp i y) ν :=
    (hcp i).bdd_mul (hh i).aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hC i y)
  have him (i : Fin n) : Integrable (fun y => h i y * cm i y) ν :=
    (hcm i).bdd_mul (hh i).aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hC i y)
  have his (i : Fin n) : Integrable (fun x => h i (f x) * b i x) m :=
    (hbi i).bdd_mul ((hh i).comp hf).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hC i (f x))
  have hir (i : Fin n) : Integrable (fun y => h i y * c y i) ν :=
    (hc i).bdd_mul (hh i).aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hC i y)
  rw [integral_finsetSum _ (fun i _ => hir i), integral_finsetSum _ (fun i _ => his i)]
  apply Finset.sum_congr rfl
  intro i _
  have hpRN : (∫ y, h i y * cp i y ∂ν) = ∫ y, h i y ∂μp i := by
    simpa only [cp, mul_comm] using
      (integral_toReal_rnDeriv_mul (f := h i) (Measure.absolutelyContinuous_of_le (hple i)))
  have hmRN : (∫ y, h i y * cm i y ∂ν) = ∫ y, h i y ∂μm i := by
    simpa only [cm, mul_comm] using
      (integral_toReal_rnDeriv_mul (f := h i) (Measure.absolutelyContinuous_of_le (hmle i)))
  have hmap (d : X → ℝ) (hd : Measurable d) (hpos : ∀ x, 0 ≤ d x) :
      (∫ y, h i y ∂(m.withDensity (fun x => ENNReal.ofReal (d x))).map f) =
        ∫ x, h i (f x) * d x ∂m := by
    rw [integral_map hf.aemeasurable (hh i).aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul (μ := m)
        (f := fun x => ENNReal.ofReal (d x)) hd.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [ENNReal.toReal_ofReal (hpos x), smul_eq_mul, mul_comm]
  change (∫ y, h i y * (cp i y - cm i y) ∂ν) = _
  simp_rw [mul_sub]
  rw [integral_sub (hip i) (him i), hpRN, hmRN,
    hmap (fun x => max (b i x) 0) ((hbm i).max measurable_const) (fun x => le_max_right _ _),
    hmap (fun x => max (-b i x) 0) ((hbm i).neg.max measurable_const) (fun x => le_max_right _ _)]
  have hbp : Integrable (fun x => h i (f x) * max (b i x) 0) m :=
    ((hbi i).sup (integrable_zero _ _ _)).bdd_mul ((hh i).comp hf).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hC i (f x))
  have hbm' : Integrable (fun x => h i (f x) * max (-b i x) 0) m :=
    ((hbi i).neg.sup (integrable_zero _ _ _)).bdd_mul ((hh i).comp hf).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hC i (f x))
  rw [← integral_sub hbp hbm']
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  rcases le_total 0 (b i x) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring

end ErrorCalculus.PolarCurrent

namespace DprBridge.BH1991.DirichletForm
variable {X : Type u} [MeasurableSpace X] {m : Measure X} (D : DirichletForm m)

/-- The prescribed polar current has exactly the Euclidean density mass, by construction. -/
theorem densityCurrent_mass {n : ℕ} (i₀ : Fin n) (ν : Measure (Fin n → ℝ))
    (c : (Fin n → ℝ) → (Fin n → ℝ)) (hc : Measurable c)
    (hi : Integrable (fun y => polarNorm (c y)) ν) :
    (PolarCurrent.ofDensity ν c hc hi i₀).mass =
      ν.withDensity (fun y => ENNReal.ofReal (polarNorm (c y))) := rfl

/--
A single centered test chain suffices for the boundary identity of the prescribed density.

Eriksson-Bique--Murugan, Section 4.2 and Remark 4.12, p. 38; the boundary includes the Dirac
correction at zero.
-/
theorem densityCurrent_boundary_of_centered_test (hL : D.Local) (G : D.CarreDuChamp)
    {n : ℕ} (i₀ : Fin n) (f : Fin n → D.form.dom) (g : D.form.dom) (a : Lp ℝ 2 m)
    (hA : D.IsGeneratorPair g a) (ha : Integrable a m)
    (ν : Measure (Fin n → ℝ)) (c : (Fin n → ℝ) → (Fin n → ℝ))
    (hc : Measurable c) (hi : Integrable (fun y => polarNorm (c y)) ν)
    (hRN : ∀ h : Fin n → (Fin n → ℝ) → ℝ,
      (∀ i, Measurable (h i)) → (∃ C : ℝ, ∀ i y, |h i y| ≤ C) →
      (∫ y, ∑ i, h i y * c y i ∂ν) = ∫ x, ∑ i,
        h i (fun j => (f j : Lp ℝ 2 m) x) *
          ((1 / 2 : ℝ) * G.Γ (D.form.formToDomain.symm (f i))
            (D.form.formToDomain.symm g) x) ∂m)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (hk : HasCompactSupport φ)
    (w : D.form.dom)
    (hw : ⇑(w : Lp ℝ 2 m) =ᵐ[m] fun x => φ (fun i => (f i : Lp ℝ 2 m) x) - φ 0)
    (hchain : ⇑(G.Γ (D.form.formToDomain.symm w) (D.form.formToDomain.symm g)) =ᵐ[m]
      fun x => ∑ i, fderiv ℝ φ (fun j => (f j : Lp ℝ 2 m) x) (Pi.single i 1) *
        G.Γ (D.form.formToDomain.symm (f i)) (D.form.formToDomain.symm g) x) :
    (PolarCurrent.ofDensity ν c hc hi i₀).boundary φ =
      -(∫ x, φ (fun i => (f i : Lp ℝ 2 m) x) * a x ∂m) + φ 0 * ∫ x, a x ∂m := by
  have hC : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hk hC (by norm_num)
  have hpartial : ∀ i, Measurable (fun y => fderiv ℝ φ y (Pi.single i 1)) := fun i =>
    ((hC.fderiv_right (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuous.clm_apply
      continuous_const).measurable
  have hbound : ∃ C : ℝ, ∀ i y, |fderiv ℝ φ y (Pi.single i 1)| ≤ C :=
    ⟨L, fun i y => fderiv_coefficient_bound hLip y i⟩
  have hf : Measurable (fun x i => (f i : Lp ℝ 2 m) x) :=
    measurable_pi_lambda _ fun i => (Lp.stronglyMeasurable _).measurable
  obtain ⟨C, hCb⟩ := hk.exists_bound_of_continuous hφ.continuous
  have hva := ha.bdd_mul (hφ.continuous.measurable.comp hf).aestronglyMeasurable
    (ae_of_all _ fun x => hCb (fun i => (f i : Lp ℝ 2 m) x))
  have he := BH1991.generator_pair_centered D g w a hA
    (fun x => φ (fun i => (f i : Lp ℝ 2 m) x)) (φ 0) hw ha hva
  change (PolarCurrent.ofDensity ν c hc hi i₀).action
    (fun i y => fderiv ℝ φ y (Pi.single i 1)) = _
  rw [PolarCurrent.ofDensity_action, hRN _ hpartial hbound]
  calc
    _ = (1 / 2 : ℝ) * ∫ x, G.Γ (D.form.formToDomain.symm w)
        (D.form.formToDomain.symm g) x ∂m := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hchain] with x hx
      rw [hx, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = D.form.E w g := (D.energy_eq_integral hL G w g).symm
    _ = _ := he

/--
The prescribed RN current is normal and has the recentered boundary when the centered smooth-test
chains are supplied.

Eriksson-Bique--Murugan, Section 4.2 and Remark 4.12, p. 38; the boundary includes the Dirac
correction at zero.
-/
theorem normalCurrent_of_RN_density_of_centered_tests (hL : D.Local) (G : D.CarreDuChamp)
    {n : ℕ} (i₀ : Fin n) (f : Fin n → D.form.dom) (g : D.form.dom) (a : Lp ℝ 2 m)
    (hA : D.IsGeneratorPair g a) (ha : Integrable a m)
    (hchain : ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∃ w : D.form.dom,
        (⇑(w : Lp ℝ 2 m) =ᵐ[m] fun x => φ (fun i => (f i : Lp ℝ 2 m) x) - φ 0) ∧
        ⇑(G.Γ (D.form.formToDomain.symm w) (D.form.formToDomain.symm g)) =ᵐ[m]
          fun x => ∑ i, fderiv ℝ φ (fun j => (f j : Lp ℝ 2 m) x) (Pi.single i 1) *
            G.Γ (D.form.formToDomain.symm (f i)) (D.form.formToDomain.symm g) x)
    (ν : Measure (Fin n → ℝ)) (c : (Fin n → ℝ) → (Fin n → ℝ))
    (hc : Measurable c) (hi : Integrable (fun y => polarNorm (c y)) ν)
    (hRN : ∀ h : Fin n → (Fin n → ℝ) → ℝ,
      (∀ i, Measurable (h i)) → (∃ C : ℝ, ∀ i y, |h i y| ≤ C) →
      (∫ y, ∑ i, h i y * c y i ∂ν) = ∫ x, ∑ i,
        h i (fun j => (f j : Lp ℝ 2 m) x) *
          ((1 / 2 : ℝ) * G.Γ (D.form.formToDomain.symm (f i))
            (D.form.formToDomain.symm g) x) ∂m) :
    (PolarCurrent.ofDensity ν c hc hi i₀).IsNormal ∧
      ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (PolarCurrent.ofDensity ν c hc hi i₀).boundary φ =
          -(∫ x, φ (fun i => (f i : Lp ℝ 2 m) x) * a x ∂m) + φ 0 * ∫ x, a x ∂m := by
  have hb : ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (PolarCurrent.ofDensity ν c hc hi i₀).boundary φ =
        -(∫ x, φ (fun i => (f i : Lp ℝ 2 m) x) * a x ∂m) + φ 0 * ∫ x, a x ∂m := by
    intro φ hφ hk
    obtain ⟨w, hw, hγ⟩ := hchain φ hφ hk
    exact D.densityCurrent_boundary_of_centered_test hL G i₀ f g a hA ha ν c hc hi hRN
      φ hφ hk w hw hγ
  refine ⟨?_, hb⟩
  exact PolarCurrent.isNormal_of_centered_source_density _
    (fun x i => (f i : Lp ℝ 2 m) x)
    (measurable_pi_lambda _ fun i => (Lp.stronglyMeasurable _).measurable)
    a (Lp.stronglyMeasurable _).measurable ha hb

/--
The prescribed RN polar current is normal and has the recentered EBM boundary.

Eriksson-Bique--Murugan, Section 4.2 and Remark 4.12, p. 38; the boundary includes the Dirac
correction at zero.
-/
theorem normalCurrent_of_RN_density (hL : D.Local) (G : D.CarreDuChamp)
    {n : ℕ} (i₀ : Fin n) (f : Fin n → D.form.dom) (g : D.form.dom) (a : Lp ℝ 2 m)
    (hA : D.IsGeneratorPair g a) (ha : Integrable a m)
    (ν : Measure (Fin n → ℝ)) (c : (Fin n → ℝ) → (Fin n → ℝ))
    (hc : Measurable c) (hi : Integrable (fun y => polarNorm (c y)) ν)
    (hRN : ∀ h : Fin n → (Fin n → ℝ) → ℝ,
      (∀ i, Measurable (h i)) → (∃ C : ℝ, ∀ i y, |h i y| ≤ C) →
      (∫ y, ∑ i, h i y * c y i ∂ν) = ∫ x, ∑ i,
        h i (fun j => (f j : Lp ℝ 2 m) x) *
          ((1 / 2 : ℝ) * G.Γ (D.form.formToDomain.symm (f i))
            (D.form.formToDomain.symm g) x) ∂m) :
    (PolarCurrent.ofDensity ν c hc hi i₀).IsNormal ∧
      ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (PolarCurrent.ofDensity ν c hc hi i₀).boundary φ =
          -(∫ x, φ (fun i => (f i : Lp ℝ 2 m) x) * a x ∂m) + φ 0 * ∫ x, a x ∂m := by
  apply D.normalCurrent_of_RN_density_of_centered_tests hL G i₀ f g a hA ha _ ν c hc hi hRN
  intro φ hφ hk
  have hC : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hk hC (by norm_num)
  obtain ⟨w, hw, hγ⟩ := D.centered_chainRule hL G i₀.pos f φ L hC hLip
  exact ⟨w, hw, hγ g⟩

/--
An actual normal current exists with the full bounded-test action and the recentered boundary.

Eriksson-Bique--Murugan, Section 4.2 and Remark 4.12, p. 38; the boundary includes the Dirac
correction at zero.
-/
theorem exists_normalCurrent (hL : D.Local) (G : D.CarreDuChamp)
    {n : ℕ} (hn : 0 < n) (f : Fin n → D.form.dom)
    (g : D.form.dom) (a : Lp ℝ 2 m)
    (hA : D.IsGeneratorPair g a) (ha : Integrable a m) :
    ∃ T : PolarCurrent n, T.IsNormal ∧
      (∀ h : Fin n → (Fin n → ℝ) → ℝ,
        (∀ i, Measurable (h i)) → (∃ C : ℝ, ∀ i y, |h i y| ≤ C) →
        T.action h = ∫ x, ∑ i, h i (fun j => (f j : Lp ℝ 2 m) x) *
          ((1 / 2 : ℝ) * G.Γ (D.form.formToDomain.symm (f i))
            (D.form.formToDomain.symm g) x) ∂m) ∧
      ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        T.boundary φ = -(∫ x, φ (fun i => (f i : Lp ℝ 2 m) x) * a x ∂m) +
          φ 0 * ∫ x, a x ∂m := by
  let i₀ : Fin n := ⟨0, hn⟩
  obtain ⟨ν, c, -, hc, hi, hRN⟩ := PolarCurrent.exists_image_vector_density
    (fun x i => (f i : Lp ℝ 2 m) x)
    (measurable_pi_lambda _ fun i => (Lp.stronglyMeasurable _).measurable)
    (fun i x => (1 / 2 : ℝ) * G.Γ (D.form.formToDomain.symm (f i)) (D.form.formToDomain.symm g) x)
    (fun i => (Lp.stronglyMeasurable _).measurable.const_mul _)
    (fun i => (L1.integrable_coeFn _).const_mul _)
  obtain ⟨hnormal, hboundary⟩ := D.normalCurrent_of_RN_density hL G i₀ f g a hA ha ν c hc hi hRN
  refine ⟨PolarCurrent.ofDensity ν c hc hi i₀, hnormal, ?_, hboundary⟩
  intro h hm hb
  rw [PolarCurrent.ofDensity_action]
  exact hRN h hm hb

end DprBridge.BH1991.DirichletForm

namespace DprBridge.BH1991.ChainCurrentControls

/-- The two slope conventions differ at the peak of a nonconstant unit hat. -/
theorem right_hat_peak :
    DirichletForm.rightHatSlope 0 1 0 = -1 ∧ gridHatSlope 0 1 0 = 0 := by
  norm_num [DirichletForm.rightHatSlope, gridHatSlope, Set.indicator]

/--
The nonlinear two-coordinate chain applies to infinite counting measure without adjoining one.
-/
theorem nonlinear_infinite_model
    (f : Fin 2 → (zeroForm (Measure.count : Measure ℕ)).form.dom)
    (hf : ∀ i, (zeroForm (Measure.count : Measure ℕ)).Bounded (f i)) :
    (∃ w : (zeroForm (Measure.count : Measure ℕ)).form.dom,
      ⇑(w : Lp ℝ 2 (Measure.count : Measure ℕ)) =ᵐ[Measure.count]
        fun x => (f 0 : Lp ℝ 2 (Measure.count : Measure ℕ)) x *
          (f 1 : Lp ℝ 2 (Measure.count : Measure ℕ)) x) ∧
    ¬ ∃ v : (zeroForm (Measure.count : Measure ℕ)).form.dom,
      ⇑(v : Lp ℝ 2 (Measure.count : Measure ℕ)) =ᵐ[Measure.count] fun _ => (1 : ℝ) := by
  refine ⟨?_, zeroForm_count_no_one⟩
  obtain ⟨w, hw, -⟩ := (zeroForm (Measure.count : Measure ℕ)).centered_bounded_chainRule
    (zeroForm_local _) (zeroCarreDuChamp _) (by decide : 0 < 2) f hf
    (fun y => 7 + y 0 * y 1) (by fun_prop)
  refine ⟨w, ?_⟩
  filter_upwards [hw] with x hx
  simpa only [Pi.zero_apply, mul_zero, add_zero, add_sub_cancel_left] using hx

/--
The Dirac correction cancels a nonzero total source mass when the source map is zero.

Eriksson-Bique--Murugan, Section 4.2 and Remark 4.12, p. 38; the boundary includes the Dirac
correction at zero.
-/
theorem dirac_centering_control (φ : (Fin 1 → ℝ) → ℝ) (hφ : φ 0 = 1) :
    (-(∫ _ : Unit, φ 0 * (1 : ℝ) ∂Measure.dirac ()) +
      φ 0 * (∫ _ : Unit, (1 : ℝ) ∂Measure.dirac ())) = 0 ∧
    (-(∫ _ : Unit, φ 0 * (1 : ℝ) ∂Measure.dirac ())) ≠ 0 := by
  simp [hφ]

/-- A zero vector density has zero mass regardless of the direction selected on its zero set. -/
theorem zero_density_mass {n : ℕ} (i₀ : Fin n) (ν : Measure (Fin n → ℝ)) :
    (PolarCurrent.ofDensity ν (fun _ => 0) measurable_const
      (by simp [polarNorm]) i₀).mass = 0 := by
  simp [PolarCurrent.ofDensity, polarMass, polarNorm]

end DprBridge.BH1991.ChainCurrentControls
