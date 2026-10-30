import ErrorCalculus.Dirichlet.BoundedDense
import ErrorCalculus.Dirichlet.DetBounded
import ErrorCalculus.Dirichlet.ExtensionLp

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace ErrorCalculus

/-- Coordinate derivative, with the finite product carrying its usual sup norm. -/
def partialDeriv {n : ℕ} (F : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ F x (Pi.single i 1)

/--
A C² function on finite coordinate space that is L-Lipschitz and whose partial derivatives are all
L′-Lipschitz.
-/
structure IsC2LipschitzGrad {n : ℕ} (F : (Fin n → ℝ) → ℝ) (L L' : ℝ≥0) : Prop where
  contDiff : ContDiff ℝ 2 F
  lipschitz : LipschitzWith L F
  partial_lipschitz : ∀ i, LipschitzWith L' (partialDeriv F i)

namespace IsC2LipschitzGrad
variable {n : ℕ} {F : (Fin n → ℝ) → ℝ} {L L' : ℝ≥0}

theorem partial_contDiff (hF : IsC2LipschitzGrad F L L') (i : Fin n) :
    ContDiff ℝ 1 (partialDeriv F i) :=
  (hF.contDiff.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const

end IsC2LipschitzGrad

theorem norm_partialDeriv_le {n : ℕ} {F : (Fin n → ℝ) → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) (i : Fin n) (x : Fin n → ℝ) : ‖partialDeriv F i x‖ ≤ L := by
  calc
    _ ≤ ‖fderiv ℝ F x‖ * ‖Pi.single i (1 : ℝ)‖ := (fderiv ℝ F x).le_opNorm _
    _ ≤ (L : ℝ) * 1 := mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hF)
      (by simp [Pi.norm_single]) (norm_nonneg _) L.coe_nonneg
    _ = _ := mul_one _

namespace ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {n : ℕ}

/-- C¹ Lipschitz calculus using everywhere measurable representatives. -/
theorem calc_representative (hn : 0 < n) (u : Fin n → S.dom)
    {F : (Fin n → ℝ) → ℝ} {L : ℝ≥0} (hC : ContDiff ℝ 1 F) (hL : LipschitzWith L F)
    (w : Lp ℝ 2 μ) (hw : ⇑w =ᵐ[μ] fun ω => F (S.representativeVec u ω)) :
    ∃ hd : w ∈ S.dom, ∀ v : S.dom, S.Γ ⟨w,hd⟩ v =ᵐ[μ] fun ω =>
      ∑ i, partialDeriv F i (S.representativeVec u ω) * S.Γ (u i) v ω := by
  obtain ⟨hd,hg⟩ := S.calc n hn u F L hC hL w
    (hw.trans ((S.coeFn_representativeVec u).fun_comp F).symm)
  refine ⟨hd, fun v => ?_⟩
  filter_upwards [hg v, S.coeFn_representativeVec u] with ω hg hu
  simpa only [hu, partialDeriv] using hg

/-- A canonical domain representative of a finite C¹ Lipschitz composition. -/
def c1Comp (hn : 0 < n) (u : Fin n → S.dom) {F : (Fin n → ℝ) → ℝ} {L : ℝ≥0}
    (hC : ContDiff ℝ 1 F) (hL : LipschitzWith L F) : S.dom :=
  let h := (memLp_congr_ae ((S.coeFn_representativeVec u).fun_comp F)).mp
    (composition_memLp (fun i => (u i : Lp ℝ 2 μ)) hL)
  ⟨h.toLp _, (S.calc_representative hn u hC hL _ h.coeFn_toLp).choose⟩

theorem coeFn_c1Comp (hn : 0 < n) (u : Fin n → S.dom) {F : (Fin n → ℝ) → ℝ}
    {L : ℝ≥0} (hC : ContDiff ℝ 1 F) (hL : LipschitzWith L F) :
    ⇑(S.c1Comp hn u hC hL : Lp ℝ 2 μ) =ᵐ[μ] fun ω => F (S.representativeVec u ω) :=
  ((memLp_congr_ae ((S.coeFn_representativeVec u).fun_comp F)).mp
    (composition_memLp (fun i => (u i : Lp ℝ 2 μ)) hL)).coeFn_toLp

theorem partial_comp_memLp_top (u : Fin n → S.dom) {F : (Fin n → ℝ) → ℝ}
    {L : ℝ≥0} (hC : ContDiff ℝ 1 F) (hL : LipschitzWith L F) (i : Fin n) :
    MemLp (fun ω => partialDeriv F i (S.representativeVec u ω)) ∞ μ := by
  apply MemLp.of_bound _ (L : ℝ) (Eventually.of_forall fun ω => norm_partialDeriv_le hL i _)
  exact ((hC.fderiv_right (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuous.clm_apply
    continuous_const).measurable.comp (S.measurable_representativeVec u) |>.aestronglyMeasurable

/--
The displayed generator expression is square integrable. For this step the Γ representatives only
need to be in L².
-/
theorem memLp_generatorCandidate (u : Fin n → S.dom)
    (hu : ∀ i, (u i : Lp ℝ 2 μ) ∈ S.generatorDom) (v : Fin n → Fin n → S.dom)
    {F : (Fin n → ℝ) → ℝ} {L L' : ℝ≥0} (hF : IsC2LipschitzGrad F L L') :
    MemLp (fun ω => ∑ i, (partialDeriv F i (S.representativeVec u ω) * S.generator ⟨u i,hu i⟩ ω +
      (1/2 : ℝ) * ∑ j, partialDeriv (partialDeriv F i) j (S.representativeVec u ω) *
        (v i j : Lp ℝ 2 μ) ω)) 2 μ := by
  apply memLp_finsetSum
  intro i _
  apply MemLp.add
  · exact (Lp.memLp _).mul (S.partial_comp_memLp_top u (hF.contDiff.of_le (by norm_num)) hF.lipschitz i)
  · apply MemLp.const_mul
    apply memLp_finsetSum
    intro j _
    exact (Lp.memLp _).mul (S.partial_comp_memLp_top u (hF.partial_contDiff i) (hF.partial_lipschitz i) j)

/-- The L² class of the generator candidate, independent of representatives a.e. -/
def generatorCandidate (u : Fin n → S.dom)
    (hu : ∀ i, (u i : Lp ℝ 2 μ) ∈ S.generatorDom) (v : Fin n → Fin n → S.dom)
    {F : (Fin n → ℝ) → ℝ} {L L' : ℝ≥0} (hF : IsC2LipschitzGrad F L L') : Lp ℝ 2 μ :=
  (S.memLp_generatorCandidate u hu v hF).toLp _

theorem coeFn_generatorCandidate (u : Fin n → S.dom)
    (hu : ∀ i, (u i : Lp ℝ 2 μ) ∈ S.generatorDom) (v : Fin n → Fin n → S.dom)
    {F : (Fin n → ℝ) → ℝ} {L L' : ℝ≥0} (hF : IsC2LipschitzGrad F L L') :
    ⇑(S.generatorCandidate u hu v hF) =ᵐ[μ] fun ω => ∑ i,
      (partialDeriv F i (S.representativeVec u ω) * S.generator ⟨u i,hu i⟩ ω +
        (1/2 : ℝ) * ∑ j, partialDeriv (partialDeriv F i) j (S.representativeVec u ω) *
          (v i j : Lp ℝ 2 μ) ω) :=
  (S.memLp_generatorCandidate u hu v hF).coeFn_toLp

/-- The bounded first derivatives are elements of the bounded domain algebra. -/
theorem partial_comp_mem_boundedDomAlgebra (hn : 0 < n) (u : Fin n → S.dom)
    {F : (Fin n → ℝ) → ℝ} {L L' : ℝ≥0} (hF : IsC2LipschitzGrad F L L') (i : Fin n) :
    (fun ω => partialDeriv F i (S.representativeVec u ω)) ∈ S.boundedDomAlgebra :=
  ⟨S.c1Comp hn u (hF.partial_contDiff i) (hF.partial_lipschitz i),
    S.coeFn_c1Comp hn u _ _, L, Eventually.of_forall fun _ => norm_partialDeriv_le hF.lipschitz i _⟩

/-- integration by parts against bounded domain tests. -/
theorem energy_comp_eq_neg_inner_of_bounded (hn : 0 < n) (u : Fin n → S.dom)
    (hu : ∀ i, (u i : Lp ℝ 2 μ) ∈ S.generatorDom) (v : Fin n → Fin n → S.dom)
    (hv : ∀ i j, ⇑(v i j : Lp ℝ 2 μ) =ᵐ[μ] S.Γ (u i) (u j))
    {F : (Fin n → ℝ) → ℝ} {L L' : ℝ≥0} (hF : IsC2LipschitzGrad F L L')
    (w : S.dom) (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun ω => F (S.representativeVec u ω))
    (z : S.dom) (hz : AEBounded (μ := μ) (z : Lp ℝ 2 μ)) :
    S.energy.E w z = -inner ℝ (S.generatorCandidate u hu v hF) (z : Lp ℝ 2 μ) := by
  let p : Fin n → S.dom := fun i => S.boundedDomElement _ (S.partial_comp_mem_boundedDomAlgebra hn u hF i)
  have hp (i : Fin n) : ⇑(p i : Lp ℝ 2 μ) =ᵐ[μ]
      fun ω => partialDeriv F i (S.representativeVec u ω) := S.coeFn_boundedDomElement _ _
  have hb (i : Fin n) : AEBounded (μ := μ) (p i : Lp ℝ 2 μ) := S.bounded_boundedDomElement _ _
  have hg := (S.calc_representative hn u (hF.contDiff.of_le (by norm_num)) hF.lipschitz w hw).choose_spec z
  have hg' (i : Fin n) := (S.calc_representative hn u (hF.partial_contDiff i)
    (hF.partial_lipschitz i) (p i) (hp i)).choose_spec (u i)
  have hleft : S.Γ w z =ᵐ[μ] fun ω => ∑ i, (p i : Lp ℝ 2 μ) ω * S.Γ z (u i) ω := by
    filter_upwards [hg, ae_all_iff.mpr hp] with ω hg hp
    change S.Γ w z ω = _ at hg
    rw [hg]
    apply Finset.sum_congr rfl
    intro i _
    rw [hp i, S.Γ_symm (u i) z]
  have hright : (fun ω => ∑ i, (z : Lp ℝ 2 μ) ω *
      (-(2 * (p i : Lp ℝ 2 μ) ω * S.generator ⟨u i,hu i⟩ ω + S.Γ (p i) (u i) ω)))
      =ᵐ[μ] fun ω => -2 * ((z : Lp ℝ 2 μ) ω * S.generatorCandidate u hu v hF ω) := by
    filter_upwards [ae_all_iff.mpr hp, ae_all_iff.mpr hg',
      ae_all_iff.mpr (fun i => ae_all_iff.mpr (hv i)), S.coeFn_generatorCandidate u hu v hF]
      with ω hp hg hv hc
    rw [hc, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hp i, hg i]
    have he : (∑ j, partialDeriv (partialDeriv F i) j (S.representativeVec u ω) * S.Γ (u j) (u i) ω) =
        ∑ j, partialDeriv (partialDeriv F i) j (S.representativeVec u ω) * (v i j : Lp ℝ 2 μ) ω := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hv i j, S.Γ_symm]
    rw [he]
    ring
  have hi (i : Fin n) : Integrable (fun ω => (p i : Lp ℝ 2 μ) ω * S.Γ z (u i) ω) μ :=
    (L1.integrable_coeFn _).bdd_mul (Lp.aestronglyMeasurable _) (hb i).choose_spec
  have hj (i : Fin n) : Integrable (fun ω => (z : Lp ℝ 2 μ) ω *
      (-(2 * (p i : Lp ℝ 2 μ) ω * S.generator ⟨u i,hu i⟩ ω + S.Γ (p i) (u i) ω))) μ := by
    apply Integrable.bdd_mul _ (Lp.aestronglyMeasurable _) hz.choose_spec
    have hh := ((Lp.memLp (p i : Lp ℝ 2 μ)).integrable_mul (Lp.memLp (S.generator ⟨u i,hu i⟩))).const_mul 2
    exact ((by simpa only [Pi.mul_apply, mul_assoc] using hh : Integrable
      (fun ω => 2 * (p i : Lp ℝ 2 μ) ω * S.generator ⟨u i,hu i⟩ ω) μ).add
        (L1.integrable_coeFn _)).neg
  rw [ErrorData.energy_apply, integral_congr_ae hleft, integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [S.integral_weight_gamma _ _ z (hu _) (hb _) hz]
  rw [← integral_finsetSum _ (fun i _ => hj i), integral_congr_ae hright, integral_const_mul,
    L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The variational characterization identifies a candidate with G₁(w-g). -/
theorem eq_resolvent_of_energy_identity (w : S.dom) (g : Lp ℝ 2 μ)
    (he : ∀ z : S.dom, S.energy.E w z = -inner ℝ g (z : Lp ℝ 2 μ)) :
    (w : Lp ℝ 2 μ) = S.generatorResolvent.G 1 ((w : Lp ℝ 2 μ) - g) := by
  rw [QuadForm.formResolvent_G _ _ _ zero_lt_one]
  exact congrArg Subtype.val (S.energy.resolvent_unique S.energy_closed 1 zero_lt_one
    ((w : Lp ℝ 2 μ) - g) w (fun z => by rw [he z, inner_sub_left]; ring))

theorem mem_generatorDom_of_energy_identity (w : S.dom) (g : Lp ℝ 2 μ)
    (he : ∀ z : S.dom, S.energy.E w z = -inner ℝ g (z : Lp ℝ 2 μ)) :
    (w : Lp ℝ 2 μ) ∈ S.generatorDom := by
  rw [S.eq_resolvent_of_energy_identity w g he]
  exact S.generatorResolvent.mem_dom_G zero_lt_one _

theorem generator_of_energy_identity (w : S.dom) (g : Lp ℝ 2 μ)
    (he : ∀ z : S.dom, S.energy.E w z = -inner ℝ g (z : Lp ℝ 2 μ))
    (hw : (w : Lp ℝ 2 μ) ∈ S.generatorDom) : S.generator ⟨w,hw⟩ = g := by
  have h := S.eq_resolvent_of_energy_identity w g he
  have hs : (⟨w,hw⟩ : S.generatorDom) =
      ⟨S.generatorResolvent.G 1 ((w : Lp ℝ 2 μ) - g), S.generatorResolvent.mem_dom_G zero_lt_one _⟩ :=
    Subtype.ext h
  rw [hs, Foundations.ContractionResolvent.generator_G _ zero_lt_one, ← h, one_smul]
  abel

/-- The weak composition identity holds against every domain element. -/
theorem energy_comp_eq_neg_inner (hn : 0 < n) (u : Fin n → S.dom)
    (hu : ∀ i, (u i : Lp ℝ 2 μ) ∈ S.generatorDom) (v : Fin n → Fin n → S.dom)
    (hv : ∀ i j, ⇑(v i j : Lp ℝ 2 μ) =ᵐ[μ] S.Γ (u i) (u j))
    {F : (Fin n → ℝ) → ℝ} {L L' : ℝ≥0} (hF : IsC2LipschitzGrad F L L')
    (w : S.dom) (hw : ⇑(w : Lp ℝ 2 μ) =ᵐ[μ] fun ω => F (S.representativeVec u ω))
    (z : S.dom) : S.energy.E w z = -inner ℝ (S.generatorCandidate u hu v hF) (z : Lp ℝ 2 μ) := by
  simpa only [inner_neg_left] using S.energy_identity_of_bounded w
    (-S.generatorCandidate u hu v hF) (fun z hz => by
      simpa only [inner_neg_left] using S.energy_comp_eq_neg_inner_of_bounded hn u hu v hv hF w hw z hz) z

/--
C² composition preserves the actual generator domain. The Γ entries represented in D need not be
bounded for this conclusion.
-/
theorem comp_mem_generatorDom (hn : 0 < n) (u : Fin n → S.dom)
    (hu : ∀ i, (u i : Lp ℝ 2 μ) ∈ S.generatorDom) (v : Fin n → Fin n → S.dom)
    (hv : ∀ i j, ⇑(v i j : Lp ℝ 2 μ) =ᵐ[μ] S.Γ (u i) (u j))
    {F : (Fin n → ℝ) → ℝ} {L L' : ℝ≥0} (hF : IsC2LipschitzGrad F L L')
    (w : Lp ℝ 2 μ) (hw : ⇑w =ᵐ[μ] fun ω => F (S.representativeVec u ω)) :
    w ∈ S.generatorDom := by
  let hd := (S.calc_representative hn u (hF.contDiff.of_le (by norm_num)) hF.lipschitz w hw).choose
  exact S.mem_generatorDom_of_energy_identity ⟨w,hd⟩ _ (S.energy_comp_eq_neg_inner hn u hu v hv hF ⟨w,hd⟩ hw)

/-- The generator is the explicit L² candidate. -/
theorem generator_comp (hn : 0 < n) (u : Fin n → S.dom)
    (hu : ∀ i, (u i : Lp ℝ 2 μ) ∈ S.generatorDom) (v : Fin n → Fin n → S.dom)
    (hv : ∀ i j, ⇑(v i j : Lp ℝ 2 μ) =ᵐ[μ] S.Γ (u i) (u j))
    {F : (Fin n → ℝ) → ℝ} {L L' : ℝ≥0} (hF : IsC2LipschitzGrad F L L')
    (w : Lp ℝ 2 μ) (hw : ⇑w =ᵐ[μ] fun ω => F (S.representativeVec u ω)) :
    S.generator ⟨w,S.comp_mem_generatorDom hn u hu v hv hF w hw⟩ = S.generatorCandidate u hu v hF := by
  let hd := (S.calc_representative hn u (hF.contDiff.of_le (by norm_num)) hF.lipschitz w hw).choose
  exact S.generator_of_energy_identity ⟨w,hd⟩ _ (S.energy_comp_eq_neg_inner hn u hu v hv hF ⟨w,hd⟩ hw) _

/-- The usual split sum formula, with Γ rather than its chosen L² representative. -/
theorem generator_comp_ae (hn : 0 < n) (u : Fin n → S.dom)
    (hu : ∀ i, (u i : Lp ℝ 2 μ) ∈ S.generatorDom) (v : Fin n → Fin n → S.dom)
    (hv : ∀ i j, ⇑(v i j : Lp ℝ 2 μ) =ᵐ[μ] S.Γ (u i) (u j))
    {F : (Fin n → ℝ) → ℝ} {L L' : ℝ≥0} (hF : IsC2LipschitzGrad F L L')
    (w : Lp ℝ 2 μ) (hw : ⇑w =ᵐ[μ] fun ω => F (S.representativeVec u ω)) :
    ⇑(S.generator ⟨w,S.comp_mem_generatorDom hn u hu v hv hF w hw⟩) =ᵐ[μ] fun ω =>
      (∑ i, partialDeriv F i (S.representativeVec u ω) * S.generator ⟨u i,hu i⟩ ω) +
        (1/2 : ℝ) * ∑ i, ∑ j, partialDeriv (partialDeriv F i) j (S.representativeVec u ω) * S.Γ (u i) (u j) ω := by
  rw [S.generator_comp hn u hu v hv hF w hw]
  filter_upwards [S.coeFn_generatorCandidate u hu v hF, ae_all_iff.mpr (fun i => ae_all_iff.mpr (hv i))]
    with ω hc hv
  simp only [hc, hv, Finset.sum_add_distrib, Finset.mul_sum]

end ErrorStructure
end ErrorCalculus
