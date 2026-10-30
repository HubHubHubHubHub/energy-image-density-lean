import ErrorCalculus.Dirichlet.LocalDirichletFormBounded
import ErrorCalculus.Dirichlet.CarreDuChampExistence

/-!
# carre du champ of a local Dirichlet form; connection to (Γ = 2γ); clause (a); locality of γ

## Main results
Generic data `LocalDirichletForm.CarreDuChamp D` for the carre du champ of a local Dirichlet
form, in the Eriksson-Bique–Murugan normalization (arXiv:2510.13659, def. 1.1 and (1.2), pp. 1–2):
ℰ(f, f)
= ∫ γ(f, f) dμ, γ = Γ/2 for BH 1991's Γ. Connection in both directions to
`Capacity.DirichletForm.IsCarreDuChamp` (BH 1991 prop. I.4.1.3, p. 17) via Γ = 2γ (`toCLM`,
`isCarreDuChamp_toCLM`, `ofIsCarreDuChamp`, `isCarreDuChamp_iff_eq_toCLM`); uniqueness, existence ⇔
(R) and the energy identity (clause (a) of BH I.6.1.1) reused from locality of γ and local
cancellation with a bounded multiplier.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option maxHeartbeats 800000

namespace ErrorCalculus

namespace LocalDirichletForm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## B. Generic carre du champ data; connection to (Γ = 2γ) -/

/--
Eriksson-Bique–Murugan, p. 2 (following BH 1991 prop. I.4.1.3, p. 17): the carre du champ operator
of a local Dirichlet form, in EBM's normalization (ℰ(f, f) = ∫ γ(f, f) dμ, i.e. γ = Γ/2 for BH's Γ).

The map γ : 𝔻 × 𝔻 → L¹(μ) is bilinear, symmetric, nonnegative, continuous for the ℰ₁ norm, and
satisfies (1.2): for f, g, h ∈ 𝔻 ∩ L^∞ and p, q, r ∈ 𝔻 representing fh, gh, fg, ½ ℰ(p, g) + ½ ℰ(q,
f) − ½ ℰ(h, r) = ∫ h γ(f, g) dμ. Symmetry and positivity are redundant (`ofIsCarreDuChamp`,
`isCarreDuChamp_toCLM`); they are retained for fidelity to EBM's text.
-/
structure CarreDuChamp (D : LocalDirichletForm μ) where
  /-- The operator γ. -/
  gamma : D.form.dom →ₗ[ℝ] D.form.dom →ₗ[ℝ] Lp ℝ 1 μ
  /-- The operator γ is symmetric. -/
  symm : ∀ f g : D.form.dom, gamma f g = gamma g f
  /-- The operator γ is nonnegative on the diagonal. -/
  nonneg : ∀ f : D.form.dom, 0 ≤ᵐ[μ] ⇑(gamma f f)
  /-- The operator γ is continuous from (𝔻, ℰ₁) × (𝔻, ℰ₁) to L¹(μ). -/
  continuous : ∃ C : ℝ, ∀ f g : D.form.dom,
    ‖gamma f g‖ ≤ C * D.form.formNorm f * D.form.formNorm g
  /-- (1.2). -/
  product : ∀ f g h : D.form.dom, AEBounded (μ := μ) ((f : Lp ℝ 2 μ) : Ω → ℝ) →
    AEBounded (μ := μ) ((g : Lp ℝ 2 μ) : Ω → ℝ) → AEBounded (μ := μ) ((h : Lp ℝ 2 μ) : Ω → ℝ) →
    ∀ p q r : D.form.dom,
    (⇑(p : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (h : Lp ℝ 2 μ) x) →
    (⇑(q : Lp ℝ 2 μ) =ᵐ[μ] fun x => (g : Lp ℝ 2 μ) x * (h : Lp ℝ 2 μ) x) →
    (⇑(r : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (g : Lp ℝ 2 μ) x) →
    (1 / 2 : ℝ) * D.form.E p g + (1 / 2 : ℝ) * D.form.E q f - (1 / 2 : ℝ) * D.form.E h r =
      ∫ x, (h : Lp ℝ 2 μ) x * gamma f g x ∂μ

variable (D : LocalDirichletForm μ)

/--
The energy on the space 𝔻 with the ℰ₁ norm (`ener_apply`), written using the identification
`D.form.formToDomain`.
-/
theorem ener_toDirichletForm (x y : D.toDirichletForm.Space) :
    D.toDirichletForm.ener x y = D.form.E (D.form.formToDomain x) (D.form.formToDomain y) :=
  D.toDirichletForm.ener_apply x y

/-- An element of 𝔻 ∩ L^∞ in sense is essentially bounded. -/
theorem aeBounded_of_mem_bddSpace {x : D.toDirichletForm.Space}
    (hx : x ∈ D.toDirichletForm.bddSpace) :
    AEBounded (μ := μ) (((D.form.formToDomain x : D.form.dom) : Lp ℝ 2 μ) : Ω → ℝ) := by
  obtain ⟨C, hC⟩ := hx
  exact ⟨C, hC.mono fun ω h => by rw [Real.norm_eq_abs]; exact h⟩

/--
An essentially bounded domain element belongs to the bounded form subspace under the inverse
form-space equivalence.
-/
theorem formToDomain_symm_mem_bddSpace {f : D.form.dom}
    (hf : AEBounded (μ := μ) ((f : Lp ℝ 2 μ) : Ω → ℝ)) :
    (D.form.formToDomain.symm f : D.toDirichletForm.Space) ∈ D.toDirichletForm.bddSpace :=
  (Submodule.mem_toAddSubgroup D.toDirichletForm.bddSpace).mp hf

namespace CarreDuChamp
variable {D} (G : D.CarreDuChamp)

/-- A chosen positive continuity constant. -/
def bound : ℝ := max G.continuous.choose 0

/-- The chosen bilinear bound for the carré du champ is nonnegative. -/
theorem bound_nonneg : 0 ≤ G.bound := le_max_right _ _

/-- ‖γ(f, g)‖_{L¹} ≤ C ‖f‖_{ℰ₁} ‖g‖_{ℰ₁}. -/
theorem norm_gamma_le (f g : D.form.dom) :
    ‖G.gamma f g‖ ≤ G.bound * D.form.formNorm f * D.form.formNorm g := by
  refine (G.continuous.choose_spec f g).trans ?_
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/--
connection to Γ = 2γ, viewed as a continuous bilinear operator on the space 𝔻 with the ℰ₁ norm
(`QuadForm.FormSpace`, the `Space` of `Capacity.DirichletForm`), in the normalization of BH 1991,
prop. I.4.1.3 (p. 17).
-/
def toCLM : D.form.FormSpace →L[ℝ] D.form.FormSpace →L[ℝ] Lp ℝ 1 μ :=
  LinearMap.mkContinuous₂
    ((((2 : ℝ) • G.gamma).comp D.form.formToDomain.toLinearMap).compl₂
      D.form.formToDomain.toLinearMap)
    (2 * G.bound) (fun x y => by
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearMap.smul_apply]
      rw [norm_smul, Real.norm_eq_abs, abs_two]
      have hx : D.form.formNorm (D.form.formToDomain x) = ‖x‖ := by
        rw [QuadForm.formNorm, LinearEquiv.symm_apply_apply]
      have hy : D.form.formNorm (D.form.formToDomain y) = ‖y‖ := by
        rw [QuadForm.formNorm, LinearEquiv.symm_apply_apply]
      have h := G.norm_gamma_le (D.form.formToDomain x) (D.form.formToDomain y)
      rw [hx, hy] at h
      linarith)

/--
The continuous form-space map is twice the domain carré du champ, transported by the equivalence.
-/
theorem toCLM_apply (x y : D.form.FormSpace) :
    G.toCLM x y = (2 : ℝ) • G.gamma (D.form.formToDomain x) (D.form.formToDomain y) :=
  rfl

/-- γ = ½ Γ. -/
theorem gamma_eq_half_smul_toCLM (f g : D.form.dom) :
    G.gamma f g = (1 / 2 : ℝ) • G.toCLM (D.form.formToDomain.symm f)
      (D.form.formToDomain.symm g) := by
  rw [toCLM_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, smul_smul]
  norm_num

/--
connection to BH 1991, prop. I.4.1.3 (p. 17): for every datum γ, Γ = 2γ is a carre du champ operator
of `D.toDirichletForm` in BH's sense.
-/
theorem isCarreDuChamp_toCLM : D.toDirichletForm.IsCarreDuChamp G.toCLM := by
  intro x hx y hy z hz
  have h := G.product (D.form.formToDomain x) (D.form.formToDomain y) (D.form.formToDomain z)
    (D.aeBounded_of_mem_bddSpace hx) (D.aeBounded_of_mem_bddSpace hy)
    (D.aeBounded_of_mem_bddSpace hz)
    (D.form.formToDomain (D.toDirichletForm.mulS x z))
    (D.form.formToDomain (D.toDirichletForm.mulS y z))
    (D.form.formToDomain (D.toDirichletForm.mulS x y))
    (D.toDirichletForm.coeFn_toLp_mulS hx hz) (D.toDirichletForm.coeFn_toLp_mulS hy hz)
    (D.toDirichletForm.coeFn_toLp_mulS hx hy)
  have hR : ∫ ω, ((D.form.formToDomain z : D.form.dom) : Lp ℝ 2 μ) ω *
      G.toCLM x y ω ∂μ = 2 * ∫ ω, ((D.form.formToDomain z : D.form.dom) : Lp ℝ 2 μ) ω *
        G.gamma (D.form.formToDomain x) (D.form.formToDomain y) ω ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul (2 : ℝ) (G.gamma (D.form.formToDomain x)
      (D.form.formToDomain y))] with ω hω
    rw [G.toCLM_apply, hω, Pi.smul_apply, smul_eq_mul]
    ring
  have key : D.form.E (D.form.formToDomain (D.toDirichletForm.mulS x z)) (D.form.formToDomain y) +
      D.form.E (D.form.formToDomain (D.toDirichletForm.mulS y z)) (D.form.formToDomain x) -
      D.form.E (D.form.formToDomain z) (D.form.formToDomain (D.toDirichletForm.mulS x y)) =
      ∫ ω, ((D.form.formToDomain z : D.form.dom) : Lp ℝ 2 μ) ω * G.toCLM x y ω ∂μ := by
    rw [hR]
    linarith
  rw [D.ener_toDirichletForm, D.ener_toDirichletForm, D.ener_toDirichletForm]
  exact key

/--
connection to Γ is a carre du champ operator of `D.toDirichletForm` if and only if Γ = 2γ
(uniqueness in BH 1991, prop. I.4.1.3, p. 17, reused via `isCarreDuChamp_unique`, under density
(i)).
-/
theorem isCarreDuChamp_iff_eq_toCLM
    {Γ : D.toDirichletForm.Space →L[ℝ] D.toDirichletForm.Space →L[ℝ] Lp ℝ 1 μ} :
    D.toDirichletForm.IsCarreDuChamp Γ ↔ Γ = G.toCLM := by
  constructor
  · intro h
    exact D.toDirichletForm.isCarreDuChamp_unique D.denseRange_toLp h G.isCarreDuChamp_toCLM
  · intro h
    rw [h]
    exact G.isCarreDuChamp_toCLM

end CarreDuChamp

/-- The bilinear map γ = Γ/2 on the form domain, obtained by transport from the BH form space. -/
def halfBilin (Γ : D.toDirichletForm.Space →L[ℝ] D.toDirichletForm.Space →L[ℝ] Lp ℝ 1 μ) :
    D.form.dom →ₗ[ℝ] D.form.dom →ₗ[ℝ] Lp ℝ 1 μ :=
  (1 / 2 : ℝ) • ((Γ.toLinearMap₁₂.comp D.form.formToDomain.symm.toLinearMap).compl₂
    D.form.formToDomain.symm.toLinearMap)

/-- The domain bilinear map is one half of the form-space map under the inverse equivalence. -/
theorem halfBilin_apply (Γ : D.toDirichletForm.Space →L[ℝ] D.toDirichletForm.Space →L[ℝ] Lp ℝ 1 μ)
    (f g : D.form.dom) :
    D.halfBilin Γ f g = (1 / 2 : ℝ) • Γ (D.form.formToDomain.symm f)
      (D.form.formToDomain.symm g) :=
  rfl

/--
reverse connection: every carre du champ operator Γ of `D.toDirichletForm` in BH's sense defines the
datum γ = Γ/2; symmetry, positivity and continuity follow from BH prop. I.4.1.3 (p. 17) proved for
the form-space operator.
-/
def ofIsCarreDuChamp
    {Γ : D.toDirichletForm.Space →L[ℝ] D.toDirichletForm.Space →L[ℝ] Lp ℝ 1 μ}
    (hΓ : D.toDirichletForm.IsCarreDuChamp Γ) : D.CarreDuChamp where
  gamma := D.halfBilin Γ
  symm f g := by
    rw [D.halfBilin_apply, D.halfBilin_apply,
      D.toDirichletForm.isCarreDuChamp_symm D.denseRange_toLp hΓ]
  nonneg f := by
    rw [D.halfBilin_apply]
    have h := (Lp.coeFn_nonneg _).2 (D.toDirichletForm.isCarreDuChamp_nonneg D.denseRange_toLp hΓ
      (D.form.formToDomain.symm f))
    filter_upwards [h, Lp.coeFn_smul (1 / 2 : ℝ) (Γ (D.form.formToDomain.symm f)
      (D.form.formToDomain.symm f))] with ω h1 h2
    rw [h2, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (by norm_num) h1
  continuous := ⟨1 / 2 * ‖Γ‖, fun f g => by
    rw [D.halfBilin_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h : ‖Γ (D.form.formToDomain.symm f) (D.form.formToDomain.symm g)‖ ≤
        ‖Γ‖ * D.form.formNorm f * D.form.formNorm g :=
      Γ.le_opNorm₂ (D.form.formToDomain.symm f) (D.form.formToDomain.symm g)
    have hn : 0 ≤ ‖Γ‖ * D.form.formNorm f * D.form.formNorm g := by
      unfold QuadForm.formNorm
      positivity
    linarith⟩
  product f g h hf hg hh p q r hp hq hr := by
    have e : ∀ {a b c : D.form.dom}, AEBounded (μ := μ) ((a : Lp ℝ 2 μ) : Ω → ℝ) →
        AEBounded (μ := μ) ((b : Lp ℝ 2 μ) : Ω → ℝ) →
        (⇑(c : Lp ℝ 2 μ) =ᵐ[μ] fun x => (a : Lp ℝ 2 μ) x * (b : Lp ℝ 2 μ) x) →
        D.toDirichletForm.mulS (D.form.formToDomain.symm a) (D.form.formToDomain.symm b) =
          D.form.formToDomain.symm c := by
      intro a b c ha hb hc
      apply D.toDirichletForm.eq_of_ae
      filter_upwards [D.toDirichletForm.coeFn_toLp_mulS (D.formToDomain_symm_mem_bddSpace ha)
        (D.formToDomain_symm_mem_bddSpace hb), hc] with ω h1 h2
      rw [h1]
      change ((D.form.formToDomain (D.form.formToDomain.symm a) : D.form.dom) : Lp ℝ 2 μ) ω *
          ((D.form.formToDomain (D.form.formToDomain.symm b) : D.form.dom) : Lp ℝ 2 μ) ω =
        ((D.form.formToDomain (D.form.formToDomain.symm c) : D.form.dom) : Lp ℝ 2 μ) ω
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
      exact h2.symm
    have key := hΓ _ (D.formToDomain_symm_mem_bddSpace hf) _ (D.formToDomain_symm_mem_bddSpace hg) _
      (D.formToDomain_symm_mem_bddSpace hh)
    rw [e hf hh hp, e hg hh hq, e hf hg hr, D.ener_toDirichletForm, D.ener_toDirichletForm,
      D.ener_toDirichletForm, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply] at key
    have key' : D.form.E p g + D.form.E q f - D.form.E h r = ∫ x, (h : Lp ℝ 2 μ) x *
        Γ (D.form.formToDomain.symm f) (D.form.formToDomain.symm g) x ∂μ := by
      rw [key]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      change ((D.form.formToDomain (D.form.formToDomain.symm h) : D.form.dom) : Lp ℝ 2 μ) ω * _ = _
      rw [LinearEquiv.apply_symm_apply]
    have hR : ∫ x, (h : Lp ℝ 2 μ) x * (D.halfBilin Γ f g) x ∂μ =
        (1 / 2 : ℝ) * ∫ x, (h : Lp ℝ 2 μ) x * Γ (D.form.formToDomain.symm f)
          (D.form.formToDomain.symm g) x ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (Γ (D.form.formToDomain.symm f)
        (D.form.formToDomain.symm g))] with ω hω
      rw [D.halfBilin_apply, hω, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hR]
    linarith

/-- The carré du champ obtained from a BH representative is its transported half-bilinear map. -/
theorem ofIsCarreDuChamp_gamma
    {Γ : D.toDirichletForm.Space →L[ℝ] D.toDirichletForm.Space →L[ℝ] Lp ℝ 1 μ}
    (hΓ : D.toDirichletForm.IsCarreDuChamp Γ) : (D.ofIsCarreDuChamp hΓ).gamma = D.halfBilin Γ :=
  rfl

namespace CarreDuChamp
variable {D}

/-- The round-trip connection recovers Γ. -/
theorem toCLM_ofIsCarreDuChamp
    {Γ : D.toDirichletForm.Space →L[ℝ] D.toDirichletForm.Space →L[ℝ] Lp ℝ 1 μ}
    (hΓ : D.toDirichletForm.IsCarreDuChamp Γ) :
    ((D.ofIsCarreDuChamp hΓ).toCLM : D.toDirichletForm.Space →L[ℝ] D.toDirichletForm.Space →L[ℝ]
      Lp ℝ 1 μ) = Γ := by
  refine ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => ?_
  change (D.ofIsCarreDuChamp hΓ).toCLM x y = Γ x y
  rw [toCLM_apply, ofIsCarreDuChamp_gamma, halfBilin_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply, smul_smul]
  norm_num

/--
uniqueness of γ (BH 1991, prop. I.4.1.3, p. 17: "the uniqueness property follows easily"),
reused from (`isCarreDuChamp_unique`) via Γ = 2γ: two carre du champ data for the same local
form have the
same γ.
-/
theorem gamma_eq (G G' : D.CarreDuChamp) : G.gamma = G'.gamma := by
  have h : G.toCLM = G'.toCLM := (G'.isCarreDuChamp_iff_eq_toCLM).1 G.isCarreDuChamp_toCLM
  refine LinearMap.ext₂ fun f g => ?_
  rw [G.gamma_eq_half_smul_toCLM, G'.gamma_eq_half_smul_toCLM, h]

/-- uniqueness: the type of carre du champ data of a local form has at most one element. -/
instance instSubsingleton : Subsingleton D.CarreDuChamp :=
  ⟨fun G G' => by
    have h := gamma_eq G G'
    cases G
    cases G'
    change _ = _ at h
    subst h
    rfl⟩

end CarreDuChamp

/--
existence: a local Dirichlet form admits carre du champ data if and only if it admits such an
operator in the sense of BH 1991, def. I.4.1.2 (p. 17), property (R) (`admitsCarreDuChamp_iff`,
under density (i)).
-/
theorem nonempty_carreDuChamp_iff :
    Nonempty D.CarreDuChamp ↔ D.toDirichletForm.AdmitsCarreDuChamp := by
  constructor
  · rintro ⟨G⟩
    exact D.toDirichletForm.admitsCarreDuChamp_of_isCarreDuChamp G.isCarreDuChamp_toCLM
  · intro h
    obtain ⟨Γ, hΓ⟩ := D.toDirichletForm.exists_isCarreDuChamp D.denseRange_toLp h
    exact ⟨D.ofIsCarreDuChamp hΓ⟩

/-! ## C. Energy identity (BH I.6.1.1, clause (a) of `BHFunctionalCalculus`) -/

namespace CarreDuChamp
variable {D} (G : D.CarreDuChamp)

/--
BH 1991, prop. I.6.1.1 (p. 36), ℰ(f) = ½ ∫ Γ(f) dm, here with γ = Γ/2: for every f ∈ 𝔻, ℰ(f, f) = ∫
γ(f, f) dμ. Reuse of `isCarreDuChamp_integral_eq` (hypothesis "1 ∈ 𝔻, ℰ(1) = 0": EBM axiom (iv)) via
Γ = 2γ.
-/
theorem energy_eq_integral (f : D.form.dom) : D.form.E f f = ∫ x, G.gamma f f x ∂μ := by
  have he1 : ∀ᵐ ω ∂μ,
      D.toDirichletForm.toLp (D.form.formToDomain.symm D.one : D.toDirichletForm.Space) ω = 1 := by
    filter_upwards [D.coeFn_one] with ω h
    change ((D.form.formToDomain (D.form.formToDomain.symm D.one) : D.form.dom) :
      Lp ℝ 2 μ) ω = 1
    rw [LinearEquiv.apply_symm_apply]
    exact h
  have he : (D.form.formToDomain.symm D.one : D.toDirichletForm.Space) ∈
      D.toDirichletForm.bddSpace :=
    ⟨1, he1.mono fun ω h => by rw [h, abs_one]⟩
  have he0 : D.toDirichletForm.ener (D.form.formToDomain.symm D.one)
      (D.form.formToDomain.symm D.one) = 0 := by
    rw [D.ener_toDirichletForm, LinearEquiv.apply_symm_apply]
    exact D.energy_one_left D.one
  have h := D.toDirichletForm.isCarreDuChamp_integral_eq G.isCarreDuChamp_toCLM he he1 he0
    (D.form.formToDomain.symm f)
  rw [D.ener_toDirichletForm, LinearEquiv.apply_symm_apply] at h
  have h' : ∫ ω, G.toCLM (D.form.formToDomain.symm f) (D.form.formToDomain.symm f) ω ∂μ =
      2 * D.form.E f f := h
  have h2 : ∫ ω, G.toCLM (D.form.formToDomain.symm f) (D.form.formToDomain.symm f) ω ∂μ =
      2 * ∫ x, G.gamma f f x ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul (2 : ℝ) (G.gamma f f)] with ω hω
    rw [G.toCLM_apply, LinearEquiv.apply_symm_apply, hω, Pi.smul_apply, smul_eq_mul]
  linarith

end CarreDuChamp

/-! ## Locality of the carré du champ and local cancellation -/

/--
Generic version of `ebm_boundedProducts` for essentially bounded f, g ∈ 𝔻, there exists p ∈ 𝔻 with p
= f g a.e. (BH 1991, cor. I.3.3.2, p. 14). An API corollary: p is the product
`Capacity.DirichletForm.mulS` (`coeFn_toLp_mulS`), transported by `D.form.formToDomain`.
-/
theorem exists_mul_mem_of_aeBounded {f g : D.form.dom}
    (hf : AEBounded (μ := μ) ((f : Lp ℝ 2 μ) : Ω → ℝ))
    (hg : AEBounded (μ := μ) ((g : Lp ℝ 2 μ) : Ω → ℝ)) :
    ∃ p : D.form.dom, ⇑(p : Lp ℝ 2 μ) =ᵐ[μ] fun x => (f : Lp ℝ 2 μ) x * (g : Lp ℝ 2 μ) x := by
  refine ⟨D.form.formToDomain (D.toDirichletForm.mulS
    (D.form.formToDomain.symm f) (D.form.formToDomain.symm g)), ?_⟩
  have h := D.toDirichletForm.coeFn_toLp_mulS
    (D.formToDomain_symm_mem_bddSpace hf) (D.formToDomain_symm_mem_bddSpace hg)
  change ⇑((D.form.formToDomain _) : Lp ℝ 2 μ) =ᵐ[μ]
    fun x => ((D.form.formToDomain (D.form.formToDomain.symm f) : D.form.dom) : Lp ℝ 2 μ) x *
      ((D.form.formToDomain (D.form.formToDomain.symm g) : D.form.dom) : Lp ℝ 2 μ) x at h
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- The symmetric clamp Tₙ f = (−n) ∨ (f ∧ n), n ∈ ℕ, is bounded. -/
theorem aeBounded_clamp_nat (n : ℕ) (f : D.form.dom) :
    AEBounded (μ := μ) (((D.clamp (-(n : ℝ)) n f : D.form.dom) : Lp ℝ 2 μ) : Ω → ℝ) :=
  ⟨n, by filter_upwards [D.abs_clamp_le n f] with x hx; rwa [Real.norm_eq_abs]⟩

/--
Symmetric truncations converge in the form norm after transport through the form-space/domain
equivalence.
-/
theorem tendsto_clamp_formSpace (f : D.form.dom) :
    Tendsto (fun n : ℕ => D.form.formToDomain.symm (D.clamp (-(n : ℝ)) n f))
      atTop (𝓝 (D.form.formToDomain.symm f)) := by
  have e : ∀ n : ℕ,
      (D.form.formToDomain.symm (D.clamp (-(n : ℝ)) n f) : D.toDirichletForm.Space) =
        D.toDirichletForm.truncS n (D.form.formToDomain.symm f) := by
    intro n
    apply D.toDirichletForm.eq_of_ae
    have hl : D.toDirichletForm.toLp
        (D.form.formToDomain.symm (D.clamp (-(n : ℝ)) n f)) =
          ((D.clamp (-(n : ℝ)) n f : D.form.dom) : Lp ℝ 2 μ) := by
      change ((D.form.formToDomain (D.form.formToDomain.symm _) : D.form.dom) : Lp ℝ 2 μ) = _
      rw [LinearEquiv.apply_symm_apply]
    have hf : D.toDirichletForm.toLp (D.form.formToDomain.symm f) = (f : Lp ℝ 2 μ) := by
      change ((D.form.formToDomain (D.form.formToDomain.symm _) : D.form.dom) : Lp ℝ 2 μ) = _
      rw [LinearEquiv.apply_symm_apply]
    rw [hl, Capacity.DirichletForm.truncS, Capacity.DirichletForm.toLp_contract]
    filter_upwards [D.coeFn_clamp (-(n : ℝ)) n f,
      D.toDirichletForm.coe_contractLp
        (Capacity.DirichletForm.lipschitzWith_trunc n)
        (Capacity.DirichletForm.trunc_zero n) (D.form.formToDomain.symm f)]
      with x h1 h2
    rw [h1, h2, hf, max_comm]
  have h := D.toDirichletForm.tendsto_contract_trunc (D.form.formToDomain.symm f)
  change Tendsto (fun n => D.toDirichletForm.truncS n (D.form.formToDomain.symm f))
    atTop (𝓝 (D.form.formToDomain.symm f)) at h
  exact h.congr fun n => (e n).symm

namespace CarreDuChamp
variable {D} (G : D.CarreDuChamp)

/-- γ(Tₙ f, Tₙ g) → γ(f, g) in L¹ (continuity of Γ = 2γ, `toCLM`). -/
theorem tendsto_gamma_clamp (f g : D.form.dom) :
    Tendsto (fun n : ℕ => G.gamma (D.clamp (-(n : ℝ)) n f) (D.clamp (-(n : ℝ)) n g)) atTop
      (𝓝 (G.gamma f g)) := by
  have h := ((G.toCLM.continuous₂.tendsto (D.form.formToDomain.symm f,
    D.form.formToDomain.symm g)).comp
      ((D.tendsto_clamp_formSpace f).prodMk_nhds (D.tendsto_clamp_formSpace g))).const_smul
        (1 / 2 : ℝ)
  rw [G.gamma_eq_half_smul_toCLM f g]
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, Function.uncurry_apply_pair]
  exact (G.gamma_eq_half_smul_toCLM _ _).symm

/-- Locality of γ for bounded f, g: (1.2) and (L₂). -/
theorem gamma_eq_zero_of_mul_of_aeBounded (f g : D.form.dom) (a : ℝ)
    (hf : AEBounded (μ := μ) ((f : Lp ℝ 2 μ) : Ω → ℝ))
    (hg : AEBounded (μ := μ) ((g : Lp ℝ 2 μ) : Ω → ℝ))
    (h : ∀ᵐ x ∂μ, ((f : Lp ℝ 2 μ) x + a) * (g : Lp ℝ 2 μ) x = 0) : G.gamma f g = 0 := by
  apply Lp.ext
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_zero ℝ 1 μ).symm
  apply D.ae_eq_zero_of_integral_mul_eq_zero
  rintro k ⟨C, hC⟩
  have hk : AEBounded (μ := μ) ((k : Lp ℝ 2 μ) : Ω → ℝ) :=
    ⟨C, by filter_upwards [hC] with x hx; rwa [Real.norm_eq_abs]⟩
  obtain ⟨p, hp⟩ := D.exists_mul_mem_of_aeBounded hf hk
  obtain ⟨q, hq⟩ := D.exists_mul_mem_of_aeBounded hg hk
  obtain ⟨r, hr⟩ := D.exists_mul_mem_of_aeBounded hf hg
  have h1 := G.product f g k hf hg hk p q r hp hq hr
  have hpg : D.form.E (p + a • k) g = 0 := by
    apply D.strongLocality (p + a • k) g 0
    filter_upwards [h, hp, Lp.coeFn_add (p : Lp ℝ 2 μ) (a • (k : Lp ℝ 2 μ)),
      Lp.coeFn_smul a (k : Lp ℝ 2 μ)] with x hx hpx h3 h4
    rw [Submodule.coe_add, Submodule.coe_smul, h3, Pi.add_apply, h4, Pi.smul_apply, hpx,
      smul_eq_mul, add_zero]
    linear_combination (k : Lp ℝ 2 μ) x * hx
  have hqf : D.form.E q f = 0 := by
    rw [D.form.symm]
    apply D.strongLocality f q a
    filter_upwards [h, hq] with x hx hqx
    rw [hqx]
    linear_combination (k : Lp ℝ 2 μ) x * hx
  have hr' : r = (-a) • g := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [h, hr, Lp.coeFn_smul (-a) (g : Lp ℝ 2 μ)] with x hx hrx h3
    rw [Submodule.coe_smul, h3, Pi.smul_apply, hrx, smul_eq_mul]
    linear_combination hx
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at hpg
  rw [hqf, hr', map_smul, smul_eq_mul] at h1
  linarith

/--
locality of γ, (L₂) transported to the carre du champ (a consequence of BH I.5.1.3 and 4.1.3, not
stated separately by BH): for f, g ∈ 𝔻 and a ∈ ℝ, (f + a) g = 0 a.e. ⇒ γ(f, g) = 0.
-/
theorem gamma_eq_zero_of_mul (f g : D.form.dom) (a : ℝ)
    (h : ∀ᵐ x ∂μ, ((f : Lp ℝ 2 μ) x + a) * (g : Lp ℝ 2 μ) x = 0) : G.gamma f g = 0 := by
  have hz : ∀ n : ℕ, |a| ≤ n →
      G.gamma (D.clamp (-(n : ℝ)) n f) (D.clamp (-(n : ℝ)) n g) = 0 := by
    intro n hn
    refine G.gamma_eq_zero_of_mul_of_aeBounded _ _ a (D.aeBounded_clamp_nat n f)
      (D.aeBounded_clamp_nat n g) ?_
    filter_upwards [h, D.coeFn_clamp (-(n : ℝ)) n f, D.coeFn_clamp (-(n : ℝ)) n g] with x hx h1 h2
    rw [h1, h2]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rcases mul_eq_zero.1 hx with h3 | h3
    · have hfx : (f : Lp ℝ 2 μ) x = -a := by linarith
      have ha := abs_le.1 hn
      rw [hfx, min_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    · rw [h3, min_eq_left hn0, max_eq_right (show -(n : ℝ) ≤ 0 by linarith), mul_zero]
  have hev : (fun n : ℕ => G.gamma (D.clamp (-(n : ℝ)) n f) (D.clamp (-(n : ℝ)) n g)) =ᶠ[atTop]
      fun _ => 0 := by
    filter_upwards [eventually_ge_atTop ⌈|a|⌉₊] with n hn
    exact hz n ((Nat.le_ceil _).trans (by exact_mod_cast hn))
  exact tendsto_nhds_unique (G.tendsto_gamma_clamp f g) (tendsto_const_nhds.congr' hev.symm)

/--
Local cancellation of γ for bounded v, w, h: h w = 0 a.e. ⇒ h γ(v, w) = 0 a.e. ((1.2) and (L₂) with
the test function h φ).
-/
theorem mul_gamma_eq_zero_of_aeBounded (v w h : D.form.dom)
    (hv : AEBounded (μ := μ) ((v : Lp ℝ 2 μ) : Ω → ℝ))
    (hw : AEBounded (μ := μ) ((w : Lp ℝ 2 μ) : Ω → ℝ))
    (hh : AEBounded (μ := μ) ((h : Lp ℝ 2 μ) : Ω → ℝ))
    (hhw : ∀ᵐ x ∂μ, (h : Lp ℝ 2 μ) x * (w : Lp ℝ 2 μ) x = 0) :
    ∀ᵐ x ∂μ, (h : Lp ℝ 2 μ) x * G.gamma v w x = 0 := by
  have hm : MemLp ((h : Lp ℝ 2 μ) : Ω → ℝ) ∞ μ := hh.memLp_top (Lp.aestronglyMeasurable _)
  set k : Lp ℝ 1 μ := boundedMul ((h : Lp ℝ 2 μ) : Ω → ℝ) hm (G.gamma v w) with hk
  have hk0 : ⇑k =ᵐ[μ] 0 := by
    apply D.ae_eq_zero_of_integral_mul_eq_zero
    rintro φ ⟨Cφ, hCφ⟩
    have hφ : AEBounded (μ := μ) ((φ : Lp ℝ 2 μ) : Ω → ℝ) :=
      ⟨Cφ, by filter_upwards [hCφ] with x hx; rwa [Real.norm_eq_abs]⟩
    obtain ⟨ψ, hψ⟩ := D.exists_mul_mem_of_aeBounded hφ hh
    have hψb : AEBounded (μ := μ) ((ψ : Lp ℝ 2 μ) : Ω → ℝ) := by
      obtain ⟨C₁, h₁⟩ := hφ
      obtain ⟨C₂, h₂⟩ := hh
      refine ⟨C₁ * C₂, ?_⟩
      filter_upwards [hψ, h₁, h₂] with x a b c
      rw [a, norm_mul]
      exact mul_le_mul b c (norm_nonneg _) ((norm_nonneg _).trans b)
    obtain ⟨p, hp⟩ := D.exists_mul_mem_of_aeBounded hv hψb
    obtain ⟨q, hq⟩ := D.exists_mul_mem_of_aeBounded hw hψb
    obtain ⟨r, hr⟩ := D.exists_mul_mem_of_aeBounded hv hw
    have h1 := G.product v w ψ hv hw hψb p q r hp hq hr
    have e1 : D.form.E p w = 0 := by
      apply D.strongLocality p w 0
      filter_upwards [hp, hψ, hhw] with x a b c
      rw [a, b, add_zero]
      linear_combination (v : Lp ℝ 2 μ) x * (φ : Lp ℝ 2 μ) x * c
    have e2 : D.form.E q v = 0 := by
      apply D.strongLocality q v 0
      filter_upwards [hq, hψ, hhw] with x a b c
      rw [a, b, add_zero]
      linear_combination (v : Lp ℝ 2 μ) x * (φ : Lp ℝ 2 μ) x * c
    have e3 : D.form.E ψ r = 0 := by
      apply D.strongLocality ψ r 0
      filter_upwards [hr, hψ, hhw] with x a b c
      rw [a, b, add_zero]
      linear_combination (v : Lp ℝ 2 μ) x * (φ : Lp ℝ 2 μ) x * c
    rw [e1, e2, e3] at h1
    have hcongr : ∫ x, (φ : Lp ℝ 2 μ) x * k x ∂μ = ∫ x, (ψ : Lp ℝ 2 μ) x * G.gamma v w x ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [coeFn_boundedMul ((h : Lp ℝ 2 μ) : Ω → ℝ) hm (G.gamma v w), hψ] with x a b
      rw [a, b]
      ring
    rw [hcongr]
    linarith
  filter_upwards [hk0, coeFn_boundedMul ((h : Lp ℝ 2 μ) : Ω → ℝ) hm (G.gamma v w)] with x a b
  rw [← b, a]
  rfl

/--
Local cancellation of γ (functional support; replaces the energy measure of BH 5.2 for the carre du
champ): for v, w ∈ 𝔻 and essentially bounded h ∈ 𝔻, h w = 0 a.e. ⇒ h γ(v, w) = 0 a.e.
-/
theorem mul_gamma_eq_zero (v w h : D.form.dom) (hh : AEBounded (μ := μ) ((h : Lp ℝ 2 μ) : Ω → ℝ))
    (hhw : ∀ᵐ x ∂μ, (h : Lp ℝ 2 μ) x * (w : Lp ℝ 2 μ) x = 0) :
    ∀ᵐ x ∂μ, (h : Lp ℝ 2 μ) x * G.gamma v w x = 0 := by
  have hm : MemLp ((h : Lp ℝ 2 μ) : Ω → ℝ) ∞ μ := hh.memLp_top (Lp.aestronglyMeasurable _)
  obtain ⟨C, hC⟩ := hh
  have hC' : ∀ᵐ x ∂μ, |(h : Lp ℝ 2 μ) x| ≤ C := by
    filter_upwards [hC] with x hx
    rwa [← Real.norm_eq_abs]
  have hz : ∀ n : ℕ, boundedMul ((h : Lp ℝ 2 μ) : Ω → ℝ) hm
      (G.gamma (D.clamp (-(n : ℝ)) n v) (D.clamp (-(n : ℝ)) n w)) = 0 := by
    intro n
    apply Lp.ext
    have h0 := G.mul_gamma_eq_zero_of_aeBounded _ _ h (D.aeBounded_clamp_nat n v)
      (D.aeBounded_clamp_nat n w) ⟨C, hC⟩ (by
        filter_upwards [hhw, D.coeFn_clamp (-(n : ℝ)) n w] with x a b
        rw [b]
        rcases mul_eq_zero.1 a with c | c
        · rw [c, zero_mul]
        · rw [c, min_eq_left (Nat.cast_nonneg n), max_eq_right (by
            linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]), mul_zero])
    filter_upwards [h0, coeFn_boundedMul ((h : Lp ℝ 2 μ) : Ω → ℝ) hm
      (G.gamma (D.clamp (-(n : ℝ)) n v) (D.clamp (-(n : ℝ)) n w)), Lp.coeFn_zero ℝ 1 μ]
      with x a b c
    rw [b, c, a]
    rfl
  have hlim := tendsto_iff_norm_sub_tendsto_zero.1 (G.tendsto_gamma_clamp v w)
  have hb : ∀ n : ℕ, ‖boundedMul ((h : Lp ℝ 2 μ) : Ω → ℝ) hm (G.gamma v w)‖ ≤
      C * ‖G.gamma (D.clamp (-(n : ℝ)) n v) (D.clamp (-(n : ℝ)) n w) - G.gamma v w‖ := by
    intro n
    have e := boundedMul_sub ((h : Lp ℝ 2 μ) : Ω → ℝ) hm
      (G.gamma (D.clamp (-(n : ℝ)) n v) (D.clamp (-(n : ℝ)) n w)) (G.gamma v w)
    rw [hz n, zero_sub] at e
    rw [← norm_neg, ← e]
    exact norm_boundedMul_le _ hm _ hC'
  have hlim' := hlim.const_mul C
  rw [mul_zero] at hlim'
  have h0 : ‖boundedMul ((h : Lp ℝ 2 μ) : Ω → ℝ) hm (G.gamma v w)‖ = 0 :=
    le_antisymm (ge_of_tendsto' hlim' hb) (norm_nonneg _)
  filter_upwards [coeFn_boundedMul ((h : Lp ℝ 2 μ) : Ω → ℝ) hm (G.gamma v w),
    Lp.coeFn_zero ℝ 1 μ] with x a b
  rw [← a, norm_eq_zero.1 h0, b]
  rfl

end CarreDuChamp

end LocalDirichletForm

end ErrorCalculus
