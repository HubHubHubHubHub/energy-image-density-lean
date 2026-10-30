import Foundations.Chaos.Cylinders
import Mathlib.Algebra.BigOperators.Finsupp.Basic

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace Foundations

/-- Unnormalised cylindrical Hermite polynomial. -/
def hermiteInfFun (α : ℕ →₀ ℕ) (x : ℕ → ℝ) : ℝ :=
  α.prod (fun i n => hermiteFun n (x i))

/-- Normalisation is the product of the one-dimensional normalisations. -/
def hermiteNormalizedFunInf (α : ℕ →₀ ℕ) (x : ℕ → ℝ) : ℝ :=
  α.prod (fun i n => hermiteUnit n (x i))

def hermiteFactorInf (α : ℕ →₀ ℕ) : ℝ :=
  α.prod (fun _ n => Real.sqrt (n.factorial : ℝ))

theorem hermiteFactorInf_pos (α : ℕ →₀ ℕ) : 0 < hermiteFactorInf α :=
  Finset.prod_pos (fun _ _ => Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos _)))

theorem hermiteNormalizedFunInf_eq (α : ℕ →₀ ℕ) (x : ℕ → ℝ) :
    hermiteNormalizedFunInf α x = (hermiteFactorInf α)⁻¹ * hermiteInfFun α x := by
  simp [hermiteNormalizedFunInf,hermiteFactorInf,hermiteInfFun,Finsupp.prod,
    hermiteUnit,Finset.prod_mul_distrib]

theorem hermiteInfFun_eq_restrict (α : ℕ →₀ ℕ) {s : Finset ℕ}
    (hs : α.support ⊆ s) (x : ℕ → ℝ) :
    hermiteInfFun α x = hermiteD (fun i : s => α i) (s.restrict x) := by
  rw [hermiteInfFun, α.prod_of_support_subset hs _ (by intros; simp [hermiteFun])]
  exact (Finset.prod_attach s (fun i => hermiteFun (α i) (x i))).symm

theorem hermiteNormalizedFunInf_eq_restrict (α : ℕ →₀ ℕ) {s : Finset ℕ}
    (hs : α.support ⊆ s) (x : ℕ → ℝ) :
    hermiteNormalizedFunInf α x =
      hermiteNormalizedFunD (fun i : s => α i) (s.restrict x) := by
  rw [hermiteNormalizedFunInf, α.prod_of_support_subset hs _ (by intros; simp)]
  exact (Finset.prod_attach s (fun i => hermiteUnit (α i) (x i))).symm

theorem memLp_hermiteInfFun (α : ℕ →₀ ℕ) : MemLp (hermiteInfFun α) 2 gaussianInf := by
  have h := (memLp_hermiteD (fun i : α.support => α i)).comp_measurePreserving
    (gaussianInf_restrict_preserving α.support)
  simpa only [Function.comp_def, ← hermiteInfFun_eq_restrict α (le_refl _)] using h

theorem memLp_hermiteNormalizedFunInf (α : ℕ →₀ ℕ) :
    MemLp (hermiteNormalizedFunInf α) 2 gaussianInf := by
  have h := (memLp_hermiteNormalizedFunD (fun i : α.support => α i)).comp_measurePreserving
    (gaussianInf_restrict_preserving α.support)
  simpa only [Function.comp_def, ← hermiteNormalizedFunInf_eq_restrict α (le_refl _)] using h

/-- The normalised infinite-product Hermite class. -/
def hermiteInf (α : ℕ →₀ ℕ) : Lp ℝ 2 gaussianInf :=
  (memLp_hermiteNormalizedFunInf α).toLp _

theorem coe_hermiteInf (α : ℕ →₀ ℕ) : hermiteInf α =ᵐ[gaussianInf] hermiteNormalizedFunInf α :=
  (memLp_hermiteNormalizedFunInf α).coeFn_toLp

theorem hermiteInf_eq_cylinder (α : ℕ →₀ ℕ) {s : Finset ℕ} (hs : α.support ⊆ s) :
    hermiteInf α = gaussianCylinderLp s (hermiteNormalizedD (fun i : s => α i)) := by
  apply Lp.ext
  filter_upwards [coe_hermiteInf α, coe_gaussianCylinderLp s (hermiteNormalizedD (fun i : s => α i)),
    (gaussianInf_restrict_preserving s).quasiMeasurePreserving.ae_eq
      (coe_hermiteNormalizedD (fun i : s => α i))] with x hx hy hz
  simp only [Function.comp_apply] at hz
  rw [hx,hy,hz]
  exact hermiteNormalizedFunInf_eq_restrict α hs x

/-- Extension of a finite multi-index by zero. -/
def extendHermiteIndex (s : Finset ℕ) (α : s → ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset s (fun i => if h : i ∈ s then α ⟨i,h⟩ else 0)
    (by intro i hi; by_contra h; simp [h] at hi)

@[simp] theorem extendHermiteIndex_apply (s : Finset ℕ) (α : s → ℕ) (i : s) :
    extendHermiteIndex s α i = α i := by simp [extendHermiteIndex]

theorem support_extendHermiteIndex (s : Finset ℕ) (α : s → ℕ) :
    (extendHermiteIndex s α).support ⊆ s := Finsupp.support_onFinset_subset

theorem gaussianCylinderLp_hermite (s : Finset ℕ) (α : s → ℕ) :
    gaussianCylinderLp s (hermiteNormalizedD α) = hermiteInf (extendHermiteIndex s α) := by
  rw [hermiteInf_eq_cylinder _ (support_extendHermiteIndex s α)]
  simp

theorem finsupp_eq_of_restrict {α β : ℕ →₀ ℕ} {s : Finset ℕ}
    (ha : α.support ⊆ s) (hb : β.support ⊆ s)
    (h : (fun i : s => α i) = fun i : s => β i) : α = β := by
  ext i
  by_cases hi : i ∈ s
  · exact congrFun h ⟨i,hi⟩
  · rw [Finsupp.notMem_support_iff.mp (fun hm => hi (ha hm)),
      Finsupp.notMem_support_iff.mp (fun hm => hi (hb hm))]

theorem orthonormal_hermiteInf : Orthonormal ℝ hermiteInf := by
  classical
  rw [orthonormal_iff_ite]
  intro α β
  let s := α.support ∪ β.support
  have ha : α.support ⊆ s := Finset.subset_union_left
  have hb : β.support ⊆ s := Finset.subset_union_right
  rw [hermiteInf_eq_cylinder α ha,hermiteInf_eq_cylinder β hb,
    (gaussianCylinderLp s).inner_map_map,
    orthonormal_iff_ite.mp orthonormal_hermiteNormalizedD]
  congr 1
  exact propext ⟨finsupp_eq_of_restrict ha hb, fun h => by rw [h]⟩

end Foundations
