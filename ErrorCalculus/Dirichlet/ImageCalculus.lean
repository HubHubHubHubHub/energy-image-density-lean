import ErrorCalculus.Dirichlet.ImageDomain
import ErrorCalculus.Dirichlet.ClosureCalculusLimits

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace ErrorCalculus

namespace ImageTest
variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

theorem memLp_top (H : ImageTest α) : MemLp H ∞ ν := by
  obtain ⟨C, hC⟩ := H.bound
  exact memLp_top_of_bound H.measurable.aestronglyMeasurable C (ae_of_all _ hC)

/-- Moving a bounded coefficient into the test function. -/
theorem integral_boundedMul (H K : ImageTest α) (f : Lp ℝ 1 ν) :
    H.integral (boundedMul K K.memLp_top f) = (H.mul K).integral f := by
  apply integral_congr_ae
  filter_upwards [coeFn_boundedMul K K.memLp_top f] with x hx
  change H x * boundedMul K K.memLp_top f x = (H x * K x) * f x
  rw [hx, mul_assoc]

/-- derivative coefficients are measurable bounded tests. -/
def derivative {k : ℕ} (u : Fin k → Lp ℝ 2 ν) {Φ : (Fin k → ℝ) → ℝ} {L : ℝ≥0}
    (hC : ContDiff ℝ 1 Φ) (hL : LipschitzWith L Φ) (i : Fin k) : ImageTest α where
  toFun x := fderiv ℝ Φ (fun j => u j x) (Pi.single i 1)
  measurable := by
    have ht : Continuous (fun z => fderiv ℝ Φ z (Pi.single i 1)) :=
      (hC.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact ht.measurable.comp (measurable_pi_lambda _ fun j => (Lp.stronglyMeasurable (u j)).measurable)
  bound := ⟨L, fun x => by simpa only [Real.norm_eq_abs] using fderiv_coefficient_bound hL _ i⟩

end ImageTest

namespace ErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ErrorStructure Ω μ) {m : ℕ} (X : Fin m → Lp ℝ 2 μ)

/-- The full C¹ Lipschitz calculus descends by testing and uniqueness. -/
theorem imageData_calculus (k : ℕ) (hk : 0 < k)
    (u : Fin k → S.toErrorData.imageDom X) (Φ : (Fin k → ℝ) → ℝ) (L : ℝ≥0)
    (hC : ContDiff ℝ 1 Φ) (hL : LipschitzWith L Φ) (w : Lp ℝ 2 (imageLaw X))
    (hw : ⇑w =ᵐ[imageLaw X] fun x => Φ (fun i => (u i : Lp ℝ 2 (imageLaw X)) x)) :
    ∃ hd : w ∈ S.toErrorData.imageDom X, ∀ v : S.toErrorData.imageDom X,
      ⇑(S.toErrorData.imageGamma X ⟨w, hd⟩ v) =ᵐ[imageLaw X] fun x => ∑ i,
        fderiv ℝ Φ (fun j => (u j : Lp ℝ 2 (imageLaw X)) x) (Pi.single i 1) *
          S.toErrorData.imageGamma X (u i) v x := by
  let T := S.toErrorData.imageLift X
  have ht := pullback_composition X (fun i => (u i : Lp ℝ 2 (imageLaw X))) Φ w hw
  obtain ⟨hd, hchain⟩ := S.calc k hk (fun i => T (u i)) Φ L hC hL (pullback X w) ht
  refine ⟨hd, fun v => ?_⟩
  let a : Fin k → ImageTest (Fin m → ℝ) := fun i =>
    ImageTest.derivative (fun j => (u j : Lp ℝ 2 (imageLaw X))) hC hL i
  let b : Fin k → ImageTest Ω := fun i =>
    (a i).comp (imageRepresentative X) (measurable_imageRepresentative X)
  have hsource : S.Γ (T ⟨w, hd⟩) (T v) =
      ∑ i, boundedMul (b i) (b i).memLp_top (S.Γ (T (u i)) (T v)) := by
    apply Lp.ext
    filter_upwards [hchain (T v),
      ae_all_iff.mpr (fun i => pullback_ae_eq X (u i)),
      lp_coeFn_sum Finset.univ (fun i => boundedMul (b i) (b i).memLp_top (S.Γ (T (u i)) (T v))),
      ae_all_iff.mpr (fun i => coeFn_boundedMul (b i) (b i).memLp_top (S.Γ (T (u i)) (T v)))]
      with ω hc hu hs hb
    change S.Γ ⟨pullback X w, hd⟩ (T v) ω = _ at hc ⊢
    rw [hc, hs]
    apply Finset.sum_congr rfl
    intro i _
    rw [hb i]
    change fderiv ℝ Φ (fun j => pullback X (u j) ω) (Pi.single i 1) * _ =
      fderiv ℝ Φ (fun j => (u j : Lp ℝ 2 (imageLaw X)) (imageRepresentative X ω))
        (Pi.single i 1) * _
    simp only [hu]
  have he : S.toErrorData.imageGamma X ⟨w, hd⟩ v =
      ∑ i, boundedMul (a i) (a i).memLp_top (S.toErrorData.imageGamma X (u i) v) := by
    apply ImageTest.eq_of_integral_eq
    intro H
    rw [S.toErrorData.imageGamma_characterization]
    change (H.comp (imageRepresentative X) (measurable_imageRepresentative X)).integral
      (S.Γ (T ⟨w, hd⟩) (T v)) = _
    rw [hsource, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [ImageTest.integral_boundedMul, ImageTest.integral_boundedMul,
      S.toErrorData.imageGamma_characterization]
    rfl
  rw [he]
  filter_upwards [lp_coeFn_sum Finset.univ
    (fun i => boundedMul (a i) (a i).memLp_top (S.toErrorData.imageGamma X (u i) v)),
    ae_all_iff.mpr (fun i => coeFn_boundedMul (a i) (a i).memLp_top
      (S.toErrorData.imageGamma X (u i) v))] with x hs ha
  rw [hs]
  exact Finset.sum_congr rfl (fun i _ => ha i)

end ErrorStructure
end ErrorCalculus
