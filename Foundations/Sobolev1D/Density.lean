import Foundations.Sobolev1D.WeightedMollify
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory Filter Set Function
open scoped Topology ENNReal ContDiff
namespace Foundations

/-- The graph of differentiation on C¹ compactly supported functions, inside L² × L². -/
def C1cGraph (ρ : ℝ → ℝ) : Set (Lp ℝ 2 (densityMeasure ρ) × Lp ℝ 2 (densityMeasure ρ)) :=
  {z | ∃ (f : ℝ → ℝ) (hf : MemLp f 2 (densityMeasure ρ))
      (hdf : MemLp (deriv f) 2 (densityMeasure ρ)),
      ContDiff ℝ 1 f ∧ HasCompactSupport f ∧ z = (hf.toLp f, hdf.toLp (deriv f))}

/-- Membership of the closure is equivalent to an actual approximating sequence. -/
theorem exists_C1c_seq_of_mem_closure {ρ : ℝ → ℝ}
    {U G : Lp ℝ 2 (densityMeasure ρ)} (h : (U,G) ∈ closure (C1cGraph ρ)) :
    ∃ (f : ℕ → ℝ → ℝ) (hf : ∀ n, MemLp (f n) 2 (densityMeasure ρ))
      (hdf : ∀ n, MemLp (deriv (f n)) 2 (densityMeasure ρ)),
      (∀ n, ContDiff ℝ 1 (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 U) ∧
      Tendsto (fun n => (hdf n).toLp (deriv (f n))) atTop (𝓝 G) := by
  obtain ⟨z,hz,ht⟩ := mem_closure_iff_seq_limit.mp h
  choose f hf hdf hC hc he using hz
  have hze : z = fun n => ((hf n).toLp (f n), (hdf n).toLp (deriv (f n))) := funext he
  rw [hze] at ht
  refine ⟨f,hf,hdf,hC,hc,?_,?_⟩
  · exact (continuous_fst.tendsto (U,G)).comp ht
  · exact (continuous_snd.tendsto (U,G)).comp ht

theorem compact_AC_mem_closure_C1cGraph {ρ v : ℝ → ℝ}
    (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (hv : ∀ a b, AbsolutelyContinuousOnInterval v a b) (hc : HasCompactSupport v)
    (hvLp : MemLp v 2 (densityMeasure ρ)) (hdLp : MemLp (deriv v) 2 (densityMeasure ρ)) :
    (hvLp.toLp v,hdLp.toLp (deriv v)) ∈ closure (C1cGraph ρ) := by
  obtain ⟨w,hw,hdw,he,hC,hs,ht,hdt⟩ := exists_mollification_tendsto hρ hpos hv hc hvLp hdLp
  apply mem_closure_iff_seq_limit.mpr
  exact ⟨fun n => ((hw n).toLp (w n),(hdw n).toLp (deriv (w n))),
    fun n => ⟨w n,hw n,hdw n,(hC n).of_le (by simp),hs n,rfl⟩, ht.prodMk_nhds hdt⟩

/-- Closure combines truncation and smoothing, avoiding a choice of numerical diagonal. -/
theorem primitive_mem_closure_C1cGraph {ρ g : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) (c : ℝ)
    (hu : MemLp (primitiveRepresentative c g) 2 (densityMeasure ρ))
    (hg : MemLp g 2 (densityMeasure ρ)) :
    (hu.toLp (primitiveRepresentative c g),hg.toLp g) ∈ closure (C1cGraph ρ) := by
  obtain ⟨v,h,hv,hh,hexp,hs,hac,hd,ht,hdt⟩ := exists_truncation_tendsto hρ hpos c hu hg
  apply isClosed_closure.mem_of_tendsto (ht.prodMk_nhds hdt)
  apply Eventually.of_forall
  intro n
  have hder : MemLp (deriv (v n)) 2 (densityMeasure ρ) := (hh n).ae_eq (hd n).symm
  have he : hder.toLp (deriv (v n)) = (hh n).toLp (h n) := by
    apply Lp.ext
    exact hder.coeFn_toLp.trans ((hd n).trans (hh n).coeFn_toLp.symm)
  have hm := compact_AC_mem_closure_C1cGraph hρ hpos (hac n) (hs n) (hv n) hder
  rwa [he] at hm

/-- C¹ compact support is dense in the weighted H¹ graph norm. -/
theorem exists_C1c_tendsto_H1 {ρ g : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) (c : ℝ)
    (hu : MemLp (primitiveRepresentative c g) 2 (densityMeasure ρ))
    (hg : MemLp g 2 (densityMeasure ρ)) :
    ∃ (f : ℕ → ℝ → ℝ) (hf : ∀ n, MemLp (f n) 2 (densityMeasure ρ))
      (hdf : ∀ n, MemLp (deriv (f n)) 2 (densityMeasure ρ)),
      (∀ n, ContDiff ℝ 1 (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp (primitiveRepresentative c g))) ∧
      Tendsto (fun n => (hdf n).toLp (deriv (f n))) atTop (𝓝 (hg.toLp g)) :=
  exists_C1c_seq_of_mem_closure (primitive_mem_closure_C1cGraph hρ hpos c hu hg)

/-- The class version keeps the representative hypothesis explicit. -/
theorem exists_C1c_tendsto_H1_Lp {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (U G : Lp ℝ 2 (densityMeasure ρ)) (c : ℝ)
    (hrep : (U : ℝ → ℝ) =ᵐ[densityMeasure ρ] primitiveRepresentative c G) :
    ∃ (f : ℕ → ℝ → ℝ) (hf : ∀ n, MemLp (f n) 2 (densityMeasure ρ))
      (hdf : ∀ n, MemLp (deriv (f n)) 2 (densityMeasure ρ)),
      (∀ n, ContDiff ℝ 1 (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 U) ∧
      Tendsto (fun n => (hdf n).toLp (deriv (f n))) atTop (𝓝 G) := by
  have hu := (Lp.memLp U).ae_eq hrep
  have he : hu.toLp (primitiveRepresentative c G) = U := Lp.ext (hu.coeFn_toLp.trans hrep.symm)
  simpa only [he, Lp.toLp_coeFn] using exists_C1c_tendsto_H1 hρ hpos c hu (Lp.memLp G)

/-- An AC function is exactly the primitive of its derivative plus its value at zero. -/
theorem eq_primitiveRepresentative_of_locallyAC {v : ℝ → ℝ}
    (hv : ∀ a b, AbsolutelyContinuousOnInterval v a b) :
    v = primitiveRepresentative (v 0) (deriv v) := by
  ext x
  have h := (hv 0 x).integral_deriv_eq_sub
  dsimp [primitiveRepresentative, primitive]
  linarith

/-- H¹ membership is the projection of the closed C¹_c graph; no new normed space is introduced. -/
def MemH1Density (ρ : ℝ → ℝ) (U : Lp ℝ 2 (densityMeasure ρ)) : Prop :=
  ∃ G : Lp ℝ 2 (densityMeasure ρ), (U,G) ∈ closure (C1cGraph ρ)

/--
Membership in the closed weighted Sobolev domain is equivalent to an absolutely continuous
representative with finite weighted derivative energy.
-/
theorem mem_H1_iff_exists_absolutelyContinuous_representative {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) (U : Lp ℝ 2 (densityMeasure ρ)) :
    MemH1Density ρ U ↔ ∃ v : ℝ → ℝ, (U : ℝ → ℝ) =ᵐ[densityMeasure ρ] v ∧
      (∀ a b, AbsolutelyContinuousOnInterval v a b) ∧ MemLp (deriv v) 2 (densityMeasure ρ) := by
  constructor
  · rintro ⟨G,hG⟩
    obtain ⟨f,hf,hdf,hC,hc,ht,hdt⟩ := exists_C1c_seq_of_mem_closure hG
    obtain ⟨v,c,hform,he,hcont,hac,hder,hderμ⟩ :=
      exists_absolutelyContinuous_representative_Lp hρ hpos (fun n => (hf n).toLp (f n)) U G
        hC (fun n => (hf n).coeFn_toLp) hdf ht hdt
    exact ⟨v,he,hac,(Lp.memLp G).ae_eq hderμ.symm⟩
  · rintro ⟨v,he,hac,hd⟩
    have hv : MemLp v 2 (densityMeasure ρ) := (Lp.memLp U).ae_eq he
    have hp := eq_primitiveRepresentative_of_locallyAC hac
    have hu : MemLp (primitiveRepresentative (v 0) (deriv v)) 2 (densityMeasure ρ) := by
      rw [← hp]
      exact hv
    have hclass : hu.toLp (primitiveRepresentative (v 0) (deriv v)) = U := by
      apply Lp.ext
      have hep : primitiveRepresentative (v 0) (deriv v) =ᵐ[densityMeasure ρ] v :=
        Eventually.of_forall (fun x => congrFun hp.symm x)
      exact hu.coeFn_toLp.trans (hep.trans he.symm)
    refine ⟨hd.toLp (deriv v), ?_⟩
    have hm := primitive_mem_closure_C1cGraph hρ hpos (v 0) hu hd
    rwa [hclass] at hm

/-- Compact support supplies the boundedness required by C¹_b applications. -/
theorem C1c_bounded {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) ∧ Continuous (deriv f) ∧ (∃ M : ℝ, ∀ x, ‖deriv f x‖ ≤ M) :=
  ⟨hc.exists_bound_of_continuous hf.continuous, hf.continuous_deriv_one,
    hc.deriv.exists_bound_of_continuous hf.continuous_deriv_one⟩

end Foundations
