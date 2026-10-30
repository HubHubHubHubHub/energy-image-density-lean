import Foundations.Sobolev1D.Representative

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Foundations

/-- Class formulation: C¹ representatives converge in L² together with their derivatives. -/
theorem exists_absolutelyContinuous_representative_Lp {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (U : ℕ → Lp ℝ 2 (densityMeasure ρ)) (u G : Lp ℝ 2 (densityMeasure ρ))
    {f : ℕ → ℝ → ℝ} (hC1 : ∀ n, ContDiff ℝ 1 (f n))
    (hrep : ∀ n, (U n : ℝ → ℝ) =ᵐ[densityMeasure ρ] f n)
    (hdf : ∀ n, MemLp (deriv (f n)) 2 (densityMeasure ρ))
    (hlim : Tendsto U atTop (𝓝 u))
    (hdlim : Tendsto (fun n => (hdf n).toLp (deriv (f n))) atTop (𝓝 G)) :
    ∃ (ũ : ℝ → ℝ) (c : ℝ),
      (∀ x, ũ x = c + ∫ t in (0:ℝ)..x, G t) ∧
      (u : ℝ → ℝ) =ᵐ[densityMeasure ρ] ũ ∧ Continuous ũ ∧
      (∀ a b, AbsolutelyContinuousOnInterval ũ a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt ũ (G x) x) ∧
      deriv ũ =ᵐ[densityMeasure ρ] (G : ℝ → ℝ) := by
  have hf (n) : MemLp (f n) 2 (densityMeasure ρ) := (Lp.memLp (U n)).ae_eq (hrep n)
  have he (n) : (hf n).toLp (f n) = U n := by
    apply Lp.ext
    exact (hf n).coeFn_toLp.trans (hrep n).symm
  have hfconv : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 ((Lp.memLp u).toLp u)) := by
    simpa only [he, Lp.toLp_coeFn] using hlim
  have hdconv : Tendsto (fun n => (hdf n).toLp (deriv (f n))) atTop (𝓝 ((Lp.memLp G).toLp G)) := by
    simpa only [Lp.toLp_coeFn] using hdlim
  obtain ⟨c,hcu,hcont,hac,hder,hderμ⟩ := exists_absolutelyContinuous_representative hρ hpos hC1
    hf (Lp.memLp u) hdf (Lp.memLp G) hfconv hdconv
  exact ⟨primitiveRepresentative c G,c,fun _ => rfl,hcu.symm,hcont,hac,hder,hderμ⟩

/-- Completeness supplies the derivative class when only the Cauchy property is given. -/
theorem exists_absolutelyContinuous_representative_Lp_of_cauchy {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (U : ℕ → Lp ℝ 2 (densityMeasure ρ)) (u : Lp ℝ 2 (densityMeasure ρ))
    {f : ℕ → ℝ → ℝ} (hC1 : ∀ n, ContDiff ℝ 1 (f n))
    (hrep : ∀ n, (U n : ℝ → ℝ) =ᵐ[densityMeasure ρ] f n)
    (hdf : ∀ n, MemLp (deriv (f n)) 2 (densityMeasure ρ))
    (hlim : Tendsto U atTop (𝓝 u))
    (hdCauchy : CauchySeq (fun n => (hdf n).toLp (deriv (f n)))) :
    ∃ (G : Lp ℝ 2 (densityMeasure ρ)) (ũ : ℝ → ℝ),
      (u : ℝ → ℝ) =ᵐ[densityMeasure ρ] ũ ∧ Continuous ũ ∧
      (∀ a b, AbsolutelyContinuousOnInterval ũ a b) ∧
      deriv ũ =ᵐ[densityMeasure ρ] (G : ℝ → ℝ) := by
  obtain ⟨G,hG⟩ := cauchySeq_tendsto_of_complete hdCauchy
  obtain ⟨ũ,c,hformula,hueq,hcont,hac,hder,hderμ⟩ :=
    exists_absolutelyContinuous_representative_Lp hρ hpos U u G hC1 hrep hdf hlim hG
  exact ⟨G,ũ,hueq,hcont,hac,hderμ⟩

/-- The same function class cannot have two different limiting derivative classes. -/
theorem weakDeriv_unique_of_C1_limits {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    {f k : ℕ → ℝ → ℝ} {u g h : ℝ → ℝ}
    (hfC1 : ∀ n, ContDiff ℝ 1 (f n)) (hkC1 : ∀ n, ContDiff ℝ 1 (k n))
    (hf : ∀ n, MemLp (f n) 2 (densityMeasure ρ))
    (hk : ∀ n, MemLp (k n) 2 (densityMeasure ρ)) (hu : MemLp u 2 (densityMeasure ρ))
    (hdf : ∀ n, MemLp (deriv (f n)) 2 (densityMeasure ρ))
    (hdk : ∀ n, MemLp (deriv (k n)) 2 (densityMeasure ρ))
    (hg : MemLp g 2 (densityMeasure ρ)) (hh : MemLp h 2 (densityMeasure ρ))
    (hfconv : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u)))
    (hkconv : Tendsto (fun n => (hk n).toLp (k n)) atTop (𝓝 (hu.toLp u)))
    (hdfconv : Tendsto (fun n => (hdf n).toLp (deriv (f n))) atTop (𝓝 (hg.toLp g)))
    (hdkconv : Tendsto (fun n => (hdk n).toLp (deriv (k n))) atTop (𝓝 (hh.toLp h))) :
    g =ᵐ[densityMeasure ρ] h := by
  obtain ⟨c,hc,-⟩ := exists_absolutelyContinuous_representative hρ hpos hfC1 hf hu hdf hg hfconv hdfconv
  obtain ⟨d,hd,-⟩ := exists_absolutelyContinuous_representative hρ hpos hkC1 hk hu hdk hh hkconv hdkconv
  exact weakDeriv_unique hρ.measurable hpos (locallyIntegrable_of_memLp_density hρ hpos hg)
    (locallyIntegrable_of_memLp_density hρ hpos hh) hc hd

/-- Energy converges to the energy of the derivative of the representative. -/
theorem tendsto_energy_representative {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (densityMeasure ρ)) (hg : MemLp g 2 (densityMeasure ρ))
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) (c : ℝ) :
    Tendsto (fun n => ∫ x, f n x ^ 2 ∂densityMeasure ρ) atTop
      (𝓝 (∫ x, (deriv (primitiveRepresentative c g) x)^2 ∂densityMeasure ρ)) := by
  have hd := (ae_densityMeasure_iff hρ.measurable hpos).mpr
    (deriv_representative_ae_eq (locallyIntegrable_of_memLp_density hρ hpos hg) c)
  have he : (∫ x, (deriv (primitiveRepresentative c g) x)^2 ∂densityMeasure ρ) =
      ∫ x, g x ^ 2 ∂densityMeasure ρ := by
    apply integral_congr_ae
    filter_upwards [hd] with x hx
    rw [hx]
  rw [he]
  exact tendsto_energy hf hg hlim

end Foundations
