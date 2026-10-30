import Foundations.Sobolev1D.Primitive

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Foundations

/-- A subsequence identifies the additive constant and the continuous representative. -/
theorem exists_const_subseq_of_C1_limits {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    {f : ℕ → ℝ → ℝ} {u g : ℝ → ℝ} (hC1 : ∀ n, ContDiff ℝ 1 (f n))
    (hf : ∀ n, MemLp (f n) 2 (densityMeasure ρ)) (hu : MemLp u 2 (densityMeasure ρ))
    (hdf : ∀ n, MemLp (deriv (f n)) 2 (densityMeasure ρ)) (hg : MemLp g 2 (densityMeasure ρ))
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u)))
    (hdlim : Tendsto (fun n => (hdf n).toLp (deriv (f n))) atTop (𝓝 (hg.toLp g))) :
    ∃ (c : ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n => f (φ n) 0) atTop (𝓝 c) ∧
      (∀ x, Tendsto (fun n => f (φ n) x) atTop (𝓝 (primitiveRepresentative c g x))) ∧
      primitiveRepresentative c g =ᵐ[densityMeasure ρ] u := by
  have he := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mp hlim
  obtain ⟨φ,hφ,hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (fun n => (hf n).1) hu.1 he).exists_seq_tendsto_ae
  have haev := (ae_densityMeasure_iff hρ.measurable hpos).mp hae
  obtain ⟨x₀,hx₀⟩ := haev.exists
  let c := u x₀ - primitive g x₀
  have hc : Tendsto (fun n => f (φ n) 0) atTop (𝓝 c) := by
    have h := hx₀.sub ((tendsto_primitive hρ hpos hdf hg hdlim x₀).comp hφ.tendsto_atTop)
    convert h using 1
    ext n
    simp only [Function.comp_apply]
    rw [primitive_deriv_eq_sub (hC1 (φ n))]
    ring
  have hall (x : ℝ) : Tendsto (fun n => f (φ n) x) atTop (𝓝 (primitiveRepresentative c g x)) := by
    change Tendsto (fun n => f (φ n) x) atTop (𝓝 (c + primitive g x))
    have h := hc.add ((tendsto_primitive hρ hpos hdf hg hdlim x).comp hφ.tendsto_atTop)
    convert h using 1
    ext n
    simp only [Function.comp_apply]
    rw [primitive_deriv_eq_sub (hC1 (φ n))]
    ring
  refine ⟨c,φ,hφ,hc,hall,?_⟩
  filter_upwards [hae] with x hx
  exact tendsto_nhds_unique (hall x) hx

/-- The weighted H¹ limit has a locally absolutely continuous representative. -/
theorem exists_absolutelyContinuous_representative {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) {f : ℕ → ℝ → ℝ} {u g : ℝ → ℝ}
    (hC1 : ∀ n, ContDiff ℝ 1 (f n))
    (hf : ∀ n, MemLp (f n) 2 (densityMeasure ρ)) (hu : MemLp u 2 (densityMeasure ρ))
    (hdf : ∀ n, MemLp (deriv (f n)) 2 (densityMeasure ρ)) (hg : MemLp g 2 (densityMeasure ρ))
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u)))
    (hdlim : Tendsto (fun n => (hdf n).toLp (deriv (f n))) atTop (𝓝 (hg.toLp g))) :
    ∃ c : ℝ, primitiveRepresentative c g =ᵐ[densityMeasure ρ] u ∧
      Continuous (primitiveRepresentative c g) ∧
      (∀ a b, AbsolutelyContinuousOnInterval (primitiveRepresentative c g) a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt (primitiveRepresentative c g) (g x) x) ∧
      deriv (primitiveRepresentative c g) =ᵐ[densityMeasure ρ] g := by
  obtain ⟨c,φ,hφ,hc,hall,he⟩ := exists_const_subseq_of_C1_limits hρ hpos hC1 hf hu hdf hg hlim hdlim
  have hl := locallyIntegrable_of_memLp_density hρ hpos hg
  exact ⟨c,he,continuous_representative hl c,absolutelyContinuousOnInterval_representative hl c,
    ae_hasDerivAt_representative hl c,
    (ae_densityMeasure_iff hρ.measurable hpos).mpr (deriv_representative_ae_eq hl c)⟩

/-- Two primitive representatives of the same weighted class have identical weak derivatives. -/
theorem weakDeriv_unique {ρ u g h : ℝ → ℝ} (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x)
    (hg : LocallyIntegrable g volume) (hh : LocallyIntegrable h volume) {c d : ℝ}
    (hc : primitiveRepresentative c g =ᵐ[densityMeasure ρ] u)
    (hd : primitiveRepresentative d h =ᵐ[densityMeasure ρ] u) :
    g =ᵐ[densityMeasure ρ] h := by
  have he : primitiveRepresentative c g = primitiveRepresentative d h :=
    MeasureTheory.Measure.eq_of_ae_eq ((ae_densityMeasure_iff hρ hpos).mp (hc.trans hd.symm))
      (continuous_representative hg c) (continuous_representative hh d)
  apply (ae_densityMeasure_iff hρ hpos).mpr
  filter_upwards [ae_hasDerivAt_representative hg c, ae_hasDerivAt_representative hh d] with x hx hy
  rw [he] at hx
  exact hx.unique hy

/-- Energy is continuous for L² convergence. -/
theorem tendsto_energy {μ : Measure ℝ} {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 (∫ x, g x ^ 2 ∂μ)) := by
  simpa only [norm_toLp_sq] using hlim.norm.pow 2

end Foundations
