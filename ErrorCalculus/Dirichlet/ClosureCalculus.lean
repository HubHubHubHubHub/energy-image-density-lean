import ErrorCalculus.Dirichlet.ClosureApproximation
import ErrorCalculus.Dirichlet.DensityCalculus
import ErrorCalculus.Dirichlet.ClosureCalculusLimits

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace ErrorCalculus.ProtoErrorStructure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (S : ProtoErrorStructure Ω μ)

/-- The full C¹ Lipschitz calculus signature on the closed domain. -/
theorem closure_calculus (h : S.energy.IsClosable) :
    ∀ (m : ℕ), 0 < m → ∀ (u : Fin m → S.energy.closureDom) (F : (Fin m → ℝ) → ℝ)
    (L : ℝ≥0), ContDiff ℝ 1 F → LipschitzWith L F →
    ∀ w : Lp ℝ 2 μ, (⇑w =ᵐ[μ] fun ω => F (fun i => (u i : Lp ℝ 2 μ) ω)) →
    ∃ hw : w ∈ S.energy.closureDom, ∀ v : S.energy.closureDom,
      ⇑(S.toErrorData.closureGamma h ⟨w, hw⟩ v) =ᵐ[μ] fun ω => ∑ i,
        fderiv ℝ F (fun j => (u j : Lp ℝ 2 μ) ω) (Pi.single i 1) *
          S.toErrorData.closureGamma h (u i) v ω := by
  intro m hm u F L hF hL w hw
  choose un hun using fun i => (S.energy.mem_closureDom_iff (u i)).mp (u i).property
  obtain ⟨φ, hφ, hφa⟩ := exists_common_ae_subsequence
    (fun i n => (un i n : Lp ℝ 2 μ)) (fun i => (u i : Lp ℝ 2 μ)) (fun i => (hun i).2)
  let x (i : Fin m) (n : ℕ) : S.dom := un i (φ n)
  have hx i : S.energy.Approaches (x i) (u i) := by
    have h0 := (hun i).2.comp hφ.tendsto_atTop
    have h1 := (S.energy.approaches_tendsto_lift h (hun i) (u i).property).comp hφ.tendsto_atTop
    exact ⟨⟨h0.cauchySeq, h1.cauchySeq⟩, h0⟩
  let a (i : Fin m) (n : ℕ) (ω : Ω) := fderiv ℝ F (fun j => (x j n : Lp ℝ 2 μ) ω) (Pi.single i 1)
  let c (i : Fin m) (ω : Ω) := fderiv ℝ F (fun j => (u j : Lp ℝ 2 μ) ω) (Pi.single i 1)
  have ha i n : MemLp (a i n) ∞ μ := fderiv_coefficient_memLp _ hF hL i
  have hc i : MemLp (c i) ∞ μ := fderiv_coefficient_memLp _ hF hL i
  have hCa i n : ∀ᵐ ω ∂μ, |a i n ω| ≤ L := ae_of_all _ fun ω => fderiv_coefficient_bound hL _ i
  have hCc i : ∀ᵐ ω ∂μ, |c i ω| ≤ L := ae_of_all _ fun ω => fderiv_coefficient_bound hL _ i
  have hat i : ∀ᵐ ω ∂μ, Tendsto (fun n => a i n ω) atTop (𝓝 (c i ω)) := by
    have hcont : Continuous (fun y => fderiv ℝ F y (Pi.single i 1)) :=
      (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
    filter_upwards [hφa] with ω hω
    exact (hcont.tendsto _).comp (tendsto_pi_nhds.mpr hω)
  choose wn hwn using fun n => ErrorStructure.exists_composition
    (fun i => (x i n : Lp ℝ 2 μ)) hL
  choose hn hchain using fun n => S.calc m hm (fun i => x i n) F L hF hL (wn n) (hwn n)
  let z (n : ℕ) : S.dom := ⟨wn n, hn n⟩
  have hz0 : Tendsto (fun n => (z n : Lp ℝ 2 μ)) atTop (𝓝 w) :=
    composition_tendsto (fun i n => (x i n : Lp ℝ 2 μ)) (fun i => (u i : Lp ℝ 2 μ))
      hL wn w hwn hw (fun i => (hx i).2)
  have hzC : S.energy.IsCauchy z := S.toErrorData.chain_isCauchy x z a c ha hc L.coe_nonneg
    hCa hCc hat (fun i => (hx i).1) hz0.cauchySeq hchain
  have hz : S.energy.Approaches z w := ⟨hzC, hz0⟩
  have hwm : w ∈ S.energy.closureDom := (S.energy.mem_closureDom_iff w).mpr ⟨z, hz⟩
  refine ⟨hwm, fun v => ?_⟩
  obtain ⟨yn, hyn⟩ := (S.energy.mem_closureDom_iff v).mp v.property
  let rhs : Lp ℝ 1 μ := ∑ i, boundedMul (c i) (hc i) (S.toErrorData.closureGamma h (u i) v)
  have hright : Tendsto (fun n => ∑ i, boundedMul (a i n) (ha i n) (S.Γ (x i n) (yn n)))
      atTop (𝓝 rhs) := by
    apply tendsto_finsetSum
    intro i _
    exact boundedMul_tendsto_one (a i) (c i) (ha i) (hc i) _ _ (hCa i) (hCc i) (hat i)
      (S.toErrorData.closureGamma_characterization h (hx i) hyn)
  have he n : S.Γ (z n) (yn n) = ∑ i, boundedMul (a i n) (ha i n) (S.Γ (x i n) (yn n)) := by
    apply Lp.ext
    filter_upwards [hchain n (yn n), lp_coeFn_sum Finset.univ
      (fun i => boundedMul (a i n) (ha i n) (S.Γ (x i n) (yn n))),
      ae_all_iff.mpr (fun i => coeFn_boundedMul (a i n) (ha i n) (S.Γ (x i n) (yn n)))] with ω hf hs hp
    exact hf.trans (by rw [hs]; simp only [hp]; rfl)
  have hleft := S.toErrorData.closureGamma_characterization h (a := ⟨w,hwm⟩) hz hyn
  have hlim : S.toErrorData.closureGamma h ⟨w,hwm⟩ v = rhs :=
    tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall (fun n => (he n).symm)))
  rw [hlim]
  filter_upwards [lp_coeFn_sum Finset.univ
    (fun i => boundedMul (c i) (hc i) (S.toErrorData.closureGamma h (u i) v)),
    ae_all_iff.mpr (fun i => coeFn_boundedMul (c i) (hc i) (S.toErrorData.closureGamma h (u i) v))] with ω hs hp
  change (∑ i, boundedMul (c i) (hc i) (S.toErrorData.closureGamma h (u i) v)) ω = _
  rw [hs]
  simp only [hp]
  rfl

end ErrorCalculus.ProtoErrorStructure
