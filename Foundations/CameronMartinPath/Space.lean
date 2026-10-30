import Foundations.HaarBasis.Indicator

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace NNReal
namespace Foundations

/-- The Cameron--Martin path with derivative `g`, starting at zero. -/
def cameronMartinPath (g : HaarL2) : PathSpace where
  toFun t := ⟪haarIndicator t,g⟫_ℝ
  continuous_toFun := by
    simp only [inner_haarIndicator]
    have hc := intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_haarL2 g) (a := 0) left_mem_uIcc
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hc
    exact hc.comp_continuous (NNReal.continuous_coe.comp continuous_subtype_val)
      (fun t => ⟨(t : ℝ≥0).coe_nonneg, by exact_mod_cast t.property.2⟩)

theorem cameronMartinPath_apply (g : HaarL2) (t : WienerTime) :
    cameronMartinPath g t = ∫ x in (0 : ℝ)..(t : ℝ≥0), g x := inner_haarIndicator t g

theorem norm_cameronMartinPath_le (g : HaarL2) : ‖cameronMartinPath g‖ ≤ ‖g‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg g)).mpr
  intro t
  exact (norm_inner_le_norm (haarIndicator t) g).trans
    (by simpa using mul_le_mul_of_nonneg_right (norm_haarIndicator_le_one t) (norm_nonneg g))

def cameronMartinPathCLM : HaarL2 →L[ℝ] PathSpace :=
  LinearMap.mkContinuous
    { toFun := cameronMartinPath
      map_add' := fun g h => by ext t; simp [cameronMartinPath,inner_add_right]
      map_smul' := fun c g => by ext t; simp [cameronMartinPath,inner_smul_right] }
    1 (fun g => by simpa using norm_cameronMartinPath_le g)

@[simp] theorem cameronMartinPathCLM_apply (g : HaarL2) :
    cameronMartinPathCLM g = cameronMartinPath g := rfl

theorem cameronMartinPath_haarFamily (i : SchauderIndex) :
    cameronMartinPath (haarFamily i) = schauderPath i := by
  ext t
  exact haar_coeff_indicator t i

theorem schauderCoordinate_cameronMartinPath (g : HaarL2) (i : SchauderIndex) :
    schauderCoordinate (cameronMartinPath g) i = haarBasis.repr g i := by
  rw [HilbertBasis.repr_apply_apply,haarBasis_apply]
  cases i with
  | none =>
    simpa [schauderCoordinate,schauderCoordinateCLM,cameronMartinPath_apply] using
      (inner_haarFamily_none g).symm
  | some p =>
    obtain ⟨j,k⟩ := p
    have hm := dyadic_midpoint_grid j k
    push_cast at hm
    simp only [schauderCoordinate,schauderCoordinateCLM,smul_apply,sub_apply,
      ContinuousMap.evalCLM_apply,cameronMartinPath_apply,dyadicPoint_coe,smul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
    rw [← hm]
    exact (inner_haarFamily_some g j k).symm

theorem tendsto_schauderIndices : Tendsto schauderIndices atTop atTop := by
  apply tendsto_atTop.mpr
  intro s
  have hi (i : SchauderIndex) : ∀ᶠ N in atTop, i ∈ schauderIndices N := by
    obtain ⟨N,hN⟩ := exists_mem_schauderIndices i
    exact (eventually_ge_atTop N).mono fun n hn => monotone_schauderIndices hn hN
  simpa only [Finset.le_iff_subset, Finset.subset_iff] using
    (s.eventually_all.mpr (fun i _ => hi i))

theorem tendsto_schauderPartial_haarCoefficients (g : HaarL2) :
    Tendsto (fun N => schauderPartial N (haarBasis.repr g)) atTop (𝓝 (cameronMartinPath g)) := by
  have h := ((haarBasis.hasSum_repr g).mapL cameronMartinPathCLM).comp tendsto_schauderIndices
  simpa only [map_smul,haarBasis_apply,cameronMartinPathCLM_apply,
    cameronMartinPath_haarFamily,schauderPartial,Function.comp_def] using h

theorem cameronMartinPath_mem_schauderGoodSet (g : HaarL2) :
    schauderCoordinate (cameronMartinPath g) ∈ schauderGoodSet := by
  have he : schauderCoordinate (cameronMartinPath g) = (haarBasis.repr g : SchauderIndex → ℝ) :=
    funext (schauderCoordinate_cameronMartinPath g)
  rw [he]
  exact (tendsto_schauderPartial_haarCoefficients g).cauchySeq

theorem schauderMap_coordinate_cameronMartinPath (g : HaarL2) :
    schauderMap (schauderCoordinate (cameronMartinPath g)) = cameronMartinPath g := by
  have h := tendsto_schauderPartial (cameronMartinPath_mem_schauderGoodSet g)
  have he : schauderCoordinate (cameronMartinPath g) = (haarBasis.repr g : SchauderIndex → ℝ) :=
    funext (schauderCoordinate_cameronMartinPath g)
  exact tendsto_nhds_unique h (by simpa only [he] using tendsto_schauderPartial_haarCoefficients g)

theorem cameronMartinPath_injective : Function.Injective cameronMartinPath := by
  intro g h hgh
  apply haarBasis.repr.injective
  ext i
  rw [← schauderCoordinate_cameronMartinPath,← schauderCoordinate_cameronMartinPath,hgh]

@[simp] theorem cameronMartinPath_zero_time (g : HaarL2) :
    cameronMartinPath g ⟨0,by simp⟩ = 0 := by
  rw [cameronMartinPath_apply]
  simp

end Foundations
