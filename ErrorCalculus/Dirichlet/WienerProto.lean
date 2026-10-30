import ErrorCalculus.Dirichlet.WienerDense

noncomputable section
open MeasureTheory Filter
namespace ErrorCalculus

/-- The cylindrical Ornstein–Uhlenbeck proto-structure on Gaussian coordinates. -/
def wienerProto : ProtoErrorStructure (ℕ → ℝ) wienerCoord where
  toErrorData := wienerData
  dense := wienerDom_dense
  «calc» := wienerProto_calculus
  one_mem := const_mem_wienerDom 1

/-- The Wiener pre-energy restricts to the OU pre-energy at every finite level. -/
theorem wienerProto_energy_cyl (N : ℕ) (u v : protoDomD (ouDensityD N)) :
    wienerProto.toErrorData.energy.E (cylProto N u) (cylProto N v) =
      (protoFormD (ouDensityD N)).E u v :=
  wienerData_energy_cyl N u v

/-- Equality of the mixed carré du champ as L¹ classes. -/
theorem wienerProto_gamma_cyl (N : ℕ) (u v : protoDomD (ouDensityD N)) :
    wienerProto.Γ (cylProto N u) (cylProto N v) = cylLp N 1 (gammaD _ u v) :=
  wienerGamma_cyl N u v

/-- The familiar sum of products of partial derivatives for ordinary cylinders. -/
theorem wienerProto_gamma_ofFunction {N : ℕ} {f g : (Fin N → ℝ) → ℝ}
    (hf : IsC1BoundedD f) (hg : IsC1BoundedD g) :
    ⇑(wienerProto.Γ (cylProto N (protoOfFunctionD _ f hf))
      (cylProto N (protoOfFunctionD _ g hg))) =ᵐ[wienerCoord]
      pointGammaD f g ∘ restrictN N := by
  rw [wienerProto_gamma_cyl]
  exact (coeFn_cylLp N 1 _).trans
    ((restrictN_preserving N).quasiMeasurePreserving.ae_eq_comp (gammaD_ofFunction _ hf hg))

end ErrorCalculus
