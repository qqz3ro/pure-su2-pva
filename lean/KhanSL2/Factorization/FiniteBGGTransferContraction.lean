module

public import KhanSL2.Factorization.FiniteBGGTransferScalars

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KhanSL2.Factorization.BGGTransfer
open BGG BGGBridge SymmetricFamily

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M] [LieRingModule Current M] [LieModule ℂ Current M]
  [CoefficientLinearCurrent R M]
attribute [local instance] harmonicModule coefficientChainModule

theorem harmonicDifferential_smul (r : R) (z : HarmonicQuotient M) :
    dHq M (r • z) = r • dHq M z := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change Submodule.Quotient.mk (dH M (harmonicScalarRaw R M r z)) =
      Submodule.Quotient.mk (harmonicScalarRaw R M r (dH M z))
    congr 1
    exact base_lTensor (rightAction M) (scalar_ract R M r) PositiveTransfer.differential z

def harmonicDifferentialLinear : Module.End R (HarmonicQuotient M) where
  __ := (dHq M).toAddMonoidHom
  map_smul' := harmonicDifferential_smul R M

/-- The full existing BGG special contraction over the original coefficient
ring, including its homotopy and all three side conditions. -/
def contraction : TauCeti.LinearSpecialContraction
    (coefficientDifferentialLinear R M) (harmonicDifferentialLinear R M) where
  incl := inclLinear R M
  proj := projLinear R M
  homotopy := homotopyLinear R M
  dM_comp_incl := by apply LinearMap.ext; intro z; exact LinearMap.congr_fun (qcN M).dM_comp_incl z
  proj_comp_dM := by apply LinearMap.ext; intro z; exact LinearMap.congr_fun (qcN M).proj_comp_dM z
  proj_comp_incl := by apply LinearMap.ext; intro z; exact LinearMap.congr_fun (qcN M).proj_comp_incl z
  dM_comp_homotopy_add_homotopy_comp_dM := by
    apply LinearMap.ext; intro z
    exact LinearMap.congr_fun (qcN M).dM_comp_homotopy_add_homotopy_comp_dM z
  homotopy_comp_incl := by apply LinearMap.ext; intro z; exact LinearMap.congr_fun (qcN M).homotopy_comp_incl z
  proj_comp_homotopy := by apply LinearMap.ext; intro z; exact LinearMap.congr_fun (qcN M).proj_comp_homotopy z
  homotopy_comp_homotopy := by apply LinearMap.ext; intro z; exact LinearMap.congr_fun (qcN M).homotopy_comp_homotopy z

end KhanSL2.Factorization.BGGTransfer
