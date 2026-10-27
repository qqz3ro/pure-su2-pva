module

public import KhanSL2.Factorization.CoefficientDegreeHomology
public import KhanSL2.Factorization.FiniteBGGTransferEquivalence
public import KhanSL2.Factorization.FiniteBGGHomology

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace KhanSL2.Factorization.BGGTransfer
open BGG Conditional SymmetricFamily
attribute [local instance] coefficientHomogeneousHomologyModule
  coefficientHomogeneousHomologyIsScalarTower coefficientHomogeneousHomologySMulCommClass

/-- The unchanged homogeneous relative CE homology of the exterior coefficient
family is the original K-module, with the original coefficient-ring action. -/
def exteriorHomologyEquivK (B p : ℕ) :
    Homology (⋀[ℂ]^B Current) p ≃ₗ[Depth.RB B] K B p :=
  (coefficientComplexHomologyEquiv (Depth.RB B) (⋀[ℂ]^B Current) p).symm.trans
    (((exteriorHomotopyEquiv B).toHomologyIso p).toLinearEquiv.trans
      (FiniteBGG.homologyEquivK B p))

end KhanSL2.Factorization.BGGTransfer
