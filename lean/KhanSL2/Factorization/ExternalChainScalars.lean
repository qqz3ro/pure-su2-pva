module

public import KhanSL2.Factorization.ExternalTotalHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG SymmetricFamily
variable (R S : Type) [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent R M]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent S N]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass

/-- Both descriptions of the joint action are the same original scalar maps on chains. -/
def externalChainObjectEquiv :
    (externalTotalShortComplex R S M N).X₂ ≃ₗ[R ⊗[ℂ] S]
      ExternalTensor R S (RelativeChains M) (RelativeChains N) where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem externalChainObjectEquiv_apply (z : RelativeChains M ⊗[ℂ] RelativeChains N) :
    externalChainObjectEquiv R S M N z = z := rfl

end KhanSL2.Factorization
