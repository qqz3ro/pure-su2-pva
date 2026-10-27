module

public import KhanSL2.Factorization.CoefficientFlatHomology
public import KhanSL2.Factorization.LinearModuleHomology
public import KhanSL2.Factorization.BalancedTensorDifferential

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG SymmetricFamily
variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientTotalHomologyModule
  coefficientTotalHomologyIsScalarTower coefficientTotalHomologySMulCommClass

/-- The unchanged signed balanced tensor boundary viewed as a square-zero pair. -/
def balancedTensorShortComplex : ShortComplex (ModuleCat A) :=
  ShortComplex.moduleCatMk (balancedTensorDifferential A M N) (balancedTensorDifferential A M N)
    (balancedTensorDifferential_square A M N)

/-- The actual coefficient-linear tensor cycles modulo its actual boundaries. -/
abbrev BalancedTensorTotalHomology := (balancedTensorShortComplex A M N).moduleCatLeftHomologyData.H

variable (L : Type) [AddCommGroup L] [Module ℂ L] [Module A L] [IsScalarTower ℂ A L]
  [LieRingModule Current L] [LieModule ℂ Current L] [CoefficientLinearCurrent A L]
variable (F : RelativeChains L →ₗ[A] RelativeChains M ⊗[A] RelativeChains N)
variable (hF : ∀ z, F (differential L z) = balancedTensorDifferential A M N (F z))

/-- The actual total comparison, using the same chain map in all three positions. -/
def balancedTotalComparisonShortMap :
    coefficientTotalShortComplex A L ⟶ balancedTensorShortComplex A M N where
  τ₁ := ModuleCat.ofHom F
  τ₂ := ModuleCat.ofHom F
  τ₃ := ModuleCat.ofHom F
  comm₁₂ := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro z; exact (hF z).symm
  comm₂₃ := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro z; exact (hF z).symm

/-- The induced original map on actual total homology, without a choice of splitting. -/
def balancedTotalComparisonMap : TotalHomology L →ₗ[A] BalancedTensorTotalHomology A M N :=
  (linearModuleQuotientHomologyMap (balancedTotalComparisonShortMap A M N L F hF)).comp
    (coefficientTotalQuotientEquiv A L).symm.toLinearMap

/-- This induced map is the class of exactly the specified image cycle. -/
theorem balancedTotalComparisonMap_mk (z : LinearMap.ker (differential L)) :
    balancedTotalComparisonMap A M N L F hF (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (⟨F z.val,by
        change balancedTensorDifferential A M N (F z.val) = 0
        rw [← hF,z.property,map_zero]⟩ : LinearMap.ker (balancedTensorDifferential A M N)) := by
  change linearModuleQuotientHomologyMap (balancedTotalComparisonShortMap A M N L F hF)
    ((coefficientTotalQuotientEquiv A L).symm (Submodule.Quotient.mk z)) = _
  rw [coefficientTotalQuotientEquiv_symm_mk,linearModuleQuotientHomologyMap_mk]
  congr 1

end KhanSL2.Factorization
