module

public import KhanSL2.Factorization.BalancedScalarCoefficients
public import KhanSL2.Factorization.CoefficientChainEquivalence
public import KhanSL2.Factorization.RelativeChainsScalarComplex
public import KhanSL2.Factorization.BalancedShuffleComplex
public import KhanSL2.Factorization.ScalarTensorComplex

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open CategoryTheory HomologicalComplex
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG SymmetricFamily NonnegativeCone

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
variable (K : Type) [CommRing K] [Algebra A K] [Algebra ℂ K] [IsScalarTower ℂ A K]

/-- Base change of the actual balanced coefficient CE source. -/
def balancedScalarSourceIso :
    scalarComplex K (coefficientRelativeComplex A (BalancedCoefficients A M N)) ≅
      coefficientRelativeComplex K
        (BalancedCoefficients K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K)) :=
  relativeChainsScalarComplexIso A (BalancedCoefficients A M N) K ≪≫
    coefficientRelativeComplexIso K (balancedBaseChangeEquiv A M N K)
      (balancedBaseChangeLinearEquiv A M N K).map_smul

/-- Base change of the actual signed tensor CE target. -/
def balancedScalarTargetIso : scalarComplex K (balancedTensorComplex A M N) ≅
    balancedTensorComplex K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K) :=
  scalarTensorComplexIso K (coefficientRelativeComplex A M) (coefficientRelativeComplex A N) ≪≫
    MonoidalCategory.tensorIso (relativeChainsScalarComplexIso A M K)
      (relativeChainsScalarComplexIso A N K)

end KhanSL2.Factorization
