module

public import KhanSL2.Factorization.BalancedTensorDifferential
public import KhanSL2.Factorization.BalancedTensorHomogeneous

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped TensorProduct
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization
open BGG BGGBridge SymmetricFamily

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass
  coefficientDegreeModule coefficientDegreeIsScalarTower coefficientDegreeSMulCommClass

/-- Actual homogeneous component of the coefficient-algebra-balanced shuffle. -/
def balancedDegreeShuffle (j : ℕ) :
    degree (BalancedCoefficients A M N) j →ₗ[A] (balancedTensorComplex A M N).X j :=
  (balancedTensorDegreeComponent A M N j).comp
    ((balancedRelativeShuffleLinear A M N).comp
      (coefficientDegreeInclusionLinear A (BalancedCoefficients A M N) j))

@[simp] theorem balancedTensorDegreeForget_degreeShuffle (j : ℕ)
    (z : degree (BalancedCoefficients A M N) j) :
    balancedTensorDegreeForget A M N j (balancedDegreeShuffle A M N j z) =
      balancedRelativeShuffle A M N z.val :=
  balancedTensorDegreeForget_component_shuffle A M N j z

/-- The original relative shuffle, balanced over A, as an actual morphism of
coefficient-linear chain complexes with the canonical signed tensor target. -/
def balancedShuffleComplex : coefficientRelativeComplex A (BalancedCoefficients A M N) ⟶
    balancedTensorComplex A M N :=
  ChainComplex.ofHom (fun j => ModuleCat.ofHom (balancedDegreeShuffle A M N j)) (fun j => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change degree (BalancedCoefficients A M N) (j+1) at z
    apply balancedTensorDegreeForget_injective A M N j
    have hd := congrArg (fun f => f.hom (balancedDegreeShuffle A M N (j+1) z))
      (balancedTensorDegreeForget_differential A M N j)
    change balancedTensorDegreeForget A M N j
      ((balancedTensorComplex A M N).d (j+1) j (balancedDegreeShuffle A M N (j+1) z)) =
        balancedTensorDifferential A M N
          (balancedTensorDegreeForget A M N (j+1) (balancedDegreeShuffle A M N (j+1) z)) at hd
    change balancedTensorDegreeForget A M N j
      ((balancedTensorComplex A M N).d (j+1) j (balancedDegreeShuffle A M N (j+1) z)) =
        balancedTensorDegreeForget A M N j (balancedDegreeShuffle A M N j
          ((coefficientRelativeComplex A (BalancedCoefficients A M N)).d (j+1) j z))
    rw [hd,balancedTensorDegreeForget_degreeShuffle,balancedTensorDegreeForget_degreeShuffle,
      coefficientRelativeComplex_d]
    exact (balancedRelativeShuffle_differential A M N z.val).symm)

end KhanSL2.Factorization
