module

public import KhanSL2.SymmetricFamily.SymmetricChainProjective
public import KhanSL2.SymmetricFamily.FactorCurrent
public import KhanSL2.Factorization.BalancedTensorModel
public import KhanSL2.Factorization.QuasiIsoBaseChange

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-! Projectivity of actual symmetric relative chain groups survives arbitrary
coefficient specialization. In particular, the nonnegative cone over a coprime
chart has flat terms before it is specialized to a point. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open BGG Macdonald Conditional Factorization
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientDegreeModule coefficientDegreeIsScalarTower
  coefficientDegreeSMulCommClass

variable (k : ℕ) (A : Type) [CommRing A] [Algebra (CoefficientRing k) A]
  [Algebra ℂ A] [IsScalarTower ℂ (CoefficientRing k) A]

theorem symmetricBaseChangedChains_projective :
    Module.Projective A (RelativeChains (CoefficientBaseChange (CoefficientRing k) (symmetricPower k) A)) := by
  let := symmetricRelativeChains_projective k
  exact Module.Projective.of_equiv'
    (relativeChainsScalarEquiv (CoefficientRing k) (symmetricPower k) A)

theorem symmetricBaseChangedDegree_projective (j : ℕ) :
    Module.Projective A (degree (CoefficientBaseChange (CoefficientRing k) (symmetricPower k) A) j) := by
  let := symmetricRelativeDegree_projective k j
  exact Module.Projective.of_equiv'
    (relativeChainsScalarDegreeEquiv (CoefficientRing k) (symmetricPower k) A j)

theorem symmetricBaseChangedComplex_flat (j : ℕ) :
    Module.Flat A ((coefficientRelativeComplex A
      (CoefficientBaseChange (CoefficientRing k) (symmetricPower k) A)).X j) := by
  let := symmetricBaseChangedDegree_projective k A j
  exact inferInstanceAs (Module.Flat A (degree (CoefficientBaseChange
    (CoefficientRing k) (symmetricPower k) A) j))

end KhanSL2.SymmetricFamily
namespace KhanSL2.Factorization
open BGG SymmetricFamily
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientDegreeModule coefficientDegreeIsScalarTower
  coefficientDegreeSMulCommClass

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]

/-- Actual tensor-complex degrees are split summands of the tensor of total chain spaces. -/
theorem balancedTensorComplex_projective
    [Module.Projective A (RelativeChains M)] [Module.Projective A (RelativeChains N)] (j : ℕ) :
    Module.Projective A ((balancedTensorComplex A M N).X j) := by
  exact Module.Projective.of_split (balancedTensorDegreeForget A M N j)
    (balancedTensorDegreeComponent A M N j)
    (LinearMap.ext (balancedTensorDegreeComponent_forget A M N j))

end KhanSL2.Factorization
namespace KhanSL2.SymmetricFamily
open BGG Macdonald Conditional Factorization
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientDegreeModule coefficientDegreeIsScalarTower
  coefficientDegreeSMulCommClass

variable {A : Type} [CommRing A] [Algebra ℂ A]

theorem factorSymmetricChains_projective (n : ℕ) (f : Polynomial A) :
    Module.Projective A (RelativeChains (FactorSymmetric n f)) := by
  let := factorCoefficientAlgebra n f
  let : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  exact symmetricBaseChangedChains_projective n A

theorem factorSymmetricComplex_flat (n j : ℕ) (f : Polynomial A) :
    Module.Flat A ((coefficientRelativeComplex A (FactorSymmetric n f)).X j) := by
  let := factorCoefficientAlgebra n f
  let : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  exact symmetricBaseChangedComplex_flat n A j

theorem factorSymmetricTensorComplex_flat (r s j : ℕ) (f g : Polynomial A) :
    Module.Flat A ((balancedTensorComplex A (FactorSymmetric r f) (FactorSymmetric s g)).X j) := by
  let := factorSymmetricChains_projective r f
  let := factorSymmetricChains_projective s g
  let := balancedTensorComplex_projective A (FactorSymmetric r f) (FactorSymmetric s g) j
  infer_instance

end KhanSL2.SymmetricFamily
