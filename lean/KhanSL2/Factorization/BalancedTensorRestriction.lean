module

public import KhanSL2.Factorization.BalancedTensorModel
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass

/-- The balanced chain tensor with its original complex scalar action fixed. -/
def BalancedTensorNative : Type := RelativeChains M⊗[A]RelativeChains N
instance : AddCommGroup (BalancedTensorNative A M N) :=
  inferInstanceAs (AddCommGroup (RelativeChains M⊗[A]RelativeChains N))
instance : Module ℂ (BalancedTensorNative A M N) :=
  inferInstanceAs (Module ℂ (RelativeChains M⊗[A]RelativeChains N))

def relativeTensorBalanceNative : RelativeChains M⊗[ℂ]RelativeChains N →ₗ[ℂ] BalancedTensorNative A M N :=
  relativeTensorBalance A M N

/-- Forgetting tensor degree after restricting coefficient scalars to ℂ.  The
native ℂ action in the target is retained even when the coefficient ring is ℂ. -/
def balancedTensorDegreeForgetRestricted (j:ℕ) :
    (ModuleCat.restrictScalars (algebraMap ℂ A)).obj ((balancedTensorComplex A M N).X j) →ₗ[ℂ]
      BalancedTensorNative A M N where
  toFun := balancedTensorDegreeForget A M N j
  map_add' := (balancedTensorDegreeForget A M N j).map_add
  map_smul' c z := by
    change balancedTensorDegreeForget A M N j (algebraMap ℂ A c • z) = _
    rw [map_smul,algebraMap_smul]
    rfl

end KhanSL2.Factorization


