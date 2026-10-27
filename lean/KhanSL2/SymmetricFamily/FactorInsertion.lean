module

public import KhanSL2.SymmetricFamily.SymmetricChartInclusion

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! Canonical insertion of the original coefficient tensors into their actual
factor specializations, with no transported replacement maps. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Macdonald
open scoped FactorRootScalars

/-- Pair two complex-linear maps in the tensor product over the original common algebra. -/
def tensorOverMap {A M N P Q : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
    [AddCommMonoid P] [Module A P] [Module ℂ P] [IsScalarTower ℂ A P]
    [AddCommMonoid Q] [Module A Q] [Module ℂ Q] [IsScalarTower ℂ A Q]
    (f : M →ₗ[ℂ] P) (g : N →ₗ[ℂ] Q) : M ⊗[ℂ] N →ₗ[ℂ] P ⊗[A] Q :=
  TensorProduct.lift (((TensorProduct.mk A P Q).restrictScalars₁₂ ℂ ℂ).compl₁₂ f g)

@[simp] theorem tensorOverMap_tmul {A M N P Q : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
    [AddCommMonoid P] [Module A P] [Module ℂ P] [IsScalarTower ℂ A P]
    [AddCommMonoid Q] [Module A Q] [Module ℂ Q] [IsScalarTower ℂ A Q]
    (f : M →ₗ[ℂ] P) (g : N →ₗ[ℂ] Q) (x : M) (y : N) :
    tensorOverMap (A:=A) f g (x ⊗ₜ[ℂ] y) = f x ⊗ₜ[A] g y := rfl

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- Insert an original symmetric coefficient into its specified factor specialization. -/
def factorSymmetricUnit (n : ℕ) (f : Polynomial A) : symmetricPower n →ₗ[ℂ] FactorSymmetric n f := by
  letI := factorCoefficientAlgebra n f
  letI : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  exact ((coefficientBaseChangeEquiv (Depth.RB n) (symmetricPower n) A).symm.toLinearMap.restrictScalars ℂ).comp
    ((TensorProduct.mk (Depth.RB n) A (symmetricPower n) 1).restrictScalars ℂ)

/-- Insert an original labelled current tensor into the factor's actual root/color coordinates. -/
def factorTensorUnit (n : ℕ) (f : Polynomial A) :
    (⨂[ℂ]^n BGG.Current) →ₗ[ℂ] FactorColors n f := by
  letI := factorCoefficientAlgebra n f
  letI : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  exact ((baseRootTensorEquiv n A).toLinearMap.restrictScalars ℂ).comp
    ((TensorProduct.mk (Depth.RB n) A (⨂[ℂ]^n BGG.Current) 1).restrictScalars ℂ)

/-- The actual invariant realization of a specialized coefficient retains its original section. -/
theorem factorSymmetricFixedEquiv_unit (n : ℕ) (f : Polynomial A) (p : symmetricPower n) :
    (factorSymmetricFixedEquiv n f (factorSymmetricUnit n f p)).val =
      factorTensorUnit n f (symmetricToTensor n p) := rfl

end KhanSL2.SymmetricFamily
