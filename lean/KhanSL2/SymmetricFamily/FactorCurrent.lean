module

public import KhanSL2.SymmetricFamily.FactorInsertion
public import KhanSL2.SymmetricFamily.FactorExterior
public import KhanSL2.Factorization.BalancedCoefficients

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The current actions on the actual factor specializations and their
canonical coefficient insertion maps, with balancing over the original base. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Macdonald Factorization

variable {A : Type} [CommRing A] [Algebra ℂ A]

instance factorSymmetricCoefficientLinear (n : ℕ) (f : Polynomial A) :
    CoefficientLinearCurrent A (FactorSymmetric n f) := by
  unfold FactorSymmetric
  let := factorCoefficientAlgebra n f
  let : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  infer_instance

instance factorExteriorCoefficientLinear (n : ℕ) (f : Polynomial A) :
    CoefficientLinearCurrent A (FactorExterior n f) := by
  unfold FactorExterior
  let := factorCoefficientAlgebra n f
  let : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  infer_instance

/-- The original coefficient insertion preserves the actual current action. -/
def factorSymmetricUnitLieHom (n : ℕ) (f : Polynomial A) :
    symmetricPower n →ₗ⁅ℂ,BGG.Current⁆ FactorSymmetric n f where
  toLinearMap := factorSymmetricUnit n f
  map_lie' := rfl

/-- Canonical pairing of current-module maps, balanced over the original common algebra. -/
def tensorOverLieHom {M N P Q : Type} [AddCommGroup M] [Module ℂ M]
    [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
    [AddCommGroup N] [Module ℂ N] [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]
    [AddCommGroup P] [Module ℂ P] [Module A P] [IsScalarTower ℂ A P]
    [LieRingModule BGG.Current P] [LieModule ℂ BGG.Current P] [CoefficientLinearCurrent A P]
    [AddCommGroup Q] [Module ℂ Q] [Module A Q] [IsScalarTower ℂ A Q]
    [LieRingModule BGG.Current Q] [LieModule ℂ BGG.Current Q] [CoefficientLinearCurrent A Q]
    (f : M →ₗ⁅ℂ,BGG.Current⁆ P) (g : N →ₗ⁅ℂ,BGG.Current⁆ Q) :
    M ⊗[ℂ] N →ₗ⁅ℂ,BGG.Current⁆ BalancedCoefficients A P Q :=
  (balancedCoefficientLieHom A P Q).comp (TensorProduct.LieModule.map f g)

@[simp] theorem tensorOverLieHom_apply {M N P Q : Type} [AddCommGroup M] [Module ℂ M]
    [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
    [AddCommGroup N] [Module ℂ N] [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]
    [AddCommGroup P] [Module ℂ P] [Module A P] [IsScalarTower ℂ A P]
    [LieRingModule BGG.Current P] [LieModule ℂ BGG.Current P] [CoefficientLinearCurrent A P]
    [AddCommGroup Q] [Module ℂ Q] [Module A Q] [IsScalarTower ℂ A Q]
    [LieRingModule BGG.Current Q] [LieModule ℂ BGG.Current Q] [CoefficientLinearCurrent A Q]
    (f : M →ₗ⁅ℂ,BGG.Current⁆ P) (g : N →ₗ⁅ℂ,BGG.Current⁆ Q) (z : M ⊗[ℂ] N) :
    tensorOverLieHom (A:=A) f g z =
      (show BalancedCoefficients A P Q from tensorOverMap (A:=A) f.toLinearMap g.toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul m n => rfl

/-- Over the ground field, the balanced action is literally the ordinary diagonal tensor action. -/
def balancedComplexEquiv (M N : Type) [AddCommGroup M] [Module ℂ M]
    [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M] [CoefficientLinearCurrent ℂ M]
    [AddCommGroup N] [Module ℂ N] [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]
    [CoefficientLinearCurrent ℂ N] :
    BalancedCoefficients ℂ M N ≃ₗ⁅ℂ,BGG.Current⁆ M ⊗[ℂ] N where
  __ := (LinearEquiv.refl ℂ (M ⊗[ℂ] N))
  map_lie' {x z} := by
    change (show M ⊗[ℂ] N from ⁅x,z⁆) = ⁅x,(show M ⊗[ℂ] N from z)⁆
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [lie_add,hz,hw]
    | tmul m n =>
      exact (TensorProduct.LieModule.lie_tmul_right x m n).symm
end KhanSL2.SymmetricFamily
