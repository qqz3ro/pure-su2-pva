module

public import KhanSL2.SymmetricFamily.FactorRootScalars
public import KhanSL2.SymmetricFamily.BaseChangedAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The original symmetric coefficient family specialized along one prescribed
factor polynomial, and its normalized actual root/color invariant realization. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Macdonald
open scoped FactorRootScalars

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The actual symmetric coefficient specialization along the factor coefficients. -/
def FactorSymmetric (n : ℕ) (f : Polynomial A) : Type :=
  letI := factorCoefficientAlgebra n f
  CoefficientBaseChange (Depth.RB n) (symmetricPower n) A

instance (n : ℕ) (f : Polynomial A) : AddCommGroup (FactorSymmetric n f) := by
  unfold FactorSymmetric
  infer_instance
instance (n : ℕ) (f : Polynomial A) : Module A (FactorSymmetric n f) := by
  unfold FactorSymmetric
  infer_instance
instance (n : ℕ) (f : Polynomial A) : Module ℂ (FactorSymmetric n f) := by
  unfold FactorSymmetric
  letI := factorCoefficientAlgebra n f
  letI : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  infer_instance
instance (n : ℕ) (f : Polynomial A) : IsScalarTower ℂ A (FactorSymmetric n f) := by
  unfold FactorSymmetric
  let := factorCoefficientAlgebra n f
  let : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  infer_instance
instance (n : ℕ) (f : Polynomial A) : LieRingModule BGG.Current (FactorSymmetric n f) := by
  unfold FactorSymmetric
  infer_instance
instance (n : ℕ) (f : Polynomial A) : LieModule ℂ BGG.Current (FactorSymmetric n f) := by
  unfold FactorSymmetric
  let := factorCoefficientAlgebra n f
  let : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  infer_instance

abbrev FactorColors (n : ℕ) (f : Polynomial A) := FactorRoots n f ⊗[ℂ] Color n

/-- The original inverse-slot permutation action on a factor's root/color coordinates. -/
def factorLabelledPermute (n : ℕ) (f : Polynomial A) (σ : Equiv.Perm (Fin n)) :
    Module.End A (FactorColors n f) :=
  TensorProduct.AlgebraTensorModule.map
    (factorRootPermutation n f σ.symm).toLinearMap (colorPermute σ)

/-- The actual normalized section realizes the original factor family as root/color invariants. -/
def factorSymmetricRootEquiv (n : ℕ) (f : Polynomial A) :
    FactorSymmetric n f ≃ₗ[A] fixedOperators (factorLabelledPermute n f) := by
  letI := factorCoefficientAlgebra n f
  letI : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  exact symmetricBaseChangedLabelledEquiv n A

end KhanSL2.SymmetricFamily
