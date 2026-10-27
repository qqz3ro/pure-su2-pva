module

public import KhanSL2.Factorization.WeightedRootModelBlockFormulas

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped TensorProduct
namespace KhanSL2.Macdonald
open Factorization.WeightedRootModel
variable {A : Type} [CommRing A] [Algebra ℂ A]

namespace WeightedFactorScalars

scoped instance factorRootsComplexAlgebra (q r : ℕ) (f : Polynomial A) :
    Algebra ℂ (FactorRoots q r f) := by
  unfold FactorRoots
  letI : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  letI : IsScalarTower ℂ (Depth.RB (q+2*r)) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom (q+2*r) f).commutes z).symm
  infer_instance

scoped instance factorRootsComplexTower (q r : ℕ) (f : Polynomial A) :
    IsScalarTower ℂ A (FactorRoots q r f) := by
  unfold FactorRoots
  let : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  let : IsScalarTower ℂ (Depth.RB (q+2*r)) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom (q+2*r) f).commutes z).symm
  infer_instance

scoped instance factorSignedComplexModule (q r : ℕ) (f : Polynomial A) :
    Module ℂ (FactorSignedModule q r f) := by
  unfold FactorSignedModule
  letI : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  letI : IsScalarTower ℂ (Depth.RB (q+2*r)) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom (q+2*r) f).commutes z).symm
  infer_instance

scoped instance factorSignedComplexTower (q r : ℕ) (f : Polynomial A) :
    IsScalarTower ℂ A (FactorSignedModule q r f) := by
  unfold FactorSignedModule
  let : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  let : IsScalarTower ℂ (Depth.RB (q+2*r)) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom (q+2*r) f).commutes z).symm
  infer_instance

end WeightedFactorScalars
open scoped WeightedFactorScalars

/-- Canonical insertion of the original labelled weighted polynomials into a factor's specified root algebra. -/
def weightedFactorRootUnit (q r : ℕ) (f : Polynomial A) :
    LabelledWeightedRing q r →ₐ[ℂ] FactorRoots q r f := by
  letI : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  letI : IsScalarTower ℂ (Depth.RB (q+2*r)) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom (q+2*r) f).commutes z).symm
  exact (weightedBaseRight q r A).restrictScalars ℂ

@[simp] theorem weightedFactorRootUnit_X (q r : ℕ) (f : Polynomial A) (i : Fin q ⊕ Fin r) :
    weightedFactorRootUnit q r f (MvPolynomial.X i) = factorRoot q r f i := rfl

/-- Canonical insertion of the original signed root module into its specified factor specialization. -/
def weightedFactorSignedUnit (q r : ℕ) (f : Polynomial A) :
    signedInvariantComplexModule q r →ₗ[ℂ] FactorSignedModule q r f := by
  letI : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  letI : IsScalarTower ℂ (Depth.RB (q+2*r)) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom (q+2*r) f).commutes z).symm
  exact (TensorProduct.mk (Depth.RB (q+2*r)) A (signedInvariantModule q r) 1).restrictScalars ℂ

@[simp] theorem weightedFactorSignedUnit_inclusion (q r : ℕ) (f : Polynomial A)
    (p : signedInvariantComplexModule q r) :
    factorSignedInclusion q r f (weightedFactorSignedUnit q r f p) = weightedFactorRootUnit q r f p.val := rfl

end KhanSL2.Macdonald
