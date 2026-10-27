module

public import KhanSL2.SymmetricFamily.RootFactorAlgebra
public import KhanSL2.SymmetricFamily.RootPermutation

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The original complex scalar structure and root permutations on a factor's
labelled-root algebra, keeping its prescribed coefficient specialization explicit. -/

noncomputable section
namespace KhanSL2.SymmetricFamily

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The exact coefficient algebra of the specified factor polynomial. -/
abbrev factorCoefficientAlgebra (n : ℕ) (f : Polynomial A) : Algebra (Depth.RB n) A :=
  (Collision.coeffHom n f).toRingHom.toAlgebra

namespace FactorRootScalars

scoped instance factorRootsComplexAlgebra (n : ℕ) (f : Polynomial A) :
    Algebra ℂ (FactorRoots n f) := by
  unfold FactorRoots
  letI := factorCoefficientAlgebra n f
  letI : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  infer_instance

scoped instance factorRootsComplexTower (n : ℕ) (f : Polynomial A) :
    IsScalarTower ℂ A (FactorRoots n f) := by
  unfold FactorRoots
  let := factorCoefficientAlgebra n f
  let : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  infer_instance

end FactorRootScalars

/-- Honest root permutations in the actual factor specialization. -/
def factorRootPermutation (n : ℕ) (f : Polynomial A) (σ : Equiv.Perm (Fin n)) :
    FactorRoots n f ≃ₐ[A] FactorRoots n f := by
  letI := factorCoefficientAlgebra n f
  exact baseRootPermutation n A σ

@[simp] theorem factorRootPermutation_root (n : ℕ) (f : Polynomial A)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    factorRootPermutation n f σ (factorRoot n f i) = factorRoot n f (σ i) := by
  let := factorCoefficientAlgebra n f
  exact baseRootPermutation_baseRoot n A σ i

end KhanSL2.SymmetricFamily
