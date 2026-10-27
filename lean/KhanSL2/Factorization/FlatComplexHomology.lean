module

public import KhanSL2.Factorization.FlatScalarHomology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace KhanSL2.Factorization
open NonnegativeCone
variable {R : Type} [CommRing R]
variable (A : Type) [CommRing A] [Algebra R A] [Module.Flat R A]

/-- Flat scalar extension of each actual categorical homology group of a chain complex. -/
def flatComplexHomologyEquiv (C : ChainComplex (ModuleCat R) ℕ) (j : ℕ) :
    A ⊗[R] C.homology j ≃ₗ[A] (scalarComplex A C).homology j :=
  (flatShortHomologyEquiv A (C.sc j)).trans
    ((HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) j).mapIso
      (scalarModuleComplexIso A C)).toLinearEquiv

end KhanSL2.Factorization
