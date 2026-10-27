module

public import KhanSL2.Factorization.FiniteBGGHomology
public import KhanSL2.Factorization.FlatComplexHomology

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped TensorProduct
namespace KhanSL2.Factorization.BGGTransfer
open Conditional NonnegativeCone

variable (B : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB B) A]
  [Module.Flat (Depth.RB B) A]

/-- The prescribed K-module after a flat scalar extension is exactly the
homology of the original scalar-extended finite BGG complex. -/
def sourceHomologyEquiv (p : ℕ) :
    A ⊗[Depth.RB B] K B p ≃ₗ[A] (scalarComplex A (FiniteBGG.complex B)).homology p :=
  ((FiniteBGG.homologyEquivK B p).symm.baseChange (Depth.RB B) A _ _).trans
    (flatComplexHomologyEquiv A (FiniteBGG.complex B) p)

end KhanSL2.Factorization.BGGTransfer

