module

public import KhanSL2.Factorization.FiniteBGGNativeHomology
public import KhanSL2.SymmetricFamily.FactorCurrent

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct DirectSum
namespace KhanSL2.Factorization.BGGTransfer
open BGG Conditional SymmetricFamily
attribute [local instance] coefficientHomogeneousHomologyModule
  coefficientHomogeneousHomologyIsScalarTower coefficientHomogeneousHomologySMulCommClass

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- Replace the original exterior CE homology factors with K, preserving all
coefficient actions and the actual complementary-degree indexing. -/
def exteriorFactorSideEquivK (r s : ℕ) (f g : Polynomial A) (p : ℕ) :
    letI := factorCoefficientAlgebra r f
    letI := factorCoefficientAlgebra s g
    (⨁ q : Fin (p+1), (A ⊗[Depth.RB r] Homology (⋀[ℂ]^r Current) q.val) ⊗[A]
      (A ⊗[Depth.RB s] Homology (⋀[ℂ]^s Current) (p-q.val))) ≃ₗ[A]
    (⨁ q : Fin (p+1), (A ⊗[Depth.RB r] K r q.val) ⊗[A]
      (A ⊗[Depth.RB s] K s (p-q.val))) := by
  letI := factorCoefficientAlgebra r f
  letI := factorCoefficientAlgebra s g
  exact DFinsupp.mapRange.linearEquiv (fun q : Fin (p+1) =>
    TensorProduct.congr
      ((exteriorHomologyEquivK r q.val).baseChange (Depth.RB r) A _ _)
      ((exteriorHomologyEquivK s (p-q.val)).baseChange (Depth.RB s) A _ _))

end KhanSL2.Factorization.BGGTransfer
