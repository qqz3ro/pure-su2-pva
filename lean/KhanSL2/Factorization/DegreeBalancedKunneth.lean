module

public import KhanSL2.Factorization.ExternalBalancedComplex
public import KhanSL2.Factorization.ExternalTensorDegreeHomology
public import KhanSL2.Factorization.FlatComplexHomology
public import KhanSL2.Factorization.DegreeExternalBaseChange

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
open CategoryTheory
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (R S A : Type) [CommRing R] [CommRing S] [CommRing A]
  [Algebra ℂ R] [Algebra ℂ S] [Algebra ℂ A]
  [Algebra R A] [Algebra S A] [Algebra (R ⊗[ℂ] S) A]
  [IsScalarTower ℂ R A] [IsScalarTower ℂ S A]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent R M]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent S N]
variable (h : ∀ r : R, ∀ s : S, algebraMap (R ⊗[ℂ] S) A (r ⊗ₜ[ℂ] s) =
  algebraMap R A r * algebraMap S A s)
attribute [local instance] coefficientHomogeneousHomologyModule coefficientHomogeneousHomologyIsScalarTower
  coefficientHomogeneousHomologySMulCommClass externalHomogeneousHomologyModule

/-- Flat extension of the independent coefficient variables identifies the actual balanced
homology in degree p with the original external tensor homology in that same degree. -/
def degreeBalancedFlatHomologyEquiv [Module.Flat (R ⊗[ℂ] S) A] (p : ℕ) :
    (balancedTensorComplex A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A)).homology p ≃ₗ[A]
      A ⊗[R ⊗[ℂ] S] TensorHomology M N p :=
  (((HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) p).mapIso
    (externalBalancedComplexIso R S A M N h).symm).toLinearEquiv).trans
      ((flatComplexHomologyEquiv A (externalTensorComplex R S M N) p).symm.trans
        ((externalTensorComplexHomologyEquiv R S M N p).baseChange (R ⊗[ℂ] S) A _ _))

/-- Degreewise Künneth for the actual balanced scalar-extended CE complexes. This is obtained
from field Künneth and flat extension of the original independent coefficient rings. -/
def degreeBalancedKunnethEquiv [Module.Flat (R ⊗[ℂ] S) A] (p : ℕ) :
    (balancedTensorComplex A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A)).homology p ≃ₗ[A]
      ⨁ q : Fin (p+1), (A ⊗[R] Homology M q.val) ⊗[A] (A ⊗[S] Homology N (p-q.val)) :=
  (degreeBalancedFlatHomologyEquiv R S A M N h p).trans
    (degreeExternalBaseChangeEquiv R S A M N h p)

end KhanSL2.Factorization
