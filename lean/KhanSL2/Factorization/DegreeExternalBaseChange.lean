module

public import KhanSL2.Factorization.DegreeExternalKunneth
public import KhanSL2.Factorization.MixedExternalBaseChangeEquiv

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
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

/-- Base change of the actual degreewise external Künneth equivalence, followed by literal
independent-ring balancing. No Künneth assertion over the chart algebra is assumed. -/
def degreeExternalBaseChangeEquiv (p : ℕ) :
    (A ⊗[R ⊗[ℂ] S] TensorHomology M N p) ≃ₗ[A]
      ⨁ q : Fin (p+1), (A ⊗[R] Homology M q.val) ⊗[A] (A ⊗[S] Homology N (p-q.val)) :=
  ((degreeExternalKunnethEquiv R S M N p).symm.baseChange (R ⊗[ℂ] S) A _ _).trans
    ((TensorProduct.directSumRight (R ⊗[ℂ] S) A A
      (fun q : Fin (p+1) => ExternalTensor R S (Homology M q.val) (Homology N (p-q.val)))).trans
      (DFinsupp.mapRange.linearEquiv (fun q : Fin (p+1) =>
        MixedExternal.equiv R S A (Homology M q.val) (Homology N (p-q.val)) h)))

end KhanSL2.Factorization
