module

public import KhanSL2.Factorization.ExternalKunneth
public import KhanSL2.Factorization.ScalarPairHomology
public import KhanSL2.Factorization.FlatScalarHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG SymmetricFamily
variable (R S : Type) [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent R M]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent S N]
attribute [local instance] externalTensorHomologyModule coefficientChainModule
  coefficientChainIsScalarTower coefficientChainSMulCommClass
  coefficientTotalHomologyModule coefficientTotalHomologyIsScalarTower coefficientTotalHomologySMulCommClass

/-- The signed tensor boundary over both original coefficient rings jointly. -/
abbrev externalTotalShortComplex : ShortComplex (ModuleCat (R ⊗[ℂ] S)) :=
  scalarPairShortComplex (R ⊗[ℂ] S) (relativeTensorDifferential M N)
    (relativeTensorDifferential_comp_self M N) (externalChainAction R S M N)
    (externalChainAction_differential R S M N)

/-- Identifying the explicit joint-linear quotient retains its original tensor classes. -/
def externalTotalQuotientEquiv :
    (externalTotalShortComplex R S M N).moduleCatLeftHomologyData.H ≃ₗ[R ⊗[ℂ] S]
      TensorTotalHomology M N :=
  LinearEquiv.ofBijective
    (scalarPairQuotientMap (R ⊗[ℂ] S) (relativeTensorDifferential M N)
      (relativeTensorDifferential_comp_self M N) (externalChainAction R S M N)
      (externalChainAction_differential R S M N))
    (scalarPairQuotientMap_bijective (R ⊗[ℂ] S) (relativeTensorDifferential M N)
      (relativeTensorDifferential_comp_self M N) (externalChainAction R S M N)
      (externalChainAction_differential R S M N))

@[simp] theorem externalTotalQuotientEquiv_mk
    (z : LinearMap.ker (externalTotalShortComplex R S M N).g.hom) :
    externalTotalQuotientEquiv R S M N (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (⟨z.val,z.property⟩ : LinearMap.ker (relativeTensorDifferential M N)) := rfl

@[simp] theorem externalTotalQuotientEquiv_symm_mk
    (z : LinearMap.ker (relativeTensorDifferential M N)) :
    (externalTotalQuotientEquiv R S M N).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (⟨z.val,z.property⟩ : LinearMap.ker (externalTotalShortComplex R S M N).g.hom) := by
  apply (externalTotalQuotientEquiv R S M N).injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable (A : Type) [CommRing A] [Algebra (R ⊗[ℂ] S) A]

/-- Flat scalar extension of genuine tensor homology, before identifying the
extended chains with the balanced tensor of the two scalar-extended factors. -/
def externalFlatQuotientEquiv [Module.Flat (R ⊗[ℂ] S) A] :
    A ⊗[R ⊗[ℂ] S] TensorTotalHomology M N ≃ₗ[A]
      ((externalTotalShortComplex R S M N).map (scalarFunctor A)).moduleCatLeftHomologyData.H :=
  ((externalTotalQuotientEquiv R S M N).symm.baseChange (R ⊗[ℂ] S) A _ _).trans
    (flatShortQuotientEquiv A (externalTotalShortComplex R S M N))

/-- Every represented cycle is carried to its actual tensor-extended cycle. -/
theorem externalFlatQuotientEquiv_mk [Module.Flat (R ⊗[ℂ] S) A]
    (a : A) (z : LinearMap.ker (relativeTensorDifferential M N)) :
    externalFlatQuotientEquiv R S M N A (a ⊗ₜ[R ⊗[ℂ] S] Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (flatShortCyclesEquiv A (externalTotalShortComplex R S M N)
        (a ⊗ₜ[R ⊗[ℂ] S] (⟨z.val,z.property⟩ :
          LinearMap.ker (externalTotalShortComplex R S M N).g.hom))) := by
  change flatShortQuotientEquiv A (externalTotalShortComplex R S M N)
    (a ⊗ₜ[R ⊗[ℂ] S] (externalTotalQuotientEquiv R S M N).symm (Submodule.Quotient.mk z)) = _
  rw [externalTotalQuotientEquiv_symm_mk,flatShortQuotientEquiv_mk]

/-- The original field Künneth isomorphism survives the specified flat extension
of the two independent coefficient variables. -/
def externalFlatKunnethQuotientEquiv [Module.Flat (R ⊗[ℂ] S) A] :
    A ⊗[R ⊗[ℂ] S] ExternalTensor R S (TotalHomology M) (TotalHomology N) ≃ₗ[A]
      ((externalTotalShortComplex R S M N).map (scalarFunctor A)).moduleCatLeftHomologyData.H :=
  ((externalKunnethEquiv R S M N).baseChange (R ⊗[ℂ] S) A _ _).trans
    (externalFlatQuotientEquiv R S M N A)

end KhanSL2.Factorization
