module

public import KhanSL2.Factorization.ExternalFlatChainComparison

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
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
variable (A : Type) [CommRing A] [Algebra ℂ A] [Algebra R A] [Algebra S A]
  [Algebra (R ⊗[ℂ] S) A] [IsScalarTower ℂ R A] [IsScalarTower ℂ S A]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass
  externalTensorHomologyModule coefficientTotalHomologyModule coefficientTotalHomologyIsScalarTower
  coefficientTotalHomologySMulCommClass
variable (e : A ⊗[R ⊗[ℂ] S] (externalTotalShortComplex R S M N).X₂ ≃ₗ[A]
  RelativeChains (CoefficientBaseChange R M A) ⊗[A] RelativeChains (CoefficientBaseChange S N A))
variable (he : ∀ (a : A) (u : RelativeChains M) (v : RelativeChains N),
  e (a ⊗ₜ[R ⊗[ℂ] S] (u ⊗ₜ[ℂ] v)) =
    (a • coefficientChainUnit R M A u) ⊗ₜ[A] coefficientChainUnit S N A v)

/-- The actual extended image of an original tensor cycle. -/
def externalBaseChangedCycle (a : A) (z : LinearMap.ker (relativeTensorDifferential M N)) :
    LinearMap.ker (balancedTensorDifferential A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A)) :=
  ⟨e (a ⊗ₜ[R ⊗[ℂ] S] z.val),by
    change balancedTensorDifferential A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A)
      (e (a ⊗ₜ[R ⊗[ℂ] S] z.val)) = 0
    rw [← externalChainBaseChange_differential R S M N A e he,LinearMap.baseChange_tmul]
    change e (a ⊗ₜ[R ⊗[ℂ] S] relativeTensorDifferential M N z.val) = 0
    rw [z.property,TensorProduct.tmul_zero,map_zero]⟩

/-- The flat comparison retains every represented cycle, not merely its dimension. -/
theorem externalFlatTensorHomologyEquiv_mk [Module.Flat (R ⊗[ℂ] S) A]
    (a : A) (z : LinearMap.ker (relativeTensorDifferential M N)) :
    externalFlatTensorHomologyEquiv R S M N A e he (a ⊗ₜ[R ⊗[ℂ] S] Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (externalBaseChangedCycle R S M N A e he a z) := by
  change externalScalarQuotientEquiv R S M N A e he
    (externalFlatQuotientEquiv R S M N A (a ⊗ₜ[R ⊗[ℂ] S] Submodule.Quotient.mk z)) = _
  rw [externalFlatQuotientEquiv_mk]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  change e (flatShortCyclesEquiv A (externalTotalShortComplex R S M N)
    (a ⊗ₜ[R ⊗[ℂ] S] (⟨z.val,z.property⟩ :
      LinearMap.ker (externalTotalShortComplex R S M N).g.hom))).val = e (a ⊗ₜ[R ⊗[ℂ] S] z.val)
  rw [flatShortCyclesEquiv_val,LinearMap.baseChange_tmul]
  rfl

/-- Compatibility with the inverse of the original field Künneth map on an arbitrary cycle. -/
theorem externalFlatTensorKunnethEquiv_inverse_mk [Module.Flat (R ⊗[ℂ] S) A]
    (a : A) (z : LinearMap.ker (relativeTensorDifferential M N)) :
    externalFlatTensorKunnethEquiv R S M N A e he
      (a ⊗ₜ[R ⊗[ℂ] S] (externalKunnethEquiv R S M N).symm (Submodule.Quotient.mk z)) =
        Submodule.Quotient.mk (externalBaseChangedCycle R S M N A e he a z) := by
  change externalFlatTensorHomologyEquiv R S M N A e he
    (a ⊗ₜ[R ⊗[ℂ] S] externalKunnethEquiv R S M N
      ((externalKunnethEquiv R S M N).symm (Submodule.Quotient.mk z))) = _
  rw [LinearEquiv.apply_symm_apply,externalFlatTensorHomologyEquiv_mk]

end KhanSL2.Factorization
