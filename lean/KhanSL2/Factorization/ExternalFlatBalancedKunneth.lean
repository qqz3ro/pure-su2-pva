module

public import KhanSL2.Factorization.ExternalFlatChainCycles
public import KhanSL2.Factorization.ExternalChainScalars
public import KhanSL2.Factorization.MixedExternalBaseChangeEquiv

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
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
variable (h : ∀ r : R, ∀ s : S, algebraMap (R ⊗[ℂ] S) A (r ⊗ₜ[ℂ] s) =
  algebraMap R A r * algebraMap S A s)
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass
  externalTensorHomologyModule coefficientTotalHomologyModule coefficientTotalHomologyIsScalarTower
  coefficientTotalHomologySMulCommClass

/-- The actual mixed scalar extension on the two original relative chain factors. -/
def externalBalancedChainEquiv :
    A ⊗[R ⊗[ℂ] S] (externalTotalShortComplex R S M N).X₂ ≃ₗ[A]
      RelativeChains (CoefficientBaseChange R M A) ⊗[A] RelativeChains (CoefficientBaseChange S N A) :=
  ((externalChainObjectEquiv R S M N).baseChange (R ⊗[ℂ] S) A _ _).trans
    ((MixedExternal.equiv R S A (RelativeChains M) (RelativeChains N) h).trans
      (TensorProduct.congr (relativeChainsScalarEquiv R M A) (relativeChainsScalarEquiv S N A)))

@[simp] theorem externalBalancedChainEquiv_tmul (a : A) (u : RelativeChains M) (v : RelativeChains N) :
    externalBalancedChainEquiv R S M N A h (a ⊗ₜ[R ⊗[ℂ] S] (u ⊗ₜ[ℂ] v)) =
      (a • coefficientChainUnit R M A u) ⊗ₜ[A] coefficientChainUnit S N A v := by
  simp only [externalBalancedChainEquiv,LinearEquiv.trans_apply,LinearEquiv.baseChange_tmul,
    externalChainObjectEquiv_apply,MixedExternal.equiv_tmul,TensorProduct.congr_tmul]
  change (a • coefficientChainUnit R M A u) ⊗ₜ[A] ((1:A) • coefficientChainUnit S N A v) = _
  rw [one_smul]

/-- Field Künneth followed by flat extension of the independent coefficient variables,
expressed in the ordinary tensor of the two original scalar-extended homology modules. -/
def externalBalancedKunnethEquiv [Module.Flat (R ⊗[ℂ] S) A] :
    (A ⊗[R] TotalHomology M) ⊗[A] (A ⊗[S] TotalHomology N) ≃ₗ[A]
      BalancedTensorTotalHomology A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A) :=
  (MixedExternal.equiv R S A (TotalHomology M) (TotalHomology N) h).symm.trans
    (externalFlatTensorKunnethEquiv R S M N A (externalBalancedChainEquiv R S M N A h)
      (externalBalancedChainEquiv_tmul R S M N A h))

/-- The balancing equivalence is exactly the canonical two unit insertions. -/
theorem mixedHomologyEquiv_unit (w : ExternalTensor R S (TotalHomology M) (TotalHomology N)) :
    MixedExternal.equiv R S A (TotalHomology M) (TotalHomology N) h (1 ⊗ₜ[R ⊗[ℂ] S] w) =
      MixedExternal.unit R S A (TotalHomology M) (TotalHomology N) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [TensorProduct.tmul_add,map_add,hu,hv]
  | tmul u v => exact MixedExternal.equiv_tmul R S A (TotalHomology M) (TotalHomology N) h 1 u v

/-- Exact compatibility with the original inverse Künneth and the actual tensor cycle.
This is the unit formula needed to identify the symmetric chart's homology map. -/
theorem externalBalancedKunnethEquiv_unit_inverse_mk [Module.Flat (R ⊗[ℂ] S) A]
    (z : LinearMap.ker (relativeTensorDifferential M N)) :
    externalBalancedKunnethEquiv R S M N A h
      (MixedExternal.unit R S A (TotalHomology M) (TotalHomology N)
        ((externalKunnethEquiv R S M N).symm (Submodule.Quotient.mk z))) =
      Submodule.Quotient.mk (externalBaseChangedCycle R S M N A
        (externalBalancedChainEquiv R S M N A h) (externalBalancedChainEquiv_tmul R S M N A h) 1 z) := by
  rw [← mixedHomologyEquiv_unit R S M N A h]
  change externalFlatTensorKunnethEquiv R S M N A (externalBalancedChainEquiv R S M N A h)
    (externalBalancedChainEquiv_tmul R S M N A h)
    ((MixedExternal.equiv R S A (TotalHomology M) (TotalHomology N) h).symm
      (MixedExternal.equiv R S A (TotalHomology M) (TotalHomology N) h _)) = _
  rw [LinearEquiv.symm_apply_apply]
  exact externalFlatTensorKunnethEquiv_inverse_mk R S M N A
    (externalBalancedChainEquiv R S M N A h) (externalBalancedChainEquiv_tmul R S M N A h) 1 z

end KhanSL2.Factorization
