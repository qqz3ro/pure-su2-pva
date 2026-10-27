module

public import KhanSL2.Factorization.ExternalBalancedDegreeForget
public import KhanSL2.Factorization.ScalarComplexHomotopy

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open CategoryTheory
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG SymmetricFamily NonnegativeCone

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
attribute [local instance] externalDegreeModule coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientDegreeModule coefficientDegreeIsScalarTower
  coefficientDegreeSMulCommClass

/-- The original external degree inclusion commutes with the original signed boundary. -/
theorem externalDegreeForget_differential (p : ℕ) :
    (externalDegreeForget R S M N p).comp (externalDegreeDifferential R S M N p) =
      (externalTotalShortComplex R S M N).g.hom.comp (externalDegreeForget R S M N (p+1)) := by
  apply LinearMap.ext
  intro z
  exact tensorDegreeForget_boundary M N p z

/-- Literal mixed balancing in each degree intertwines the actual CE tensor differentials. -/
theorem externalBalancedDegreeEquiv_differential (p : ℕ)
    (z : (scalarComplex A (externalTensorComplex R S M N)).X (p+1)) :
    externalBalancedDegreeEquiv R S A M N h p
      ((scalarComplex A (externalTensorComplex R S M N)).d (p+1) p z) =
      (balancedTensorComplex A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A)).d (p+1) p
        (externalBalancedDegreeEquiv R S A M N h (p+1) z) := by
  apply balancedTensorDegreeForget_injective A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A) p
  rw [externalBalancedDegreeEquiv_forget]
  have hd := congrArg (fun f => f.hom (externalBalancedDegreeEquiv R S A M N h (p+1) z))
    (balancedTensorDegreeForget_differential A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A) p)
  change balancedTensorDegreeForget A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A) p
    ((balancedTensorComplex A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A)).d (p+1) p
      (externalBalancedDegreeEquiv R S A M N h (p+1) z)) =
    balancedTensorDifferential A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A)
      (balancedTensorDegreeForget A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A) (p+1)
        (externalBalancedDegreeEquiv R S A M N h (p+1) z)) at hd
  rw [hd,externalBalancedDegreeEquiv_forget]
  rw [← externalChainBaseChange_differential R S M N A
    (externalBalancedChainEquiv R S M N A h) (externalBalancedChainEquiv_tmul R S M N A h)]
  apply congrArg (externalBalancedChainEquiv R S M N A h)
  have hc := congrArg (fun f => f.baseChange A) (externalDegreeForget_differential R S M N p)
  simp only [LinearMap.baseChange_comp] at hc
  rw [scalarComplex_d,externalTensorComplex_d]
  exact LinearMap.congr_fun hc z

/-- The original scalar-extended independent-coefficient tensor complex is
canonically the actual balanced tensor complex. No flatness is needed here. -/
def externalBalancedComplexIso :
    scalarComplex A (externalTensorComplex R S M N) ≅
      balancedTensorComplex A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (externalBalancedDegreeEquiv R S A M N h p).toModuleIso)
    (fun i j hij => by
      have hji : j+1=i := hij
      subst i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (externalBalancedDegreeEquiv_differential R S A M N h j z).symm)

end KhanSL2.Factorization

