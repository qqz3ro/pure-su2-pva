module

public import KhanSL2.Factorization.ExternalTotalHomology
public import KhanSL2.Factorization.BalancedTotalHomology
public import KhanSL2.Factorization.KunnethCoefficientMaps

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
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

/-- The actual map on relative chains induced by the coefficient unit. -/
abbrev coefficientChainUnit (P : Type) [CommRing P] [Algebra ℂ P]
    (V : Type) [AddCommGroup V] [Module ℂ V] [Module P V] [IsScalarTower ℂ P V]
    [LieRingModule Current V] [LieModule ℂ Current V] [CoefficientLinearCurrent P V]
    (B : Type) [CommRing B] [Algebra P B] [Algebra ℂ B] [IsScalarTower ℂ P B] :=
  coefficientMap (coefficientBaseChangeUnit P V B).toLinearMap
    (constantEquivariant_of_lieHom (coefficientBaseChangeUnit P V B))

variable (e : A ⊗[R ⊗[ℂ] S] (externalTotalShortComplex R S M N).X₂ ≃ₗ[A]
  RelativeChains (CoefficientBaseChange R M A) ⊗[A] RelativeChains (CoefficientBaseChange S N A))
variable (he : ∀ (a : A) (u : RelativeChains M) (v : RelativeChains N),
  e (a ⊗ₜ[R ⊗[ℂ] S] (u ⊗ₜ[ℂ] v)) =
    (a • coefficientChainUnit R M A u) ⊗ₜ[A] coefficientChainUnit S N A v)

include he in
/-- Literal balancing and coefficient extension commute with the unchanged signed boundary. -/
theorem externalChainBaseChange_differential
    (z : A ⊗[R ⊗[ℂ] S] (externalTotalShortComplex R S M N).X₂) :
    e (((externalTotalShortComplex R S M N).g.hom.baseChange A) z) =
      balancedTensorDifferential A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A) (e z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul a z =>
    rw [LinearMap.baseChange_tmul]
    change e (a ⊗ₜ[R ⊗[ℂ] S] relativeTensorDifferential M N z) = _
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add,TensorProduct.tmul_add,hz,hw]
    | tmul u v =>
      rw [relativeTensorDifferential_tmul,TensorProduct.tmul_add,map_add,he,he,he,
        balancedTensorDifferential_tmul,differential_coefficient_smul,relativeParity_coefficient_smul]
      rw [← coefficientMap_differential (coefficientBaseChangeUnit R M A),
        ← coefficientMap_differential (coefficientBaseChangeUnit S N A),
        ← coefficientMap_parity (coefficientBaseChangeUnit R M A).toLinearMap
          (constantEquivariant_of_lieHom (coefficientBaseChangeUnit R M A))]

/-- The chain comparison induces the same literal balanced cycle quotient equivalence. -/
def externalScalarQuotientEquiv :
    ((externalTotalShortComplex R S M N).map (scalarFunctor A)).moduleCatLeftHomologyData.H ≃ₗ[A]
      BalancedTensorTotalHomology A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A) :=
  shortQuotientCongr _ _ e e e
    (externalChainBaseChange_differential R S M N A e he)
    (externalChainBaseChange_differential R S M N A e he)

/-- Actual balanced tensor homology is flat scalar extension of the original external tensor homology. -/
def externalFlatTensorHomologyEquiv [Module.Flat (R ⊗[ℂ] S) A] :
    A ⊗[R ⊗[ℂ] S] TensorTotalHomology M N ≃ₗ[A]
      BalancedTensorTotalHomology A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A) :=
  (externalFlatQuotientEquiv R S M N A).trans (externalScalarQuotientEquiv R S M N A e he)

/-- Flat external Künneth with the actual balanced differential and cycle quotient. -/
def externalFlatTensorKunnethEquiv [Module.Flat (R ⊗[ℂ] S) A] :
    A ⊗[R ⊗[ℂ] S] ExternalTensor R S (TotalHomology M) (TotalHomology N) ≃ₗ[A]
      BalancedTensorTotalHomology A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A) :=
  ((externalKunnethEquiv R S M N).baseChange (R ⊗[ℂ] S) A _ _).trans
    (externalFlatTensorHomologyEquiv R S M N A e he)

end KhanSL2.Factorization
