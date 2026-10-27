module

public import KhanSL2.Factorization.FiniteBGGTransferEquivalence
public import KhanSL2.Factorization.RelativeChainsScalarComplex
public import KhanSL2.Factorization.ScalarComplexHomotopy

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open CategoryTheory
open scoped TensorProduct
namespace KhanSL2.Factorization.BGGTransfer
open BGG SymmetricFamily Conditional NonnegativeCone
attribute [local instance] coefficientChainModule coefficientDegreeModule

variable (B : ℕ) (A : Type) [CommRing A] [Algebra (CoefficientRing B) A]
  [Algebra ℂ A] [IsScalarTower ℂ (CoefficientRing B) A]

/-- The actual relative CE complex of any scalar-extended exterior coefficient
family is homotopy equivalent to the scalar-extended original finite BGG complex.
This remains valid on nonflat and nonreduced fibres. -/
def exteriorBaseChangeHomotopyEquiv :
    HomotopyEquiv
      (coefficientRelativeComplex A (CoefficientBaseChange (CoefficientRing B) (⋀[ℂ]^B BGG.Current) A))
      (scalarComplex A (FiniteBGG.complex B)) :=
  (HomotopyEquiv.ofIso (relativeChainsScalarComplexIso
    (CoefficientRing B) (⋀[ℂ]^B BGG.Current) A).symm).trans
      (scalarHomotopyEquiv A (exteriorHomotopyEquiv B))

omit [Algebra ℂ A] [IsScalarTower ℂ (CoefficientRing B) A] in
theorem exteriorBaseChange_term_finite (j : ℕ) :
    Module.Finite A ((scalarComplex A (FiniteBGG.complex B)).X j) := by
  let := FiniteBGG.term_finite B j
  change Module.Finite A (A ⊗[CoefficientRing B] (FiniteBGG.complex B).X j)
  infer_instance

omit [Algebra ℂ A] [IsScalarTower ℂ (CoefficientRing B) A] in
theorem exteriorBaseChange_term_projective (j : ℕ) :
    Module.Projective A ((scalarComplex A (FiniteBGG.complex B)).X j) := by
  let := FiniteBGG.term_projective B j
  change Module.Projective A (A ⊗[CoefficientRing B] (FiniteBGG.complex B).X j)
  infer_instance

omit [Algebra ℂ A] [IsScalarTower ℂ (CoefficientRing B) A] in
theorem exteriorBaseChange_bounded (j : ℕ) (hj : B < j) :
    Subsingleton ((scalarComplex A (FiniteBGG.complex B)).X j) := by
  let := FiniteBGG.bounded B j hj
  change Subsingleton (A ⊗[CoefficientRing B] (FiniteBGG.complex B).X j)
  infer_instance

end KhanSL2.Factorization.BGGTransfer

