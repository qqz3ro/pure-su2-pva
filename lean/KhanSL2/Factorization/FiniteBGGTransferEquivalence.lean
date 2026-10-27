module

public import KhanSL2.Factorization.FiniteBGGTransferTerms
public import Mathlib.Algebra.Homology.Homotopy

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open CategoryTheory
namespace KhanSL2.Factorization.BGGTransfer
open BGG SymmetricFamily Conditional
attribute [local instance] harmonicModule coefficientChainModule coefficientDegreeModule

/-- Identification of the actual harmonic complex with the already proved
finite projective BGG complex, over its original coefficient ring. -/
def exteriorComplexIso (B : ℕ) :
    harmonicComplex (CoefficientRing B) (⋀[ℂ]^B BGG.Current) ≅ FiniteBGG.complex B :=
  HomologicalComplex.Hom.isoOfComponents (fun p => (exteriorTermEquiv B p).toModuleIso)
    (fun i j hij => by
      have h : j+1=i := hij
      subst i
      rw [harmonicComplex_d,FiniteBGG.complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (exteriorTermEquiv_differential B j z).symm)

/-- The original exterior-coefficient relative CE complex has a genuine
coefficient-linear chain homotopy equivalence to the existing finite BGG complex.
No homology base-change assumption enters this construction. -/
def exteriorHomotopyEquiv (B : ℕ) :
    HomotopyEquiv (coefficientRelativeComplex (CoefficientRing B) (⋀[ℂ]^B BGG.Current))
      (FiniteBGG.complex B) :=
  (homotopyEquiv (CoefficientRing B) (⋀[ℂ]^B BGG.Current)).trans
    (HomotopyEquiv.ofIso (exteriorComplexIso B))

end KhanSL2.Factorization.BGGTransfer

