module

public import KhanSL2.Factorization.FiniteBGGTransferBaseChange
public import KhanSL2.SymmetricFamily.ExteriorChartCurrent
public import KhanSL2.Factorization.BalancedShuffleComplex
public import KhanSL2.Factorization.CoefficientChainEquivalence
public import TauCeti.Algebra.Homology.Bifunctor.Homotopy

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open CategoryTheory HomologicalComplex MonoidalCategory
open scoped TensorProduct
namespace KhanSL2.Factorization.BGGTransfer
open BGG SymmetricFamily Conditional NonnegativeCone
attribute [local instance] coefficientChainModule coefficientDegreeModule

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The original finite BGG complex specialized along the actual factor coefficients. -/
def factorComplex (n : ℕ) (f : Polynomial A) : ChainComplex (ModuleCat A) ℕ :=
  letI := factorCoefficientAlgebra n f
  scalarComplex A (FiniteBGG.complex n)

/-- The original relative CE complex of a factor fibre has the original finite BGG
complex as a homotopy model, without any flatness hypothesis on the specialization. -/
def factorExteriorHomotopyEquiv (n : ℕ) (f : Polynomial A) :
    HomotopyEquiv (coefficientRelativeComplex A (FactorExterior n f)) (factorComplex n f) := by
  letI := factorCoefficientAlgebra n f
  letI : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  exact exteriorBaseChangeHomotopyEquiv n A

theorem factorComplex_finite (n : ℕ) (f : Polynomial A) (j : ℕ) :
    Module.Finite A ((factorComplex n f).X j) := by
  let := factorCoefficientAlgebra n f
  exact exteriorBaseChange_term_finite n A j

theorem factorComplex_projective (n : ℕ) (f : Polynomial A) (j : ℕ) :
    Module.Projective A ((factorComplex n f).X j) := by
  let := factorCoefficientAlgebra n f
  exact exteriorBaseChange_term_projective n A j

/-- Tensoring the two genuine BGG contractions gives a homotopy model of the
balanced CE tensor complex, over the common coefficient algebra. -/
def factorTensorHomotopyEquiv (r s : ℕ) (f g : Polynomial A) :
    HomotopyEquiv (balancedTensorComplex A (FactorExterior r f) (FactorExterior s g))
      (HomologicalComplex.tensorObj (factorComplex r f) (factorComplex s g)) :=
  HomotopyEquiv.mapBifunctor (curriedTensor (ModuleCat A)) (ComplexShape.down ℕ)
    (factorExteriorHomotopyEquiv r f) (factorExteriorHomotopyEquiv s g)

variable {r s : ℕ} [Algebra (Depth.RB (r+s)) A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- The specified normalized exterior chart comparison, followed by the actual
relative CE shuffle balanced over the original chart algebra. -/
def exteriorChartComplex (c : Collision.ChartData (r+s) r s A) :
    coefficientRelativeComplex A
      (CoefficientBaseChange (Depth.RB (r+s)) (⋀[ℂ]^(r+s) Current) A) ⟶
      balancedTensorComplex A (FactorExterior r c.f₁) (FactorExterior s c.f₂) :=
  (coefficientRelativeComplexIso A (exteriorChartCurrentEquiv c)
    (fun a x => (exteriorChartEquiv c).map_smul a x)).hom ≫
      balancedShuffleComplex A (FactorExterior r c.f₁) (FactorExterior s c.f₂)

/-- The actual exterior chart shuffle transported along the proved BGG contractions. -/
def finiteChartMap (c : Collision.ChartData (r+s) r s A) :
    scalarComplex A (FiniteBGG.complex (r+s)) ⟶
      HomologicalComplex.tensorObj (factorComplex r c.f₁) (factorComplex s c.f₂) :=
  (exteriorBaseChangeHomotopyEquiv (r+s) A).inv ≫ exteriorChartComplex c ≫
    (factorTensorHomotopyEquiv r s c.f₁ c.f₂).hom

end KhanSL2.Factorization.BGGTransfer

