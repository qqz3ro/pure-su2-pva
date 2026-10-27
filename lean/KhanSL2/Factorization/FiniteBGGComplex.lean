module

public import KhanSL2.Conditional.BGGHomologyAction
public import KhanSL2.PolynomialBGG.FiniteTerms
public import KhanSL2.PolynomialBGG.ProjectiveTerms
public import KhanSL2.Factorization.FibreComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization.FiniteBGG
open Conditional
open scoped KhanSL2.Conditional

/-- The previously constructed actual exterior BGG differential over its
prescribed elementary coefficient ring, packaged as a chain complex. -/
def complex (B : ℕ) : ChainComplex (ModuleCat (CoefficientRing B)) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of (CoefficientRing B) (BGGComplex.Term B n))
    (fun n => ModuleCat.ofHom (bggDifferential B n))
    (fun n => by
      apply ModuleCat.hom_ext
      exact bggDifferential_square_zero B n)

@[simp] theorem complex_X (B n : ℕ) :
    (complex B).X n = ModuleCat.of (CoefficientRing B) (BGGComplex.Term B n) := rfl

@[simp] theorem complex_d (B n : ℕ) :
    (complex B).d (n+1) n = ModuleCat.ofHom (bggDifferential B n) :=
  by simp only [complex,ChainComplex.of,ChainComplex.of_d]

theorem term_finite (B n : ℕ) : Module.Finite (CoefficientRing B) ((complex B).X n) :=
  PolynomialBGG.bggTerm_finite B n

theorem term_projective (B n : ℕ) : Module.Projective (CoefficientRing B) ((complex B).X n) :=
  PolynomialBGG.bggTerm_projective B n

theorem bounded (B n : ℕ) (hn : B < n) : Subsingleton ((complex B).X n) :=
  BGGComplex.term_subsingleton_of_lt B n hn

end KhanSL2.Factorization.FiniteBGG
