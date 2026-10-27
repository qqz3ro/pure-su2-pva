module

public import KhanSL2.PolynomialBGG.RootRingFree
public import KhanSL2.PolynomialBGG.LabelledRoot

@[expose] public section
noncomputable section
namespace KhanSL2.PolynomialBGG
open Conditional
open scoped KhanSL2.Conditional

/-- Every actual BGG term is projective for its prescribed coefficient-ring action. -/
theorem bggTerm_projective (B p : ℕ) :
    Module.Projective (CoefficientRing B) (BGGComplex.Term B p) := by
  have := labelledCoinvariants_projective B p
  exact bggTerm_projective_of_labelled B p

end KhanSL2.PolynomialBGG
