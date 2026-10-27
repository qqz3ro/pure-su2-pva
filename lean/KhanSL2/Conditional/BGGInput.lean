module

public import KhanSL2.Conditional.TopRankOne
public import KhanSL2.PolynomialBGG.FiniteTerms
public import KhanSL2.PolynomialBGG.ProjectiveTerms

@[expose] public section

/-!
# Proved polynomial-module properties of the fixed BGG complex

The coefficient action, differential linearity, compatibility with complex scalars,
and coefficient-linearity of the canonical homology comparison are proved.
Every actual BGG term is finitely generated and projective for this action.
The legacy `PolynomialBGGInput` proposition is supplied by the theorem
`polynomialBGGInput`; it is no longer a remaining hypothesis.
-/

noncomputable section
namespace KhanSL2.Conditional
open scoped KhanSL2.Conditional

/-- The legacy property container for the constructed coefficient action. -/
structure BGGPolynomialProperties (B : ℕ) : Prop where
  projective : ∀ p, Module.Projective (CoefficientRing B) (BGGComplex.Term B p)

/-- The former polynomial input, now proved for the fixed model. -/
def PolynomialBGGInput : Prop :=
  ∀ B : ℕ, BGGPolynomialProperties B

/-- Every actual BGG term is projective over its prescribed coefficient ring. -/
theorem bggPolynomialProperties (B : ℕ) : BGGPolynomialProperties B :=
  ⟨fun p => PolynomialBGG.bggTerm_projective B p⟩

/-- The entire former polynomial hypothesis is a proved theorem. -/
theorem polynomialBGGInput : PolynomialBGGInput := bggPolynomialProperties

end KhanSL2.Conditional
