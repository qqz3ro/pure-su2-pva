module

public import KhanSL2.SourceBracketJacobi

@[expose] public section

/-!
# The source is a graded differential Poisson vertex superalgebra

This entry point depends only on the source presentation and the PVA axioms.
It does not import the Chevalley--Eilenberg or cohomology construction.
-/

noncomputable section

namespace KhanSL2

/-- The concrete bracket on the original source quotient satisfies every
axiom of the originally defined graded differential super-PVA structure. -/
theorem source_isPVA : IsPVA sourceData Source.bracket where
  algebra := source_isGradedDifferentialSuperalgebra
  sesquilinear_left := Source.bracket_left_translation
  sesquilinear_right := Source.bracket_right_translation
  super_skew := Source.bracket_super_skew
  super_jacobi := Source.bracket_super_jacobi
  super_leibniz := Source.bracket_super_leibniz
  bracket_degree := Source.bracket_degree

/-- The source structural claims that occur in `MainStatement` have a
constructed witness and require no assumptions about the target. -/
theorem source_pva_exists :
    ∃ br : LambdaBracket Source, IsPVA sourceData br ∧ IsSourceBracket br :=
  ⟨Source.bracket, source_isPVA, Source.bracket_generator_formulas⟩

end KhanSL2
