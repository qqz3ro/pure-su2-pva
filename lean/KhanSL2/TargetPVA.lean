module

public import KhanSL2.CEComplex
public import KhanSL2.BCFullHamiltonianIdentity
public import KhanSL2.RelativeHamiltonian

@[expose] public section

/-! The fixed PVA structure on the original restricted relative cohomology.
All input identities in the descent construction are discharged here. -/

noncomputable section

namespace KhanSL2

/-- The CE differential respects the bracket on relative invariants. -/
theorem relativeBracket_compatibility : RelativeBracketCompatibility BC.bracket :=
  RelativeHamiltonian.relative_compatibility full_isPVA omegaHamiltonian_mem
    fullDifferential_eq_zeroMode_apply

/-- Unit, wedge product, translation, and grading on the original quotient. -/
def targetData : DifferentialData Cohomology :=
  CohomologyDescent.data relativeComplex_laws.translation_commutes
    relativeBracket_compatibility

/-- The bracket induced by the explicitly normalized finite-mode `bc` bracket. -/
def targetBracket : LambdaBracket Cohomology :=
  CohomologyDescent.bracket relativeComplex_laws.translation_commutes
    relativeBracket_compatibility

/-- Every graded differential super-PVA axiom holds on the concrete target. -/
theorem target_isPVA : IsPVA targetData targetBracket :=
  CohomologyDescent.isPVA relativeComplex_laws.translation_commutes
    relativeBracket_compatibility cochain_isPVA

/-- All target operations have their specified values on cocycle representatives. -/
theorem target_isInduced :
    IsInducedOnCohomology BC.bracket targetData targetBracket :=
  CohomologyDescent.induced relativeComplex_laws.translation_commutes
    relativeBracket_compatibility

theorem target_piece (d : Degree) : targetData.piece d = cohomologyPiece d := rfl

end KhanSL2
