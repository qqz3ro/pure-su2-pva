module

public import MainProof

@[expose] public section

/-! Public entry point for the vfinal release.

`KhanSL2.mainStatement` is the original theorem, unchanged from v0.17.0.
The theorem below spells out its proposition so that the fixed source, target,
PVA operations, and canonical map can be inspected directly.
See ../docs/SCOPE.md and ../docs/DECLARATIONS.md.
-/

namespace KhanSL2

/-- The specified canonical map is a graded differential PVA isomorphism. -/
theorem mainStatement_explicit :
    IsGradedDifferentialPVAIsomorphism
      sourceData Source.bracket targetData targetBracket phi :=
  mainStatement

end KhanSL2
