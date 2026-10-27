module

public import KhanSL2.Deformation.Assembly

@[expose] public section

/-!
# The two deformations eliminate the low degrees (paper §5)

* `Deformation.Staircase`: the staircase lemma replacing the spectral sequences;
* `Deformation.Delta`, `CohomologyOps`, `PhiDelta`, `SourceContraction`, `SourceHomotopy`:
  `δ_ℓ`, their action on cohomology and on the source, and the source contractions;
* `RelabelOne`, `AcyclicOne`: `D₁` is the `B = 0` complex after relabelling;
* `SplitOps` … `SplitMap`: `D₀` in split coordinates, two Casimir null-homotopies, Künneth;
* `LowDegreeStaircase`, `LowDegree`: paper Prop. 5.3, `lowDegreeStep : Conditional.LowDegreeStep`;
* `Assembly`: `Conditional.mainStatement_of_twoInputs`.
-/
