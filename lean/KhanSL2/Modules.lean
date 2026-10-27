module

public import KhanSL2.Modules.SourceDualModel
public import KhanSL2.Modules.CoefficientLinearity
public import KhanSL2.Modules.DepthModuleComparison
public import KhanSL2.Modules.BGGAssembly

@[expose] public section

/-!
# Source dual, coefficient action, and the specified polynomial comparison

`sourceDualEquiv` identifies the restricted dual of the actual source with the
actual weighted-root polynomial module `JB`. The actual coefficient shifts on
relative CE chains descend to commuting operators on `KTotal`; the first `B`
power sums define its `R B` action. `psiBLinear` equips exactly the existing
Taylor comparison `psiB` with proved `R B`-linearity and is surjective.

`depthJBEquiv` reconciles the imported depth module with this same polynomial
module via elementary symmetric coordinates. `kTotalEquivBGG` identifies the
actual homology with the assembled BGG homology. The finite projective
presentation and kernel-support results used in depth descent are proved in
`PolynomialBGG` and `Collision`. The complete isomorphism theorem is in
`MainProof`.
-/
