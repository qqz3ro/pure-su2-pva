# Guide to the completed proof

The final theorem is a short assembly of the development:

```lean
theorem KhanSL2.mainStatement : KhanSL2.MainStatement :=
  KhanSL2.Collision.mainStatement_of_kFactor KhanSL2.Collision.kFactor
```

The implementation is in [MainProof.lean](../lean/MainProof.lean). This guide
explains what the two dependencies contain. Exact declaration names and links
are indexed in [DECLARATIONS.md](DECLARATIONS.md).

## Fixed structures and the canonical map

The source starts as a concrete differential generators-and-relations quotient.
Its bracket is constructed, and all super-PVA axioms are proved. Independently,
the target is constructed from finite relative CE cochains: the differential
squares to zero, preserves invariants, and supports the induced product,
translation, grading, and bracket. Those induced operations also satisfy the
PVA axioms.

The prescribed cocycles satisfy the source relations. Evaluation therefore
descends to the fixed linear map `phi`; its operation-preservation laws and
uniqueness are proved before the isomorphism theorem. At this stage proving
`MainStatement` is equivalent to proving that this particular map is bijective.

## Injectivity and the dual comparison

Closed Cartan chains produce functionals separating each finite source sector.
Finite Taylor comparisons and the grading extend this separation to arbitrary
finite sums, proving `phi_injective`.

The chain/cochain dictionary identifies each homogeneous cohomology piece with
the dual of a finite-dimensional relative CE homology piece. Under that
identification, `psiK` is the transpose of `phi`, and injectivity gives its
surjectivity. The restricted source dual is then identified with the polynomial
module `J`; the original coefficient operators give the coefficient-ring action
on `K`, and the specified comparison `psi` is proved linear for these actions.

## Relative BGG, depth, and the comparison induction

The development constructs the relative affine A1 BGG resolution on its stated
induced terms, including its augmentation, exactness, energy grading, relative
projectivity, and relative splittings. Applying the coefficient construction
gives the finite BGG complex used in the proof.

Its terms are proved finite and projective over the coefficient ring; the top
term is free of rank one. The low-degree comparison follows from the deformation
argument. For middle degrees, the source-side depth bound and support of the
comparison kernel on the collision locus force that kernel to vanish. Strong
induction on coefficient degree assembles these cases.

This part is available as
`Conditional.mainStatement_of_collisionSupport`: it is an intermediate theorem
whose collision-support input is supplied by the next part of the development.

## Strong Macdonald and factorization on coprime charts

The existing checked Strong Macdonald/Hodge calculation identifies harmonic
invariants and their free generators. The `Macdonald/StrongBridge*` modules
identify that model with the concrete coefficient/cohomology constructions,
including normalization, grading, coefficient operators, and coproducts.

The actual normalized symmetric coproduct is compared with root coordinates.
This proves the symmetric chart quasi-isomorphism and then
`SymmetricFamily.symmetricTensorShuffle`. Specialization and finite local
filtrations transfer the result to the exterior coefficient shuffle; collisions
within either factor are permitted, while the two factor supports are disjoint.

Finite BGG comparison and complex-point detection give the chart homology
comparison. Kunneth is applied with the original independent coefficient rings
and the required flatness before the mixed coefficient actions are balanced.
This produces `chartFactorizationEquiv` for the original coefficient homology.
The final theorem `Collision.kFactor` has no remaining shuffle or factorization
hypothesis.

## Closing the proof

The proved factorization of `K`, together with the already proved factorization
of `J`, supplies collision support for the original comparison kernel.
The BGG/depth/deformation induction then proves the needed comparison
injectivity. Homogeneous duality gives surjectivity of `phi`; its proved
injectivity and its established PVA morphism laws give `MainStatement`.

```text
checked Strong Macdonald calculation
    -> actual symmetric shuffle
    -> exterior shuffle and finite BGG chart comparison
    -> coefficient-compatible Kunneth
    -> KFactor
    -> collision support
    -> depth/deformation comparison induction
    -> bijectivity of the specified phi
    -> MainStatement
```

All arrows in this diagram summarize proved dependencies, not new assumptions.

## Reading the verification result

A native build checks Lean proof terms. The final axiom audit checks that the
completed theorem has its exact unconditional type and that its dependencies
use only `propext`, `Classical.choice`, and `Quot.sound`. Neither check alone
decides whether an English formulation has been translated as intended; that
is why the finite-mode convention and other mathematical choices are listed
explicitly in [SCOPE.md](SCOPE.md).

