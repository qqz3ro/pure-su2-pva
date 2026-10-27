module

public import KhanSL2.Conditional.Assembly

@[expose] public section

/-!
# Assembly of the specified-map theorem from collision support

`Conditional.mainStatement_of_collisionSupport` proves `MainStatement` from
middle-degree collision support. It assembles the relative BGG resolution,
coefficient actions and linearity, finite projectivity, the rank-one top term,
depth descent, low-degree deformation, and finite-dimensional duality.

The required collision support follows from the factorization proved in
`KhanSL2.Collision.Proof`. `MainProof` supplies this proved input and concludes
the unconditional theorem for the specified canonical map.
-/
