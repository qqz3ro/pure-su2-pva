module

public import KhanSL2.CanonicalTarget

@[expose] public section

/-! Concrete invariant primitives used to evaluate the source relations. -/

noncomputable section
namespace KhanSL2.CanonicalRelations

/-- The invariant primitive of the square of the canonical even cocycle. -/
def squarePrimitive : Cochain :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
    epsilon a b c • wedge (wedge (generator (.b 0 a)) (generator (.b 0 b)))
      (generator (.c 1 c))

/-- The invariant contraction used for the mixed translated relation. -/
def contraction : Cochain :=
  ∑ a : Fin 3, wedge (generator (.b 0 a)) (generator (.b 1 a))

end KhanSL2.CanonicalRelations
