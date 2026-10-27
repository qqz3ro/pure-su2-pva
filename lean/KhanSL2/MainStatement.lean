module

public import KhanSL2.CanonicalMap
public import KhanSL2.PVAIsomorphism
public import KhanSL2.ColorBasis

@[expose] public section

/-!
# Version 2: the specified canonical map is an isomorphism

The target `Cohomology` is the concrete finite-mode relative CE quotient for
sl₂[x,y]/(y²) relative to the constants, with trivial complex coefficients.
`Mode.b j a` is dual to `t_a x^j y`; `Mode.c j a` is dual to `t_a x^(j+1)`.

The map `phi` has already been defined by evaluation, proved well-defined,
and proved to preserve the unit, product, translation, bracket, and grading.
Both PVA structures have been constructed and proved independently.

The file defines a proposition. It neither proves that proposition nor
declares it as an axiom.
-/

noncomputable section

namespace KhanSL2

/-- The explicitly constructed canonical map is a graded differential PVA
isomorphism. It sends `X_i` to `T^i xClass` and `Y_i` to `T^i yClass`.

The total cohomological degrees of `X` and `Y` are 2 and 3. The three
preserved gradings are `(total CE degree, y-count, spin)`, equivalently the
attachment's `(B,p,S)` with total CE degree `B+p`.
-/
def MainStatement : Prop :=
  IsGradedDifferentialPVAIsomorphism
    sourceData Source.bracket targetData targetBracket phi

/-- All morphism laws are proved, so only bijectivity of the fixed map remains.
This equivalence does not prove either injectivity or surjectivity. -/
theorem mainStatement_iff_bijective : MainStatement ↔ Function.Bijective phi :=
  phiPVAMap.isomorphism_iff_bijective source_isPVA.algebra.grading_internal
    target_isPVA.algebra.grading_internal (fun _ _ ha => phi_degree ha)

end KhanSL2
