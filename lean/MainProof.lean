module

public import KhanSL2.Collision.Proof
public import KhanSL2.Collision.Completion

@[expose] public section

/-! Completion of the original proposition for the specified canonical map.
The constructions of `phi`, both PVA structures, and `MainStatement` are unchanged.
-/

namespace KhanSL2

/-- The specified canonical map is a graded differential PVA isomorphism. -/
theorem mainStatement : MainStatement :=
  Collision.mainStatement_of_kFactor Collision.kFactor

/-- In particular, the original, explicitly defined canonical map is bijective. -/
theorem phi_bijective : Function.Bijective phi :=
  mainStatement_iff_bijective.mp mainStatement

end KhanSL2
