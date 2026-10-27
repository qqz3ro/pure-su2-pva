module

public import KhanSL2.BGG.ColorRootEquivariance

@[expose] public section

namespace KhanSL2.BGG.PositiveCE

/-- Constants act by even derivations on the actual pure-positive CE complex. -/
theorem colorAction_parity (a : Fin 3) (u : Cochain) :
    colorAction a (FiniteExterior.parityLinear u) =
      FiniteExterior.parityLinear (colorAction a u) := by
  apply inclusion_injective
  simp only [inclusion_colorAction, inclusion_parity, KhanSL2.colorAction_parity]

end KhanSL2.BGG.PositiveCE