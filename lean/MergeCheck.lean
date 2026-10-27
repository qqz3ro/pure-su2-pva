module

public import BGG
public import KhanSL2.DictionaryStatement

@[expose] public section

/-! Current-algebra convention check.

The BGG development and milestone M2 live in one environment without name clashes,
and they use the same current algebra `𝔩 = ℂ[z] ⊗ 𝔰𝔩₂` with the same Lie structure.
The coefficient-homology connection is now proved separately in `BGGBridgeStatement`. -/

example : KhanSL2.BGG.Current = KhanSL2.Current.Cur := rfl

example : (inferInstance : LieRing KhanSL2.BGG.Current) =
    (inferInstance : LieRing KhanSL2.Current.Cur) := rfl

example : (inferInstance : LieAlgebra ℂ KhanSL2.BGG.Current) =
    (inferInstance : LieAlgebra ℂ KhanSL2.Current.Cur) := rfl

example (n : ℕ) (a : Fin 3) :
    KhanSL2.BGG.mode n (KhanSL2.MatrixSL2.color a) = KhanSL2.Current.cur n a := rfl

#check @KhanSL2.BGG.relative_bgg_resolution
#check @KhanSL2.BGG.RelativeCochains.cohomologyEquiv
#check @KhanSL2.Current.milestoneM2
