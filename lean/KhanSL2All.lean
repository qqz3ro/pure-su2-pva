module

public import KhanSL2
public import BGG
public import BGGBridge
public import KhanSL2.Modules
public import Depth
public import KhanSL2.Conditional
public import KhanSL2.Deformation
public import KhanSL2.PolynomialBGG
public import KhanSL2.Macdonald
public import StrongMacdonald
public import Collision
public import MainProof

@[expose] public section

/-! Complete formalization of the original specified canonical map.
Use `KhanSL2.mainStatement : KhanSL2.MainStatement` and
`KhanSL2.phi_bijective : Function.Bijective KhanSL2.phi` from `MainProof`.
-/
