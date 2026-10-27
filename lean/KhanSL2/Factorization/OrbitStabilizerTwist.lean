module

public import KhanSL2.Factorization.OrbitStabilizer

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KhanSL2.Factorization.FiberTransport

variable {R G I : Type*} [CommRing R] [Group G] [MulAction G I]
variable {M : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Scalar-character twisting includes the sign character on alternating roots. -/
def twist (T : FiberTransport (R:=R) (G:=G) M) (χ : G →* Rˣ) :
    FiberTransport (R:=R) (G:=G) M where
  move g i j h := (T.move g i j h).trans (LinearEquiv.smulOfUnit (χ g))
  one_apply i x := by
    change ((χ 1 : Rˣ) : R) • T.move 1 i i _ x = x
    rw [map_one,Units.val_one,one_smul,T.one_apply]
  mul_apply g h i j k hh hg x := by
    change ((χ (g*h) : Rˣ) : R) • T.move (g*h) i k _ x =
      ((χ g : Rˣ) : R) • T.move g j k hg (((χ h : Rˣ) : R) • T.move h i j hh x)
    rw [map_mul,Units.val_mul,T.mul_apply,map_smul,smul_smul]

@[simp] theorem twist_move (T : FiberTransport (R:=R) (G:=G) M) (χ : G →* Rˣ)
    (g : G) (i j : I) (h : g • i = j) (x : M i) :
    (T.twist χ).move g i j h x = (χ g : R) • T.move g i j h x := rfl

end KhanSL2.Factorization.FiberTransport
