module

public import KhanSL2.Factorization.OrbitStabilizer
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KhanSL2.Factorization.FiberTransport

variable {R A G I : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [MulAction G I]

/-- The coherent fibre action induced by actual algebra automorphisms on an
invariant family of ideals. These are the actual quotient algebras. -/
def quotients (ρ : G →* (A ≃ₐ[R] A)) (J : I → Ideal A)
    (hJ : ∀ g i, Ideal.map (ρ g).toRingHom (J i) = J (g • i)) :
    FiberTransport (R:=R) (G:=G) (fun i => A ⧸ J i) where
  move g i j h := (Ideal.quotientEquivAlg (J i) (J j) (ρ g)
    (by
      change J j = Ideal.map (ρ g).toRingHom (J i)
      rw [hJ,h])).toLinearEquiv
  one_apply i x := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (J i) (ρ 1 a) = Ideal.Quotient.mk (J i) a
    rw [map_one]
    rfl
  mul_apply g h i j k hh hg x := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (J k) (ρ (g*h) a) =
      Ideal.Quotient.mk (J k) (ρ g (ρ h a))
    rw [map_mul]
    rfl

@[simp] theorem quotients_move_mk (ρ : G →* (A ≃ₐ[R] A)) (J : I → Ideal A)
    (hJ : ∀ g i, Ideal.map (ρ g).toRingHom (J i) = J (g • i))
    (g : G) (i j : I) (h : g • i = j) (a : A) :
    (quotients ρ J hJ).move g i j h (Ideal.Quotient.mk (J i) a) =
      Ideal.Quotient.mk (J j) (ρ g a) := rfl

end KhanSL2.Factorization.FiberTransport

