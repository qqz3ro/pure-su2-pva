module

public import KhanSL2.CEDerivationBasics
public import KhanSL2.ExteriorRing

@[expose] public section

/-! The concrete CE multiplication is the finite exterior algebra product. -/

noncomputable section

namespace KhanSL2

instance : FiniteExterior.GeneratorOrder Mode where
  code := Mode.code
  code_injective := Mode.code_injective

theorem wedge_eq_generic (u v : Cochain) :
    wedge u v = FiniteExterior.wedge Mode.code u v := rfl

theorem cochain_mul_eq_wedge (u v : Cochain) : u * v = wedge u v := rfl

theorem cochain_one_eq : (1 : Cochain) = cochainOne := rfl

theorem wedge_assoc (u v w : Cochain) :
    wedge (wedge u v) w = wedge u (wedge v w) :=
  FiniteExterior.wedge_assoc Mode.code u v w

theorem cochainOne_wedge (u : Cochain) : wedge cochainOne u = u :=
  FiniteExterior.wedge_one_left Mode.code u

theorem wedge_cochainOne (u : Cochain) : wedge u cochainOne = u :=
  FiniteExterior.wedge_one_right Mode.code u

theorem monomialWedge_supercomm (s t : ExteriorMonomial) :
    monomialWedge s t =
      (-1 : ℂ) ^ (s.card * t.card) • monomialWedge t s :=
  FiniteExterior.monomialWedge_supercomm Mode.code Mode.code_injective s t

def cochainParity : Cochain →ₐ[ℂ] Cochain := FiniteExterior.parity

theorem cochainParity_apply (u : Cochain) :
    cochainParity u = FiniteExterior.parityLinear u := rfl

@[simp] theorem cochainParity_generator (m : Mode) :
    cochainParity (generator m) = -generator m :=
  FiniteExterior.parity_generator m

@[simp] theorem cochainParity_involutive (u : Cochain) :
    cochainParity (cochainParity u) = u :=
  FiniteExterior.parity_involutive u

theorem cochain_induction {P : Cochain → Prop}
    (hzero : P 0) (hone : P cochainOne)
    (hadd : ∀u v, P u → P v → P (u + v))
    (hsmul : ∀(r : ℂ) u, P u → P (r • u))
    (hgen : ∀a u, P u → P (wedge (generator a) u))
    (u : Cochain) : P u :=
  FiniteExterior.induction_on Mode.code hzero hone hadd hsmul hgen u

end KhanSL2
