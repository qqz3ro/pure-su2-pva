module

public import KhanSL2.BGG.FirstMaps
public import KhanSL2.BGG.RelativeProjectivity
public import TauCeti.Algebra.Lie.Sl2.Standard

@[expose] public section

/-! The coefficient representations and underlying induced modules in all BGG degrees.
The energy shifts are recorded separately; compatibility with the enveloping-algebra
energy grading is a further theorem, not a property assumed by these definitions. -/

noncomputable section

namespace KhanSL2.BGG

/-- The irreducible constant-sl₂ representation of highest weight `2p`. -/
abbrev Coefficient (p : ℕ) := TauCeti.Sl2Std ℂ (2 * p)

/-- Its actual matrix-sl₂ action. -/
def coefficientAction (p : ℕ) (x : G) : Coefficient p →ₗ[ℂ] Coefficient p :=
  LieModule.toEnd ℂ G (Coefficient p) x

@[simp] theorem coefficientAction_apply (p : ℕ) (x : G) (v : Coefficient p) :
    coefficientAction p x v = ⁅x, v⁆ := rfl

/-- The underlying module `U(sl₂[z]) ⊗_{U(sl₂)} V(2p)`. -/
abbrev Term (p : ℕ) := Induced.Model constGenerator (coefficientAction p)

/-- The coefficient generators of the induced term. -/
def termGenerator (p : ℕ) : Coefficient p →ₗ[ℂ] Term p :=
  Induced.of constGenerator (coefficientAction p)

/-- The prescribed energy of coefficient generators in BGG degree `p`. -/
def generatorEnergy (p : ℕ) : ℕ := p * (p + 1) / 2

@[simp] theorem generatorEnergy_zero : generatorEnergy 0 = 0 := rfl
@[simp] theorem generatorEnergy_one : generatorEnergy 1 = 1 := rfl

theorem coefficient_finrank (p : ℕ) : Module.finrank ℂ (Coefficient p) = 2 * p + 1 :=
  TauCeti.Sl2Std.finrank_eq (K := ℂ) (n := 2 * p)

instance coefficient_irreducible (p : ℕ) : LieModule.IsIrreducible ℂ G (Coefficient p) :=
  TauCeti.Sl2Std.isIrreducible

@[simp] theorem const_smul_termGenerator (p : ℕ) (x : G) (v : Coefficient p) :
    constGenerator x • termGenerator p v = termGenerator p ⁅x, v⁆ :=
  Induced.inc_smul_of constGenerator (coefficientAction p) x v

/-- Every BGG term has the relative lifting property for sequences split over constants. -/
theorem term_relative_projective (p : ℕ)
    {N N' : Type*} [AddCommGroup N] [Module ℂ N] [Module Enveloping N]
    [IsScalarTower ℂ Enveloping N] [AddCommGroup N'] [Module ℂ N']
    [Module Enveloping N'] [IsScalarTower ℂ Enveloping N']
    (π : N →ₗ[Enveloping] N') (s : N' →ₗ[ℂ] N)
    (hs : ∀ n, π (s n) = n)
    (hs_const : ∀ x n, s (constGenerator x • n) = constGenerator x • s n)
    (F : Term p →ₗ[Enveloping] N') :
    ∃ F' : Term p →ₗ[Enveloping] N, π.comp F' = F :=
  Induced.exists_lift_of_equivariant_section constGenerator (coefficientAction p)
    π s hs hs_const F

/-- The chosen highest-weight coefficient generator in degree `p`. -/
def termHighest (p : ℕ) : Term p :=
  termGenerator p (TauCeti.Sl2Std.basis ℂ (2 * p) 0)

theorem const_e_smul_termHighest (p : ℕ) :
    constGenerator (TauCeti.slFinTwoBasis ℂ 0) • termHighest p = 0 := by
  unfold termHighest
  rw [const_smul_termGenerator, TauCeti.Sl2Std.lie_slFinTwoBasis_zero,
    TauCeti.Sl2Std.raise_basis_zero, map_zero]

theorem const_h_smul_termHighest (p : ℕ) :
    constGenerator (TauCeti.slFinTwoBasis ℂ 2) • termHighest p =
      (2 * p : ℂ) • termHighest p := by
  unfold termHighest
  rw [const_smul_termGenerator, TauCeti.Sl2Std.lie_slFinTwoBasis_two,
    TauCeti.Sl2Std.diag_basis, map_smul]
  simp

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] LieRingModule.ofAssociativeModule

instance termLieRingModule (p : ℕ) : LieRingModule Current (Term p) :=
  LieRingModule.compLieHom (Term p) (UniversalEnvelopingAlgebra.ι ℂ)

instance termLieModule (p : ℕ) : LieModule ℂ Current (Term p) := by
  let := LieModule.ofAssociativeModule (R := ℂ) (A := Enveloping) (M := Term p)
  exact LieModule.compLieHom (Term p) (UniversalEnvelopingAlgebra.ι ℂ)

@[simp] theorem term_lie (p : ℕ) (x : Current) (q : Term p) :
    ⁅x, q⁆ = (UniversalEnvelopingAlgebra.ι ℂ x : Enveloping) • q := rfl

end KhanSL2.BGG
