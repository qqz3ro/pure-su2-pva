module

public import KhanSL2.BGG.TermPBW
public import TauCeti.Algebra.Lie.UniversalEnveloping.Derivation.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The explicit constant-sl₂ action in relative PBW coordinates. -/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGG

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Left adjoint action of a constant current, as a Lie derivation. -/
def currentConstantDerivation (x : G) : LieDerivation ℂ Current Current :=
  -LieDerivation.inner ℂ Current Current (constant x)

@[simp] theorem currentConstantDerivation_apply (x : G) (u : Current) :
    currentConstantDerivation x u = ⁅constant x, u⁆ := by
  change -⁅u, constant x⁆ = ⁅constant x, u⁆
  exact lie_skew (constant x) u

/-- The adjoint action preserves the actual positive-current ideal. -/
def positiveConstantDerivation (x : G) : LieDerivation ℂ positive positive where
  toFun u := ⟨currentConstantDerivation x u, by
    change evalZero (currentConstantDerivation x u) = 0
    rw [currentConstantDerivation_apply, evalZero.map_lie, evalZero_constant,
      show evalZero (u : Current) = 0 from u.property, lie_zero]⟩
  map_add' u v := Subtype.ext ((currentConstantDerivation x).map_add u v)
  map_smul' r u := Subtype.ext ((currentConstantDerivation x).map_smul r u)
  leibniz' u v := Subtype.ext ((currentConstantDerivation x).leibniz' u v)

@[simp] theorem positiveConstantDerivation_coe (x : G) (u : positive) :
    (positiveConstantDerivation x u : Current) = ⁅constant x, (u : Current)⁆ :=
  currentConstantDerivation_apply x u

/-- The natural extension of constant adjoint action to the positive enveloping algebra. -/
def positiveUEDerivation (x : G) : TauCeti.derivationLieAlgebra ℂ PositiveEnveloping :=
  TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation ℂ positive
    (positiveConstantDerivation x)

private theorem currentConstant_enveloping (x : G) :
    TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation ℂ Current
      (currentConstantDerivation x) = TauCeti.innerDerivation ℂ (constGenerator x) := by
  rw [currentConstantDerivation, ← TauCeti.UniversalEnvelopingAlgebra.envelopingDerivationHom_apply,
    map_neg, TauCeti.UniversalEnvelopingAlgebra.envelopingDerivationHom_apply,
    TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_inner, neg_neg]
  rfl

/-- The natural constant derivation becomes the actual commutator in the ambient algebra. -/
theorem positiveFactor_derivation (x : G) (u : PositiveEnveloping) :
    positiveFactor ((positiveUEDerivation x : Module.End ℂ PositiveEnveloping) u) =
      constGenerator x * positiveFactor u - positiveFactor u * constGenerator x := by
  have h := TauCeti.UniversalEnvelopingAlgebra.map_envelopingDerivation ℂ positive
    positive.toLieSubalgebra.incl (positiveConstantDerivation x) (currentConstantDerivation x)
    (fun _ => rfl) u
  rw [currentConstant_enveloping] at h
  simpa only [positiveFactor, positiveUEDerivation, TauCeti.coe_innerDerivation,
    LieAlgebra.ad_apply, Ring.lie_def] using h

/-- The tensor action is the Leibniz sum of the adjoint and coefficient actions. -/
def positiveTensorConstantAction (p : ℕ) (x : G) :
    Module.End ℂ (PositiveEnveloping ⊗[ℂ] Coefficient p) :=
  TensorProduct.map (positiveUEDerivation x : Module.End ℂ PositiveEnveloping)
    (LinearMap.id : Coefficient p →ₗ[ℂ] Coefficient p) +
  TensorProduct.map (LinearMap.id : PositiveEnveloping →ₗ[ℂ] PositiveEnveloping)
    (coefficientAction p x)

@[simp] theorem positiveTensorConstantAction_tmul (p : ℕ) (x : G)
    (u : PositiveEnveloping) (v : Coefficient p) :
    positiveTensorConstantAction p x (u ⊗ₜ[ℂ] v) =
      ((positiveUEDerivation x : Module.End ℂ PositiveEnveloping) u) ⊗ₜ[ℂ] v +
        u ⊗ₜ[ℂ] coefficientAction p x v := rfl

/-- Relative PBW intertwines the explicit constant-sl₂ action, not merely vector spaces. -/
theorem positiveTensorEquivTerm_constant (p : ℕ) (x : G)
    (t : PositiveEnveloping ⊗[ℂ] Coefficient p) :
    positiveTensorEquivTerm p (positiveTensorConstantAction p x t) =
      ⁅constant x, positiveTensorEquivTerm p t⁆ := by
  induction t using TensorProduct.inductionOn with
  | tmul u v =>
    rw [positiveTensorConstantAction_tmul, map_add, positiveTensorEquivTerm_tmul,
      positiveTensorEquivTerm_tmul, positiveTensorEquivTerm_tmul, term_lie]
    change positiveFactor ((positiveUEDerivation x : Module.End ℂ PositiveEnveloping) u) •
      termGenerator p v + positiveFactor u • termGenerator p (coefficientAction p x v) =
        constGenerator x • (positiveFactor u • termGenerator p v)
    have hb : constGenerator x • termGenerator p v =
        termGenerator p (coefficientAction p x v) :=
      Induced.inc_smul_of constGenerator (coefficientAction p) x v
    rw [← hb, positiveFactor_derivation, sub_smul, mul_smul, mul_smul]
    abel
  | add t s ht hs => simp only [map_add, lie_add, ht, hs]

end KhanSL2.BGG
