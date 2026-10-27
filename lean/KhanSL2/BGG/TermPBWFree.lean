module

public import KhanSL2.BGG.TermPBWGrading

@[expose] public section

/-! The induced BGG term is genuinely free over the positive-current enveloping algebra. -/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGG

/-- Restriction of the actual current-enveloping action to positive currents. -/
instance termPositiveModule (p : ℕ) : Module PositiveEnveloping (Term p) :=
  Module.compHom (Term p) positiveFactor.toRingHom

@[simp] theorem positive_smul_term (p : ℕ) (u : PositiveEnveloping) (q : Term p) :
    u • q = positiveFactor u • q := rfl

instance termPositiveScalarTower (p : ℕ) : IsScalarTower ℂ PositiveEnveloping (Term p) where
  smul_assoc r u q := by
    change positiveFactor (r • u) • q = r • (positiveFactor u • q)
    rw [map_smul, smul_assoc]

/-- The relative PBW equivalence bundled over the positive enveloping algebra. -/
def positiveTensorModuleEquivTerm (p : ℕ) :
    PositiveEnveloping ⊗[ℂ] Coefficient p ≃ₗ[PositiveEnveloping] Term p where
  toAddEquiv := (positiveTensorEquivTerm p).toAddEquiv
  map_smul' u t := positiveTensorEquivTerm_smul p u t

@[simp] theorem positiveTensorModuleEquivTerm_apply (p : ℕ)
    (t : PositiveEnveloping ⊗[ℂ] Coefficient p) :
    positiveTensorModuleEquivTerm p t = positiveTensorEquivTerm p t := rfl

/-- A free positive-enveloping basis consists precisely of the standard coefficient generators. -/
def termPositiveBasis (p : ℕ) :
    Module.Basis (Fin (2 * p + 1)) PositiveEnveloping (Term p) :=
  ((TauCeti.Sl2Std.basis ℂ (2 * p)).baseChange PositiveEnveloping).map
    (positiveTensorModuleEquivTerm p)

@[simp] theorem termPositiveBasis_apply (p : ℕ) (i : Fin (2 * p + 1)) :
    termPositiveBasis p i = termGenerator p (TauCeti.Sl2Std.basis ℂ (2 * p) i) := by
  simp only [termPositiveBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    positiveTensorModuleEquivTerm_apply, positiveTensorEquivTerm_one_tmul]

instance termFreePositive (p : ℕ) : Module.Free PositiveEnveloping (Term p) :=
  Module.Free.of_basis (termPositiveBasis p)

/-- All free generators occur at the prescribed BGG energy. -/
theorem termPositiveBasis_mem (p : ℕ) (i : Fin (2 * p + 1)) :
    termPositiveBasis p i ∈ termPiece p (generatorEnergy p) := by
  rw [termPositiveBasis_apply]
  exact termGenerator_mem p _

end KhanSL2.BGG
