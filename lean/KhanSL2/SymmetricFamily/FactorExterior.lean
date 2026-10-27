module

public import KhanSL2.SymmetricFamily.FactorRootScalars
public import KhanSL2.SymmetricFamily.ExteriorBaseChangedLabelled
public import KhanSL2.SymmetricFamily.SignedRepresentation

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The original exterior coefficient family specialized along one prescribed
factor polynomial, and its normalized actual root/color invariant realization. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Macdonald
open scoped FactorRootScalars

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The actual exterior coefficient specialization along the factor coefficients. -/
def FactorExterior (n : ℕ) (f : Polynomial A) : Type :=
  letI := factorCoefficientAlgebra n f
  CoefficientBaseChange (Depth.RB n) (⋀[ℂ]^n BGG.Current) A

instance (n : ℕ) (f : Polynomial A) : AddCommGroup (FactorExterior n f) := by
  unfold FactorExterior
  infer_instance
instance (n : ℕ) (f : Polynomial A) : Module A (FactorExterior n f) := by
  unfold FactorExterior
  infer_instance
instance (n : ℕ) (f : Polynomial A) : Module ℂ (FactorExterior n f) := by
  unfold FactorExterior
  letI := factorCoefficientAlgebra n f
  letI : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  infer_instance
instance (n : ℕ) (f : Polynomial A) : IsScalarTower ℂ A (FactorExterior n f) := by
  unfold FactorExterior
  let := factorCoefficientAlgebra n f
  let : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  infer_instance
instance (n : ℕ) (f : Polynomial A) : LieRingModule BGG.Current (FactorExterior n f) := by
  unfold FactorExterior
  infer_instance
instance (n : ℕ) (f : Polynomial A) : LieModule ℂ BGG.Current (FactorExterior n f) := by
  unfold FactorExterior
  let := factorCoefficientAlgebra n f
  let : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  infer_instance

/-- The inverse-slot factor action with its actual exterior sign. -/
def factorSignedLabelledPermute (n : ℕ) (f : Polynomial A) (σ : Equiv.Perm (Fin n)) :
    Module.End A (FactorColors n f) := (σ.sign:A) • factorLabelledPermute n f σ

/-- The original alternating section realizes exterior factor coefficients as signed invariants. -/
def factorExteriorRootEquiv (n : ℕ) (f : Polynomial A) :
    FactorExterior n f ≃ₗ[A] fixedOperators (factorSignedLabelledPermute n f) := by
  letI := factorCoefficientAlgebra n f
  letI : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  exact exteriorBaseChangedLabelledEquiv n A

/-- The honest signed simultaneous factor group action. -/
def factorSignedLabelledRepresentation (n : ℕ) (f : Polynomial A) :
    Equiv.Perm (Fin n) →* Module.End A (FactorColors n f) :=
  scalarTwistRepresentation (permutationSign n A) (factorLabelledRepresentation n f)

theorem factorSignedLabelledRepresentation_inverse (n : ℕ) (f : Polynomial A)
    (σ : Equiv.Perm (Fin n)) :
    factorSignedLabelledRepresentation n f σ.symm = factorSignedLabelledPermute n f σ := by
  change (permutationSign n A σ.symm : A) • factorLabelledRepresentation n f σ.symm = _
  rw [permutationSign_val,factorLabelledRepresentation_eq,Equiv.symm_symm]
  rw [Equiv.Perm.sign_symm]
  rfl

/-- Original exterior factor coefficients equal the actual signed fixed module. -/
def factorExteriorFixedEquiv (n : ℕ) (f : Polynomial A) :
    FactorExterior n f ≃ₗ[A]
      Factorization.FiberTransport.fixedVectors (fun σ => factorSignedLabelledRepresentation n f σ) :=
  (factorExteriorRootEquiv n f).trans
    (fixedReindexEquiv (factorSignedLabelledPermute n f)
      (fun σ => factorSignedLabelledRepresentation n f σ) (Equiv.inv _)
      (factorSignedLabelledRepresentation_inverse n f))

end KhanSL2.SymmetricFamily