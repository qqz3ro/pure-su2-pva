module

public import KhanSL2.Macdonald.CurrentActionShift

@[expose] public section

/-! A separate type for symmetric chain coefficients with the actual current action.
The type wrapper prevents this instance from assigning the chain action to the
restricted cochain coordinates represented by the underlying polynomial ring. -/

noncomputable section
namespace KhanSL2.Macdonald

def SymmetricCoefficients : Type := Poly

instance : CommRing SymmetricCoefficients := inferInstanceAs (CommRing Poly)
instance : Algebra ℂ SymmetricCoefficients := inferInstanceAs (Algebra ℂ Poly)

/-- Forget the chain-coefficient interpretation, retaining the polynomial algebra. -/
def symmetricCoefficientsEquiv : SymmetricCoefficients ≃ₐ[ℂ] Poly := AlgEquiv.refl

instance : LieRingModule BGG.Current SymmetricCoefficients :=
  LieRingModule.compLieHom Poly currentAction

instance : LieModule ℂ BGG.Current SymmetricCoefficients :=
  LieModule.compLieHom Poly currentAction

@[simp] theorem symmetricCoefficients_lie (x : BGG.Current) (p : SymmetricCoefficients) :
    symmetricCoefficientsEquiv ⁅x,p⁆ = currentAction x (symmetricCoefficientsEquiv p) := rfl

/-- The symmetric-algebra universal model, now landing in the actual coefficient module. -/
def symmetricCoefficientsFromSymmetricAlgebra :
    SymmetricAlgebra ℂ BGG.Current ≃ₐ[ℂ] SymmetricCoefficients :=
  symmetricCurrentEquiv.trans symmetricCoefficientsEquiv.symm

/-- Each raising power-sum operator is an actual current-module endomorphism. -/
def symmetricCoefficientEnd (m : ℕ) :
    SymmetricCoefficients →ₗ⁅ℂ,BGG.Current⁆ SymmetricCoefficients where
  toLinearMap := (symmetricCoefficientShift m).toLinearMap
  map_lie' {x p} := symmetricCoefficientShift_currentAction m x p

@[simp] theorem symmetricCoefficientEnd_apply (m : ℕ) (p : SymmetricCoefficients) :
    symmetricCoefficientsEquiv (symmetricCoefficientEnd m p) =
      symmetricCoefficientShift m (symmetricCoefficientsEquiv p) := rfl

end KhanSL2.Macdonald
