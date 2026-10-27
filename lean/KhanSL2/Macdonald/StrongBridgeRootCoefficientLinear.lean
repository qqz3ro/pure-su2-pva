module

public import KhanSL2.Macdonald.StrongBridgeFixedSignedRoots
public import KhanSL2.Factorization.CoefficientTotalScalars

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual Macdonald homology equivalence is linear over the original
coefficient ring, proved from its genuine power-sum action. -/
noncomputable section
open scoped DirectSum
namespace KhanSL2.Macdonald
open Factorization SymmetricFamily Conditional

instance (priority := 2000) symmetricPowerHomologySMul (s : ℕ) :
    SMul (CoefficientRing s) (TotalHomology (symmetricPower s)) where
  smul a u := coefficientTotalHomologyMap
    (coefficientScalarLieHom (CoefficientRing s) (symmetricPower s) a) u

instance (priority := 2000) symmetricPowerHomologyCoefficientModule (s : ℕ) :
    Module (CoefficientRing s) (TotalHomology (symmetricPower s)) :=
  coefficientTotalHomologyModule (CoefficientRing s) (symmetricPower s)

instance symmetricPowerHomologySMulCommClass (s : ℕ) :
    SMulCommClass ℂ (CoefficientRing s) (TotalHomology (symmetricPower s)) :=
  coefficientTotalHomologySMulCommClass (CoefficientRing s) (symmetricPower s)

instance symmetricPowerHomologyIsScalarTower (s : ℕ) :
    IsScalarTower ℂ (CoefficientRing s) (TotalHomology (symmetricPower s)) :=
  coefficientTotalHomologyIsScalarTower (CoefficientRing s) (symmetricPower s)

/-- The coefficient generators still act by the originally defined raising maps. -/
theorem symmetricPowerHomology_coefficientCoordinates_smul (s : ℕ) (i : Fin s)
    (u : TotalHomology (symmetricPower s)) :
    coefficientCoordinates s (MvPolynomial.X i) • u =
      symmetricPowerHomologyShift (i.val+1) s u := by
  have hs : coefficientScalarLieHom (CoefficientRing s) (symmetricPower s)
      (coefficientCoordinates s (MvPolynomial.X i)) = symmetricPowerCoefficientEnd (i.val+1) s := by
    apply LieModuleHom.ext
    intro p
    exact symmetricCoefficientCoordinates_smul s i p
  change coefficientTotalHomologyMap
    (coefficientScalarLieHom (CoefficientRing s) (symmetricPower s)
      (coefficientCoordinates s (MvPolynomial.X i))) u = _
  rw [hs]
  rfl

/-- The specified fixed homology equivalence in actual weighted polynomial modules. -/
def symmetricPowerSignedRootEquiv (s : ℕ) : TotalHomology (symmetricPower s) ≃ₗ[ℂ]
    ⨁ d : RootHomologyDegrees s, FixedSignedRootModel s d :=
  (symmetricPowerRootEquiv s).trans (fixedSignedRootEquiv s)

theorem symmetricPowerSignedRootEquiv_coefficientCoordinates (s : ℕ) (i : Fin s)
    (u : TotalHomology (symmetricPower s)) :
    symmetricPowerSignedRootEquiv s (coefficientCoordinates s (MvPolynomial.X i) • u) =
      coefficientCoordinates s (MvPolynomial.X i) • symmetricPowerSignedRootEquiv s u := by
  rw [symmetricPowerHomology_coefficientCoordinates_smul]
  change fixedSignedRootEquiv s
    (symmetricPowerRootEquiv s (symmetricPowerHomologyShift (i.val+1) s u)) = _
  rw [symmetricPowerRootEquiv_shift,fixedSignedRootEquiv_powerSum]
  rfl

/-- All coefficient scalars are retained, by the proved independent power-sum coordinates. -/
theorem symmetricPowerSignedRootEquiv_smul (s : ℕ) (a : CoefficientRing s)
    (u : TotalHomology (symmetricPower s)) :
    symmetricPowerSignedRootEquiv s (a • u) = a • symmetricPowerSignedRootEquiv s u :=
  Modules.polynomialCoordinates_intertwines (coefficientCoordinates s)
    (symmetricPowerSignedRootEquiv s).toLinearMap
      (symmetricPowerSignedRootEquiv_coefficientCoordinates s) a u

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency true in
/-- Actual relative homology with symmetric coefficients, as a module over its
original coefficient ring, in the explicit weighted root-polynomial model. -/
def symmetricPowerRootLinearEquiv (s : ℕ) :
    TotalHomology (symmetricPower s) ≃ₗ[CoefficientRing s]
      ⨁ d : RootHomologyDegrees s, FixedSignedRootModel s d where
  __ := (symmetricPowerSignedRootEquiv s).toEquiv
  map_add' := (symmetricPowerSignedRootEquiv s).map_add
  map_smul' := symmetricPowerSignedRootEquiv_smul s

end KhanSL2.Macdonald
