module

public import KhanSL2.SymmetricFamily.ExteriorLabelled
public import KhanSL2.SymmetricFamily.FiniteProjective

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! Exterior current coefficients over the original raising power-sum action.
The normalized alternating section is proved coefficient-linear and split. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Conditional
open scoped KhanSL2.Conditional

/-- The original raising operators commute on each exterior degree. -/
theorem exteriorPowerCoefficient_commute (m n k : ℕ) :
    Commute (exteriorDeriv k (Modules.coefficientShift m))
      (exteriorDeriv k (Modules.coefficientShift n)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (Modules.coefficientPower_commute m n).eq x.val

/-- Evaluate coefficient coordinates at the actual exterior coefficient derivations. -/
def exteriorCoefficientAction (k : ℕ) :
    CoefficientRing k →ₐ[ℂ] Module.End ℂ (⋀[ℂ]^k BGG.Current) :=
  (Modules.commutingPolynomialEval
    (fun i : Fin k => exteriorDeriv k (Modules.coefficientShift (i.val+1)))
    (fun i j => exteriorPowerCoefficient_commute (i.val+1) (j.val+1) k)).comp
      (coefficientCoordinates k).symm.toAlgHom

instance exteriorPowerCoefficientModule (k : ℕ) :
    Module (CoefficientRing k) (⋀[ℂ]^k BGG.Current) :=
  Module.compHom (⋀[ℂ]^k BGG.Current) (exteriorCoefficientAction k).toRingHom

theorem exteriorCoefficientCoordinates_smul (k : ℕ) (i : Fin k)
    (x : ⋀[ℂ]^k BGG.Current) :
    coefficientCoordinates k (MvPolynomial.X i) • x =
      exteriorDeriv k (Modules.coefficientShift (i.val+1)) x := by
  change (Modules.commutingPolynomialEval
    (fun j : Fin k => exteriorDeriv k (Modules.coefficientShift (j.val+1)))
    (fun j l => exteriorPowerCoefficient_commute (j.val+1) (l.val+1) k))
      ((coefficientCoordinates k).symm (coefficientCoordinates k (MvPolynomial.X i))) x = _
  rw [AlgEquiv.symm_apply_apply]
  exact LinearMap.congr_fun (Modules.commutingPolynomialEval_X _ _ i) x

instance exteriorPowerCoefficientSMulCommClass (k : ℕ) :
    SMulCommClass ℂ (CoefficientRing k) (⋀[ℂ]^k BGG.Current) where
  smul_comm c r x := (map_smul (exteriorCoefficientAction k r) c x).symm

instance exteriorPowerCoefficientIsScalarTower (k : ℕ) :
    IsScalarTower ℂ (CoefficientRing k) (⋀[ℂ]^k BGG.Current) where
  smul_assoc c r x :=
    LinearMap.congr_fun ((exteriorCoefficientAction k).toLinearMap.map_smul c r) x

/-- The canonical normalized exterior section is linear for the fixed coefficient action. -/
theorem exteriorToTensor_smul (k : ℕ) (r : CoefficientRing k)
    (x : ⋀[ℂ]^k BGG.Current) :
    exteriorToTensor BGG.Current k (r • x) = r • exteriorToTensor BGG.Current k x := by
  apply Modules.polynomialCoordinates_intertwines
    (M := ⋀[ℂ]^k BGG.Current) (V := ⨂[ℂ]^k BGG.Current) (coefficientCoordinates k)
    (exteriorToTensor BGG.Current k) _ r x
  intro i y
  rw [exteriorCoefficientCoordinates_smul, tensorCoefficientCoordinates_smul]
  exact LinearMap.congr_fun (exteriorToTensor_exteriorDeriv k
    (Modules.coefficientShift (i.val+1))) y

/-- The actual exterior quotient is linear for the same fixed coefficient action. -/
theorem tensorToExterior_smul (k : ℕ) (r : CoefficientRing k)
    (x : ⨂[ℂ]^k BGG.Current) :
    tensorToExterior BGG.Current k (r • x) = r • tensorToExterior BGG.Current k x := by
  apply Modules.polynomialCoordinates_intertwines (coefficientCoordinates k)
    (tensorToExterior BGG.Current k) _ r x
  intro i y
  rw [exteriorCoefficientCoordinates_smul, tensorCoefficientCoordinates_smul]
  exact LinearMap.congr_fun (tensorToExterior_tensorDeriv k
    (Modules.coefficientShift (i.val+1))) y

/-- The signed labelled-root comparison respects the original coefficient scalars. -/
theorem exteriorLabelledEquiv_smul (k : ℕ) (r : CoefficientRing k)
    (x : ⋀[ℂ]^k BGG.Current) :
    (exteriorLabelledEquiv k (r • x)).val = r • (exteriorLabelledEquiv k x).val := by
  change rootTensorEquiv k (exteriorToTensor BGG.Current k (r • x)) = _
  rw [exteriorToTensor_smul, rootTensorEquiv_smul]
  rfl

def exteriorToTensorLinear (k : ℕ) :
    (⋀[ℂ]^k BGG.Current) →ₗ[CoefficientRing k] (⨂[ℂ]^k BGG.Current) where
  __ := (exteriorToTensor BGG.Current k).toAddHom
  map_smul' := exteriorToTensor_smul k

def tensorToExteriorLinear (k : ℕ) :
    (⨂[ℂ]^k BGG.Current) →ₗ[CoefficientRing k] (⋀[ℂ]^k BGG.Current) where
  __ := (tensorToExterior BGG.Current k).toAddHom
  map_smul' := tensorToExterior_smul k

theorem tensorToExteriorLinear_exteriorToTensorLinear (k : ℕ) :
    (tensorToExteriorLinear k).comp (exteriorToTensorLinear k) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (tensorToExterior_exteriorToTensor BGG.Current k) x

/-- Actual exterior coefficient powers are projective over their prescribed coefficient ring. -/
theorem exteriorPower_projective (k : ℕ) :
    Module.Projective (CoefficientRing k) (⋀[ℂ]^k BGG.Current) := by
  let := currentTensor_free k
  exact Module.Projective.of_split (exteriorToTensorLinear k) (tensorToExteriorLinear k)
    (tensorToExteriorLinear_exteriorToTensorLinear k)

/-- Actual exterior coefficient powers are finite over their prescribed coefficient ring. -/
theorem exteriorPower_finite (k : ℕ) :
    Module.Finite (CoefficientRing k) (⋀[ℂ]^k BGG.Current) := by
  let := currentTensor_finite k
  apply Module.Finite.of_surjective (tensorToExteriorLinear k)
  intro x
  exact ⟨exteriorToTensorLinear k x,
    LinearMap.congr_fun (tensorToExteriorLinear_exteriorToTensorLinear k) x⟩

end KhanSL2.SymmetricFamily
