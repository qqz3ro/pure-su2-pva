module

public import KhanSL2.SymmetricFamily.LabelledRoots
public import KhanSL2.PolynomialBGG.TensorAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! The symmetric coefficient ring acts on the actual symmetric coefficient
module by its previously defined raising operators. The labelled-root comparison
is proved linear for this action; its action is not imposed by transport. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open Macdonald PolynomialBGG Conditional
open scoped KhanSL2.Conditional

/-- The actual raising operators commute after restriction to symmetric degree. -/
theorem symmetricPowerCoefficientEnd_commute (m n k : ℕ) :
    Commute (symmetricPowerCoefficientEnd m k).toLinearMap
      (symmetricPowerCoefficientEnd n k).toLinearMap := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact LinearMap.congr_fun (symmetricCoefficientShift_commute m n).eq p.val

/-- Evaluate power-sum coordinates at the actual raising coefficient operators. -/
def symmetricPolynomialAction (k : ℕ) :
    MvPolynomial (Fin k) ℂ →ₐ[ℂ] Module.End ℂ (symmetricPower k) :=
  Modules.commutingPolynomialEval
    (fun i : Fin k => (symmetricPowerCoefficientEnd (i.val+1) k).toLinearMap)
    (fun i j => symmetricPowerCoefficientEnd_commute (i.val+1) (j.val+1) k)

/-- The fixed elementary-coordinate coefficient-ring action on symmetric powers. -/
def symmetricCoefficientAction (k : ℕ) :
    CoefficientRing k →ₐ[ℂ] Module.End ℂ (symmetricPower k) :=
  (symmetricPolynomialAction k).comp (coefficientCoordinates k).symm.toAlgHom

instance symmetricPowerCoefficientModule (k : ℕ) : Module (CoefficientRing k) (symmetricPower k) :=
  Module.compHom (symmetricPower k) (symmetricCoefficientAction k).toRingHom

@[simp] theorem symmetricCoefficient_smul_eq (k : ℕ) (r : CoefficientRing k) (p : symmetricPower k) :
    r • p = symmetricCoefficientAction k r p := rfl

/-- Each independent power sum has precisely its previously defined raising action. -/
theorem symmetricCoefficientCoordinates_smul (k : ℕ) (i : Fin k) (p : symmetricPower k) :
    coefficientCoordinates k (MvPolynomial.X i) • p = symmetricPowerCoefficientEnd (i.val+1) k p := by
  change symmetricPolynomialAction k
    ((coefficientCoordinates k).symm (coefficientCoordinates k (MvPolynomial.X i))) p = _
  rw [AlgEquiv.symm_apply_apply]
  exact LinearMap.congr_fun (Modules.commutingPolynomialEval_X _ _ i) p

instance symmetricPowerCoefficientSMulCommClass (k : ℕ) :
    SMulCommClass ℂ (CoefficientRing k) (symmetricPower k) where
  smul_comm c r p := (map_smul (symmetricCoefficientAction k r) c p).symm

instance symmetricPowerCoefficientIsScalarTower (k : ℕ) :
    IsScalarTower ℂ (CoefficientRing k) (symmetricPower k) where
  smul_assoc c r p :=
    LinearMap.congr_fun ((symmetricCoefficientAction k).toLinearMap.map_smul c r) p

/-- Normalized symmetrization is linear for the actual fixed coefficient actions. -/
theorem symmetricToTensor_smul (k : ℕ) (r : CoefficientRing k) (p : symmetricPower k) :
    symmetricToTensor k (r • p) = r • symmetricToTensor k p := by
  exact Modules.polynomialCoordinates_intertwines
    (M := symmetricPower k) (V := ⨂[ℂ]^k BGG.Current)
    (coefficientCoordinates k) (symmetricToTensor k) (fun i q => by
      rw [symmetricCoefficientCoordinates_smul, tensorCoefficientCoordinates_smul]
      exact symmetricToTensor_symmetricDegreeDeriv k (Modules.coefficientShift (i.val+1)) q) r p

/-- Multiplication from labelled tensors is linear for the same fixed coefficient actions. -/
theorem tensorToSymmetric_smul (k : ℕ) (r : CoefficientRing k) (x : ⨂[ℂ]^k BGG.Current) :
    tensorToSymmetric k (r • x) = r • tensorToSymmetric k x := by
  apply Modules.polynomialCoordinates_intertwines (coefficientCoordinates k) (tensorToSymmetric k) _ r x
  intro i y
  rw [symmetricCoefficientCoordinates_smul, tensorCoefficientCoordinates_smul]
  exact tensorToSymmetric_tensorDeriv k (Modules.coefficientShift (i.val+1)) y

/-- The full current action commutes with every coefficient-ring scalar. -/
theorem current_lie_symmetricCoefficient_smul (k : ℕ) (x : BGG.Current)
    (r : CoefficientRing k) (p : symmetricPower k) : ⁅x,r • p⁆ = r • ⁅x,p⁆ := by
  apply Modules.polynomialCoordinates_intertwines (coefficientCoordinates k)
    (LieModule.toEnd ℂ BGG.Current (symmetricPower k) x) _ r p
  intro i q
  simp only [LieModule.toEnd_apply_apply, symmetricCoefficientCoordinates_smul]
  exact ((symmetricPowerCoefficientEnd (i.val+1) k).map_lie x q).symm

/-- The invariant labelled-root identification respects the already constructed ring action. -/
theorem symmetricLabelledEquiv_smul (k : ℕ) (r : CoefficientRing k) (p : symmetricPower k) :
    (symmetricLabelledEquiv k (r • p)).val = r • (symmetricLabelledEquiv k p).val := by
  change rootTensorEquiv k (symmetricToTensor k (r • p)) = _
  rw [symmetricToTensor_smul, rootTensorEquiv_smul]
  rfl

end KhanSL2.SymmetricFamily
