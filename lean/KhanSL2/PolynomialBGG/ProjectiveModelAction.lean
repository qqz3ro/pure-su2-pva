module

public import KhanSL2.PolynomialBGG.ProjectiveModelWindow
public import Mathlib.Algebra.Module.TransferInstance

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-! The fixed-degree coinvariant model carries exactly the already constructed
coefficient-ring action on the actual assembled BGG term. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.PolynomialBGG
open BGG BGGBridge Current Conditional

/-- Transport of the existing coefficient action through the proved model equivalence. -/
instance windowCoinvariantsModule (B p : ℕ) :
    Module (CoefficientRing B) (WindowCoinvariants B p) :=
  (termEquivWindow B p).symm.toAddEquiv.module (CoefficientRing B)

/-- The model equivalence is linear over the existing coefficient ring. -/
def termEquivWindowLinear (B p : ℕ) :
    BGGComplex.Term B p ≃ₗ[CoefficientRing B] WindowCoinvariants B p :=
  ((termEquivWindow B p).symm.toAddEquiv.linearEquiv (CoefficientRing B)).symm

theorem windowInclQ_eq_termToCoinvariants (B p : ℕ) (u : WindowCoinvariants B p) :
    windowInclQ B p u = BGGComplex.termToCoinvariants B p ((termEquivWindow B p).symm u) := by
  have h := windowInclQ_termToWindow B p ((termEquivWindow B p).symm u)
  change windowInclQ B p (termEquivWindow B p ((termEquivWindow B p).symm u)) = _ at h
  rwa [LinearEquiv.apply_symm_apply] at h

theorem windowInclQ_smul (B p : ℕ) (a : CoefficientRing B) (u : WindowCoinvariants B p) :
    windowInclQ B p (a • u) = a • windowInclQ B p u := by
  rw [windowInclQ_eq_termToCoinvariants, windowInclQ_eq_termToCoinvariants]
  have h := (termEquivWindowLinear B p).symm.map_smul a u
  change (termEquivWindow B p).symm (a • u) = a • (termEquivWindow B p).symm u at h
  rw [h, BGGComplex.termToCoinvariants_smul]

instance windowCoinvariantsIsScalarTower (B p : ℕ) :
    IsScalarTower ℂ (CoefficientRing B) (WindowCoinvariants B p) where
  smul_assoc c a u := by
    apply windowInclQ_injective B p
    simp only [windowInclQ_smul, map_smul, smul_assoc]

instance windowCoinvariantsSMulCommClass (B p : ℕ) :
    SMulCommClass ℂ (CoefficientRing B) (WindowCoinvariants B p) where
  smul_comm c a u := by
    apply windowInclQ_injective B p
    simp only [windowInclQ_smul, map_smul, smul_comm c a]

/-- The fixed-degree model embeds coefficient-linearly in the actual global quotient. -/
def windowInclQLinear (B p : ℕ) :
    WindowCoinvariants B p →ₗ[CoefficientRing B] (HarmN NB ⧸ relH NB) where
  __ := (windowInclQ B p).toAddHom
  map_smul' := windowInclQ_smul B p

/-- The actual coefficient power-sum operation before imposing constant relations. -/
def windowPower (m B p : ℕ) : Module.End ℂ (WindowModel B p) :=
  LinearMap.lTensor (TauCeti.Sl2Std ℂ (2*p)) (exteriorDeriv B (Modules.coefficientShift m))

theorem windowIncl_power (m B p : ℕ) (u : WindowModel B p) :
    windowIncl B p (windowPower m B p u) = coefficientHarmPower m (windowIncl B p u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul v ν => rfl

theorem windowPower_commute (m n B p : ℕ) : Commute (windowPower m B p) (windowPower n B p) := by
  apply LinearMap.ext
  intro u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [Module.End.mul_apply, map_add, hu, hv]
  | tmul v ν =>
    change v ⊗ₜ[ℂ] exteriorDeriv B (Modules.coefficientShift m)
        (exteriorDeriv B (Modules.coefficientShift n) ν) =
      v ⊗ₜ[ℂ] exteriorDeriv B (Modules.coefficientShift n)
        (exteriorDeriv B (Modules.coefficientShift m) ν)
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun (Modules.coefficientPower_commute m n).eq ν

/-- Independent power sums act by the already specified mode-shift derivations. -/
def windowCoefficientAction (B p : ℕ) : CoefficientRing B →ₐ[ℂ] Module.End ℂ (WindowModel B p) :=
  (Modules.commutingPolynomialEval (fun i : Fin B => windowPower (i.val+1) B p)
    (fun i j => windowPower_commute (i.val+1) (j.val+1) B p)).comp
      (coefficientCoordinates B).symm.toAlgHom

instance windowModelModule (B p : ℕ) : Module (CoefficientRing B) (WindowModel B p) :=
  Module.compHom (WindowModel B p) (windowCoefficientAction B p).toRingHom

theorem windowCoordinates_smul (B p : ℕ) (i : Fin B) (u : WindowModel B p) :
    coefficientCoordinates B (MvPolynomial.X i) • u = windowPower (i.val+1) B p u := by
  change (Modules.commutingPolynomialEval
    (fun j : Fin B => windowPower (j.val+1) B p)
    (fun j k => windowPower_commute (j.val+1) (k.val+1) B p))
    ((coefficientCoordinates B).symm (coefficientCoordinates B (MvPolynomial.X i))) u = _
  rw [AlgEquiv.symm_apply_apply]
  exact LinearMap.congr_fun (Modules.commutingPolynomialEval_X _ _ i) u

instance windowModelIsScalarTower (B p : ℕ) :
    IsScalarTower ℂ (CoefficientRing B) (WindowModel B p) where
  smul_assoc c a u :=
    LinearMap.congr_fun ((windowCoefficientAction B p).toLinearMap.map_smul c a) u

instance windowModelSMulCommClass (B p : ℕ) :
    SMulCommClass ℂ (CoefficientRing B) (WindowModel B p) where
  smul_comm c a u := (map_smul (windowCoefficientAction B p a) c u).symm

/-- The actual quotient map is linear for the coefficient action on both sides. -/
theorem windowMkQ_smul (B p : ℕ) (a : CoefficientRing B) (u : WindowModel B p) :
    (windowRelations B p).mkQ (a • u) = a • (windowRelations B p).mkQ u := by
  apply Modules.polynomialCoordinates_intertwines (coefficientCoordinates B)
    (windowRelations B p).mkQ _ a u
  intro i v
  apply windowInclQ_injective B p
  rw [windowCoordinates_smul, windowInclQ_smul, globalCoefficientCoordinates_smul]
  change (relH NB).mkQ (windowIncl B p (windowPower (i.val+1) B p v)) =
    coefficientBGGPower (i.val+1) ((relH NB).mkQ (windowIncl B p v))
  rw [windowIncl_power]
  rfl

/-- The model quotient, bundled over the genuine coefficient ring. -/
def windowMkQLinear (B p : ℕ) : WindowModel B p →ₗ[CoefficientRing B] WindowCoinvariants B p where
  __ := (windowRelations B p).mkQ.toAddHom
  map_smul' := windowMkQ_smul B p

end KhanSL2.PolynomialBGG
