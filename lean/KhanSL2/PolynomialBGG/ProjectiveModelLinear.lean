module

public import KhanSL2.PolynomialBGG.ProjectiveModelAction
public import KhanSL2.PolynomialBGG.ProjectiveModelLabelled
public import KhanSL2.PolynomialBGG.TensorAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

/-! Coefficient-linear alternating retraction and its descent to constant
coinvariants. The coefficient ring is the existing elementary-coordinate R_B. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.PolynomialBGG
open BGG BGGBridge Current Conditional

/-- Constant diagonal action, bundled over the coefficient ring. -/
def labelledActLinear (B p : ℕ) (x : G) :
    Module.End (CoefficientRing B) (LabelledModel B p) where
  __ := (labelledAct B p x).toAddHom
  map_smul' r u := by
    change labelledAct B p x (r • u) = r • labelledAct B p x u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [smul_add, map_add, hu, hv]
    | tmul ν v =>
      simp only [labelledAct, TensorProduct.smul_tmul', diag_tmul,
        TensorProduct.smul_tmul', smul_add]
      rw [tensorConstantLie_smul]

def labelledRelationsLinear (B p : ℕ) : Submodule (CoefficientRing B) (LabelledModel B p) :=
  ⨆ x : G, LinearMap.range (labelledActLinear B p x)

theorem labelledToWindow_smul (B p : ℕ) (a : CoefficientRing B) (u : LabelledModel B p) :
    labelledToWindow B p (a • u) = a • labelledToWindow B p u := by
  apply Modules.polynomialCoordinates_intertwines (coefficientCoordinates B)
    (labelledToWindow B p) _ a u
  intro i v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [smul_add, map_add, hu, hv]
  | tmul ν w =>
    rw [TensorProduct.smul_tmul', tensorCoefficientCoordinates_smul, windowCoordinates_smul]
    change w ⊗ₜ[ℂ] tensorToExterior Cur B (tensorDeriv B (Modules.coefficientShift (i.val+1)) ν) =
      w ⊗ₜ[ℂ] exteriorDeriv B (Modules.coefficientShift (i.val+1)) (tensorToExterior Cur B ν)
    exact congrArg (fun z => w ⊗ₜ[ℂ] z)
      (LinearMap.congr_fun (tensorToExterior_tensorDeriv B (Modules.coefficientShift (i.val+1))) ν)

theorem windowToLabelled_smul (B p : ℕ) (a : CoefficientRing B) (u : WindowModel B p) :
    windowToLabelled B p (a • u) = a • windowToLabelled B p u := by
  apply Modules.polynomialCoordinates_intertwines (coefficientCoordinates B)
    (windowToLabelled B p) _ a u
  intro i v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [smul_add, map_add, hu, hv]
  | tmul w ν =>
    rw [windowCoordinates_smul]
    change exteriorToTensor Cur B (exteriorDeriv B (Modules.coefficientShift (i.val+1)) ν) ⊗ₜ[ℂ] w =
      coefficientCoordinates B (MvPolynomial.X i) • (exteriorToTensor Cur B ν ⊗ₜ[ℂ] w)
    rw [TensorProduct.smul_tmul', tensorCoefficientCoordinates_smul]
    exact congrArg (fun z => z ⊗ₜ[ℂ] w)
      (LinearMap.congr_fun (exteriorToTensor_exteriorDeriv B (Modules.coefficientShift (i.val+1))) ν)

def labelledToWindowLinear (B p : ℕ) :
    LabelledModel B p →ₗ[CoefficientRing B] WindowModel B p where
  __ := (labelledToWindow B p).toAddHom
  map_smul' := labelledToWindow_smul B p

def windowToLabelledLinear (B p : ℕ) :
    WindowModel B p →ₗ[CoefficientRing B] LabelledModel B p where
  __ := (windowToLabelled B p).toAddHom
  map_smul' := windowToLabelled_smul B p

/-- The labelled quotient maps to the actual fixed-degree quotient. -/
def labelledQuotientToWindow (B p : ℕ) :
    (LabelledModel B p ⧸ labelledRelationsLinear B p) →ₗ[CoefficientRing B]
      WindowCoinvariants B p :=
  (labelledRelationsLinear B p).liftQ
    ((windowMkQLinear B p).comp (labelledToWindowLinear B p)) (by
      refine iSup_le fun x => ?_
      rintro _ ⟨u, rfl⟩
      change (windowRelations B p).mkQ (labelledToWindow B p (labelledAct B p x u)) = 0
      rw [labelledToWindow_act, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_iSup_of_mem x ⟨labelledToWindow B p u, rfl⟩)

/-- The alternating section descends to the actual constant coinvariants. -/
def windowToLabelledQuotient (B p : ℕ) : WindowCoinvariants B p →ₗ[ℂ]
    (LabelledModel B p ⧸ labelledRelationsLinear B p) :=
  (windowRelations B p).liftQ
    (((labelledRelationsLinear B p).mkQ.restrictScalars ℂ).comp (windowToLabelled B p)) (by
      refine iSup_le fun x => ?_
      rintro _ ⟨u, rfl⟩
      change (labelledRelationsLinear B p).mkQ (windowToLabelled B p (windowAct B p x u)) = 0
      rw [windowToLabelled_act, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_iSup_of_mem x ⟨windowToLabelled B p u, rfl⟩)

theorem windowToLabelledQuotient_smul (B p : ℕ) (a : CoefficientRing B)
    (u : WindowCoinvariants B p) :
    windowToLabelledQuotient B p (a • u) = a • windowToLabelledQuotient B p u := by
  induction u using Submodule.Quotient.induction_on with
  | _ u =>
    change windowToLabelledQuotient B p (a • (windowRelations B p).mkQ u) = _
    rw [← windowMkQ_smul]
    change (labelledRelationsLinear B p).mkQ (windowToLabelled B p (a • u)) =
      a • (labelledRelationsLinear B p).mkQ (windowToLabelled B p u)
    rw [windowToLabelled_smul, map_smul]

def windowToLabelledQuotientLinear (B p : ℕ) :
    WindowCoinvariants B p →ₗ[CoefficientRing B]
      (LabelledModel B p ⧸ labelledRelationsLinear B p) where
  __ := (windowToLabelledQuotient B p).toAddHom
  map_smul' := windowToLabelledQuotient_smul B p

theorem labelledQuotient_window_section (B p : ℕ) :
    (labelledQuotientToWindow B p).comp (windowToLabelledQuotientLinear B p) = LinearMap.id := by
  apply LinearMap.ext
  intro u
  induction u using Submodule.Quotient.induction_on with
  | _ u =>
    change (windowRelations B p).mkQ (labelledToWindow B p (windowToLabelled B p u)) =
      (windowRelations B p).mkQ u
    rw [labelledToWindow_windowToLabelled]

/-- The only needed input is projectivity of the explicit labelled color quotient.
The conclusion concerns the actual BGG term with its existing coefficient action. -/
theorem bggTerm_projective_of_labelled (B p : ℕ)
    [Module.Projective (CoefficientRing B)
      (LabelledModel B p ⧸ labelledRelationsLinear B p)] :
    Module.Projective (CoefficientRing B) (BGGComplex.Term B p) := by
  have : Module.Projective (CoefficientRing B) (WindowCoinvariants B p) :=
    Module.Projective.of_split (windowToLabelledQuotientLinear B p)
      (labelledQuotientToWindow B p) (labelledQuotient_window_section B p)
  exact Module.Projective.of_equiv' (termEquivWindowLinear B p).symm

end KhanSL2.PolynomialBGG
