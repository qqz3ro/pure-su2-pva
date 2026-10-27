module

public import KhanSL2.PolynomialBGG.ProjectiveModelWindow

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The normalized alternating section gives a split map from labelled
current tensors onto the fixed-degree BGG model, before and after imposing
constant Lie algebra relations. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.PolynomialBGG
open BGG BGGBridge Current

/-- Labelled current tensors with the finite harmonic coefficient. -/
abbrev LabelledModel (B p : ℕ) := (⨂[ℂ]^B Cur) ⊗[ℂ] TauCeti.Sl2Std ℂ (2*p)

instance labelledModelAddCommGroup (B p : ℕ) : AddCommGroup (LabelledModel B p) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- Wedge the labelled current factors and put the harmonic factor first. -/
def labelledToWindow (B p : ℕ) : LabelledModel B p →ₗ[ℂ] WindowModel B p :=
  (TensorProduct.comm ℂ (⋀[ℂ]^B Cur) (TauCeti.Sl2Std ℂ (2*p))).toLinearMap.comp
    (LinearMap.rTensor (TauCeti.Sl2Std ℂ (2*p)) (tensorToExterior Cur B))

/-- The canonical normalized alternating section, with factors reversed. -/
def windowToLabelled (B p : ℕ) : WindowModel B p →ₗ[ℂ] LabelledModel B p :=
  (LinearMap.rTensor (TauCeti.Sl2Std ℂ (2*p)) (exteriorToTensor Cur B)).comp
    (TensorProduct.comm ℂ (TauCeti.Sl2Std ℂ (2*p)) (⋀[ℂ]^B Cur)).toLinearMap

theorem labelledToWindow_windowToLabelled (B p : ℕ) (u : WindowModel B p) :
    labelledToWindow B p (windowToLabelled B p u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul v ν =>
    change v ⊗ₜ[ℂ] tensorToExterior Cur B (exteriorToTensor Cur B ν) = v ⊗ₜ[ℂ] ν
    rw [show tensorToExterior Cur B (exteriorToTensor Cur B ν) = ν from
      LinearMap.congr_fun (tensorToExterior_exteriorToTensor Cur B) ν]

/-- Diagonal constant action on labelled current tensors. -/
def labelledAct (B p : ℕ) (x : G) : Module.End ℂ (LabelledModel B p) :=
  diag (tensorDeriv B (adCur (constant x)))
    (LieModule.toEnd ℂ G (TauCeti.Sl2Std ℂ (2*p)) x)

theorem labelledToWindow_act (B p : ℕ) (x : G) (u : LabelledModel B p) :
    labelledToWindow B p (labelledAct B p x u) = windowAct B p x (labelledToWindow B p u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul ν v =>
    simp only [labelledAct, windowAct, labelledToWindow, diag_tmul, map_add,
      LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
      TensorProduct.comm_tmul]
    have h := LinearMap.congr_fun (tensorToExterior_tensorDeriv B (adCur (constant x))) ν
    change tensorToExterior Cur B (tensorDeriv B (adCur (constant x)) ν) = _ at h
    rw [h, LinearMap.comp_apply, add_comm]

theorem windowToLabelled_act (B p : ℕ) (x : G) (u : WindowModel B p) :
    windowToLabelled B p (windowAct B p x u) = labelledAct B p x (windowToLabelled B p u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul v ν =>
    simp only [labelledAct, windowAct, windowToLabelled, diag_tmul, map_add,
      LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
      TensorProduct.comm_tmul]
    have h := LinearMap.congr_fun (exteriorToTensor_exteriorDeriv B (adCur (constant x))) ν
    change exteriorToTensor Cur B (exteriorDeriv B (adCur (constant x)) ν) = _ at h
    rw [h, LinearMap.comp_apply, add_comm]

/-- The actual constant action relations on the labelled model. -/
def labelledRelations (B p : ℕ) : Submodule ℂ (LabelledModel B p) :=
  ⨆ x : G, LinearMap.range (labelledAct B p x)

end KhanSL2.PolynomialBGG
