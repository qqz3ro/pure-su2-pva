module

public import KhanSL2.BGGBridge.Windows
public import KhanSL2.Modules.CoefficientHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

/-! # Coefficient shifts on the actual BGG contraction

The exterior coefficient power sums commute with the current action. Base change
therefore carries them through the actual differential and contraction maps, and
constant coinvariants preserve these identities.
-/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGGBridge
open KhanSL2.BGG KhanSL2.Current

local instance chainAddCommGroup : AddCommGroup (ChainN NB) := inferInstance
local instance chainModule : Module ℂ (ChainN NB) := inferInstance
local instance harmAddCommGroup : AddCommGroup (HarmN NB) := inferInstance
local instance harmModule : Module ℂ (HarmN NB) := inferInstance
local instance chainQuotAddCommGroup : AddCommGroup (ChainN NB ⧸ relC NB) := inferInstance
local instance chainQuotModule : Module ℂ (ChainN NB ⧸ relC NB) := inferInstance
local instance harmQuotAddCommGroup : AddCommGroup (HarmN NB ⧸ relH NB) := inferInstance
local instance harmQuotModule : Module ℂ (HarmN NB ⧸ relH NB) := inferInstance

/-- The coefficient power sum on the CE tensor model. -/
def coefficientChainModelPower (m : ℕ) : Module.End ℂ (ChainN NB) :=
  LinearMap.lTensor PositiveCE.Cochain (Modules.coefficientPower m)

/-- The coefficient power sum on harmonic tensors. -/
def coefficientHarmPower (m : ℕ) : Module.End ℂ (HarmN NB) :=
  LinearMap.lTensor PositiveCE.Harmonic (Modules.coefficientPower m)

@[simp] theorem coefficientChainModelPower_tmul (m : ℕ) (v : PositiveCE.Cochain) (n : NB) :
    coefficientChainModelPower m (v ⊗ₜ[ℂ] n) = v ⊗ₜ[ℂ] Modules.coefficientPower m n := rfl

@[simp] theorem coefficientHarmPower_tmul (m : ℕ) (v : PositiveCE.Harmonic) (n : NB) :
    coefficientHarmPower m (v ⊗ₜ[ℂ] n) = v ⊗ₜ[ℂ] Modules.coefficientPower m n := rfl

/-- The exterior-model change acts on the other tensor factor. -/
theorem J_coefficientChainPower (m : ℕ) (ξ : GenChains) :
    J (Modules.coefficientChainPower m ξ) = coefficientChainModelPower m (J ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul v n => rfl
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The power sum commutes with the positive enveloping algebra action. -/
theorem coefficientPower_ract (m : ℕ) (u : PositiveEnveloping) (n : NB) :
    Modules.coefficientPower m (ract (rightAction NB) u n) =
      ract (rightAction NB) u (Modules.coefficientPower m n) :=
  ract_commute NB (fun y n => Modules.coefficientPower_lie m y n) u n

theorem dH_coefficientHarmPower (m : ℕ) (z : HarmN NB) :
    dH NB (coefficientHarmPower m z) = coefficientHarmPower m (dH NB z) :=
  base_lTensor (rightAction NB) (coefficientPower_ract m) PositiveTransfer.differential z

theorem dC_coefficientChainModelPower (m : ℕ) (z : ChainN NB) :
    dC NB (coefficientChainModelPower m z) = coefficientChainModelPower m (dC NB z) :=
  base_lTensor (rightAction NB) (coefficientPower_ract m) FreeCE.differential z

theorem incl_coefficientHarmPower (m : ℕ) (z : HarmN NB) :
    (cN NB).incl (coefficientHarmPower m z) =
      coefficientChainModelPower m ((cN NB).incl z) :=
  base_lTensor (rightAction NB) (coefficientPower_ract m) PositiveTransfer.contraction.incl z

theorem proj_coefficientChainModelPower (m : ℕ) (z : ChainN NB) :
    (cN NB).proj (coefficientChainModelPower m z) =
      coefficientHarmPower m ((cN NB).proj z) :=
  base_lTensor (rightAction NB) (coefficientPower_ract m) PositiveTransfer.contraction.proj z

/-- Coefficient-only tensor maps preserve the diagonal constant action. -/
theorem coefficient_lTensor_diag {A : Type*} [AddCommGroup A] [Module ℂ A]
    (m : ℕ) (D : Module.End ℂ A) (x : G) (z : A ⊗[ℂ] NB) :
    LinearMap.lTensor A (Modules.coefficientPower m)
        (diag D (LieModule.toEnd ℂ Current NB (constant x)) z) =
      diag D (LieModule.toEnd ℂ Current NB (constant x))
        (LinearMap.lTensor A (Modules.coefficientPower m) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v n =>
    simp only [diag_tmul, map_add, LinearMap.lTensor_tmul]
    exact congrArg (fun t => D v ⊗ₜ[ℂ] Modules.coefficientPower m n + v ⊗ₜ[ℂ] t)
      (Modules.coefficientPower_lie m (constant x) n)
  | add v w hv hw => simp only [map_add, hv, hw]

theorem coefficientHarmPower_actH (m : ℕ) (x : G) (z : HarmN NB) :
    coefficientHarmPower m (actH NB x z) = actH NB x (coefficientHarmPower m z) :=
  coefficient_lTensor_diag m _ x z

theorem coefficientChainModelPower_actC (m : ℕ) (x : G) (z : ChainN NB) :
    coefficientChainModelPower m (actC NB x z) = actC NB x (coefficientChainModelPower m z) :=
  coefficient_lTensor_diag m _ x z

theorem coefficientHarmPower_relH (m : ℕ) :
    relH NB ≤ (relH NB).comap (coefficientHarmPower m) :=
  le_comap_of_commute (actH NB) (actH NB) (coefficientHarmPower m)
    (coefficientHarmPower_actH m)

theorem coefficientChainModelPower_relC (m : ℕ) :
    relC NB ≤ (relC NB).comap (coefficientChainModelPower m) :=
  le_comap_of_commute (actC NB) (actC NB) (coefficientChainModelPower m)
    (coefficientChainModelPower_actC m)

/-- The natural power sum on actual BGG coinvariants. -/
def coefficientBGGPower (m : ℕ) : Module.End ℂ (HarmN NB ⧸ relH NB) :=
  (relH NB).mapQ (relH NB) (coefficientHarmPower m) (coefficientHarmPower_relH m)

/-- The natural power sum on CE-model coinvariants. -/
def coefficientChainQuotPower (m : ℕ) : Module.End ℂ (ChainN NB ⧸ relC NB) :=
  (relC NB).mapQ (relC NB) (coefficientChainModelPower m) (coefficientChainModelPower_relC m)

@[simp] theorem coefficientBGGPower_mk (m : ℕ) (z : HarmN NB) :
    coefficientBGGPower m (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (coefficientHarmPower m z) := rfl

@[simp] theorem coefficientChainQuotPower_mk (m : ℕ) (z : ChainN NB) :
    coefficientChainQuotPower m (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (coefficientChainModelPower m z) := rfl

theorem coefficientBGGPower_dHq (m : ℕ) (z : HarmN NB ⧸ relH NB) :
    dHq NB (coefficientBGGPower m z) = coefficientBGGPower m (dHq NB z) := by
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    change Submodule.Quotient.mk (dH NB (coefficientHarmPower m z)) =
      Submodule.Quotient.mk (coefficientHarmPower m (dH NB z))
    rw [dH_coefficientHarmPower]

theorem coefficientChainQuotPower_dCq (m : ℕ) (z : ChainN NB ⧸ relC NB) :
    dCq NB (coefficientChainQuotPower m z) = coefficientChainQuotPower m (dCq NB z) := by
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    change Submodule.Quotient.mk (dC NB (coefficientChainModelPower m z)) =
      Submodule.Quotient.mk (coefficientChainModelPower m (dC NB z))
    rw [dC_coefficientChainModelPower]

theorem coefficientHarmPower_commute (m n : ℕ) :
    Commute (coefficientHarmPower m) (coefficientHarmPower n) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    exact congrArg (fun t => v ⊗ₜ[ℂ] t)
      (LinearMap.congr_fun (Modules.coefficientPower_commute m n).eq w)
  | add v w hv hw => simp only [Module.End.mul_apply, map_add, hv, hw]

theorem coefficientBGGPower_commute (m n : ℕ) :
    Commute (coefficientBGGPower m) (coefficientBGGPower n) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    change Submodule.Quotient.mk (coefficientHarmPower m (coefficientHarmPower n z)) =
      Submodule.Quotient.mk (coefficientHarmPower n (coefficientHarmPower m z))
    exact congrArg (fun t => (Submodule.Quotient.mk t : HarmN NB ⧸ relH NB))
      (LinearMap.congr_fun (coefficientHarmPower_commute m n).eq z)

theorem Jq_coefficientRelPower (m : ℕ) (z : RelChains) :
    Jq (Modules.coefficientRelPower m z) = coefficientChainQuotPower m (Jq z) := by
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    change Submodule.Quotient.mk (J (Modules.coefficientChainPower m z)) =
      Submodule.Quotient.mk (coefficientChainModelPower m (J z))
    rw [J_coefficientChainPower]

theorem qincl_coefficientBGGPower (m : ℕ) (z : HarmN NB ⧸ relH NB) :
    (qcN NB).incl (coefficientBGGPower m z) =
      coefficientChainQuotPower m ((qcN NB).incl z) := by
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    change Submodule.Quotient.mk ((cN NB).incl (coefficientHarmPower m z)) =
      Submodule.Quotient.mk (coefficientChainModelPower m ((cN NB).incl z))
    rw [incl_coefficientHarmPower]

theorem qproj_coefficientChainQuotPower (m : ℕ) (z : ChainN NB ⧸ relC NB) :
    (qcN NB).proj (coefficientChainQuotPower m z) =
      coefficientBGGPower m ((qcN NB).proj z) := by
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    change Submodule.Quotient.mk ((cN NB).proj (coefficientChainModelPower m z)) =
      Submodule.Quotient.mk (coefficientHarmPower m ((cN NB).proj z))
    rw [proj_coefficientChainModelPower]

end KhanSL2.BGGBridge
