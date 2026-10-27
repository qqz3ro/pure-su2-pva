module

public import KhanSL2.BGG.FreeCE
public import KhanSL2.BGG.PositiveEnergyScale

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Total physical-energy dilation commutes with the actual free CE differential. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.FreeCE

/-- Simultaneous dilation of the enveloping coefficient and the exterior modes. -/
def totalEnergyScale : Module.End ℂ Chain :=
  TensorProduct.map positiveUEScale.toLinearMap PositiveCE.energyScale

@[simp] theorem totalEnergyScale_tmul (a : PositiveEnveloping) (u : Cochain) :
    totalEnergyScale (a ⊗ₜ[ℂ] u) = positiveUEScale a ⊗ₜ[ℂ] PositiveCE.energyScale u := rfl

@[simp] theorem positiveUEScale_ueGenerator (m : Mode) :
    positiveUEScale (ueGenerator m) = (2 : ℂ) ^ (m.index + 1) • ueGenerator m := by
  have h := positiveUEScale_generator (m.index, MatrixSL2.color m.color)
  rw [show positiveEnergy (m.index, MatrixSL2.color m.color) =
    ((m.index + 1 : ℕ) : ℤ) by simp [positiveEnergy], zpow_natCast] at h
  exact h

/-- Each coefficient-action summand moves energy from the exterior factor into U(n). -/
theorem totalEnergyScale_actionTerm (m : Mode) (u : Chain) :
    totalEnergyScale (actionTerm m u) = actionTerm m (totalEnergyScale u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a u =>
    simp only [actionTerm_tmul, totalEnergyScale_tmul, map_mul, positiveUEScale_ueGenerator,
      mul_smul_comm]
    rw [TensorProduct.smul_tmul, PositiveCE.energyScale_contract]

theorem totalEnergyScale_finiteAction (S : Finset Mode) (u : Chain) :
    totalEnergyScale (finiteAction S u) = finiteAction S (totalEnergyScale u) := by
  simp only [finiteAction, LinearMap.sum_apply, map_sum, totalEnergyScale_actionTerm]

/-- The actual finitely supported action boundary preserves total physical energy. -/
theorem totalEnergyScale_action (u : Chain) :
    totalEnergyScale (action u) = action (totalEnergyScale u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a u =>
    let S := FiniteExterior.supportModes u ∪ FiniteExterior.supportModes (PositiveCE.energyScale u)
    rw [← finiteAction_tmul_eq S a u Finset.subset_union_left,
      totalEnergyScale_finiteAction, totalEnergyScale_tmul,
      finiteAction_tmul_eq S _ _ Finset.subset_union_right]

theorem totalEnergyScale_bracket (u : Chain) :
    totalEnergyScale (bracket u) = bracket (totalEnergyScale u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a u => simp only [bracket_tmul, totalEnergyScale_tmul, PositiveCE.energyScale_boundary]

/-- Total energy is an actual symmetry of the standard free CE complex. -/
theorem totalEnergyScale_differential (u : Chain) :
    totalEnergyScale (differential u) = differential (totalEnergyScale u) := by
  simp only [differential, LinearMap.add_apply, map_add,
    totalEnergyScale_action, totalEnergyScale_bracket]

end KhanSL2.BGG.FreeCE
