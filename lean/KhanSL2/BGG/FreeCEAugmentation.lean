module

public import KhanSL2.BGG.FreeCE
public import KhanSL2.BGG.PositiveBoundaryAdjoint

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The actual augmentation of the standard free CE module. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.FreeCE

open PositiveCE FiniteExterior

/-- The exterior scalar coefficient. -/
def scalarCoefficient : Cochain →ₗ[ℂ] ℂ := Finsupp.lapply ∅

@[simp] theorem scalarCoefficient_one : scalarCoefficient 1 = 1 := by
  change (monomial (∅ : Finset Mode)) ∅ = 1
  simp [monomial]

@[simp] theorem scalarCoefficient_boundary (ω : Cochain) : scalarCoefficient (boundary ω) = 0 := by
  have h := boundary_pairing ω 1
  rw [d_one, map_zero] at h
  simpa only [show (1 : Cochain) = monomial ∅ from rfl,
    coefficientPairing_monomial_right, scalarCoefficient, Finsupp.lapply_apply] using h

/-- The augmentation uses the actual enveloping augmentation and exterior scalar coefficient. -/
def augmentation : Chain →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (UE.augmentation ℂ positive).toLinearMap scalarCoefficient)

@[simp] theorem augmentation_tmul (u : PositiveEnveloping) (ω : Cochain) :
    augmentation (u ⊗ₜ[ℂ] ω) = UE.augmentation ℂ positive u * scalarCoefficient ω := by
  simp only [augmentation, LinearMap.comp_apply, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, TensorProduct.lid_tmul, smul_eq_mul]

/-- Include the trivial coefficient as the scalar CE chain. -/
def scalarInclusion : ℂ →ₗ[ℂ] Chain := LinearMap.toSpanSingleton ℂ Chain (1 ⊗ₜ[ℂ] 1)

@[simp] theorem augmentation_scalarInclusion (r : ℂ) : augmentation (scalarInclusion r) = r := by
  simp [scalarInclusion, augmentation_tmul]

theorem augmentation_surjective : Function.Surjective augmentation :=
  fun r => ⟨scalarInclusion r, augmentation_scalarInclusion r⟩

@[simp] theorem augmentation_action (t : Chain) : augmentation (action t) = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul u ω =>
    induction ω using Finsupp.induction_linear with
    | zero => simp
    | add ω η hω hη => simp only [TensorProduct.tmul_add, map_add, hω, hη, add_zero]
    | single s r =>
      have hr : Finsupp.single s r = r • monomial s := by simp [monomial]
      rw [hr, TensorProduct.tmul_smul, LinearMap.map_smul_of_tower, map_smul]
      suffices augmentation (action (u ⊗ₜ[ℂ] monomial s)) = 0 by rw [this, smul_zero]
      rw [action_tmul_monomial, map_sum]
      apply Finset.sum_eq_zero
      intro m _
      simp only [augmentation_tmul, map_mul, ueGenerator, UE.augmentation_ι, mul_zero, zero_mul]
  | add t s ht hs => simp only [map_add, ht, hs, add_zero]

@[simp] theorem augmentation_bracket (t : Chain) : augmentation (bracket t) = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul u ω => simp only [bracket_tmul, augmentation_tmul, scalarCoefficient_boundary, mul_zero]
  | add t s ht hs => simp only [map_add, ht, hs, add_zero]

/-- The specified augmentation annihilates the actual full CE boundary. -/
@[simp] theorem augmentation_differential (t : Chain) : augmentation (differential t) = 0 := by
  simp only [differential, LinearMap.add_apply, map_add, augmentation_action,
    augmentation_bracket, add_zero]

@[simp] theorem bracket_square_zero (t : Chain) : bracket (bracket t) = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul u ω => simp only [bracket_tmul, boundary_square_zero, TensorProduct.tmul_zero]
  | add t s ht hs => simp only [map_add, ht, hs, add_zero]

end KhanSL2.BGG.FreeCE
