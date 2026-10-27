module

public import KhanSL2.BGG.FreeCEAugmentation

@[expose] public section

/-! The free CE augmentation as a genuine enveloping-module morphism. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG.FreeCE

/-- The trivial positive-current action on the scalar coefficient is the actual augmentation action. -/
instance scalarPositiveModule : Module PositiveEnveloping ℂ :=
  Module.compHom ℂ (UE.augmentation ℂ positive).toRingHom

@[simp] theorem scalar_positive_smul (u : PositiveEnveloping) (r : ℂ) :
    u • r = UE.augmentation ℂ positive u * r := rfl

theorem augmentation_smul (u : PositiveEnveloping) (t : Chain) :
    augmentation (u • t) = u • augmentation t := by
  induction t using TensorProduct.inductionOn with
  | tmul v ω =>
    rw [TensorProduct.smul_tmul', augmentation_tmul, augmentation_tmul, scalar_positive_smul]
    change UE.augmentation ℂ positive (u * v) * scalarCoefficient ω = _
    rw [map_mul, mul_assoc]
  | add t s ht hs => simp only [smul_add, map_add, ht, hs]

/-- The specified augmentation is linear for the actual enveloping-algebra actions. -/
def augmentationModule : Chain →ₗ[PositiveEnveloping] ℂ where
  toFun := augmentation
  map_add' := augmentation.map_add
  map_smul' := augmentation_smul

@[simp] theorem augmentationModule_apply (t : Chain) : augmentationModule t = augmentation t := rfl

theorem augmentationModule_surjective : Function.Surjective augmentationModule := augmentation_surjective

@[simp] theorem augmentationModule_differential (t : Chain) :
    augmentationModule (differential t) = 0 := augmentation_differential t

end KhanSL2.BGG.FreeCE
