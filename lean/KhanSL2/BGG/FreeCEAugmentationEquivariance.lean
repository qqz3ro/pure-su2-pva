module

public import KhanSL2.BGG.FreeCEEquivariance
public import KhanSL2.BGG.FreeCEAugmentation

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The specified augmentation is invariant under the actual constant-sl₂ action. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG
attribute [local instance 100] LieRing.ofAssociativeRing

/-- A derivation induced from the positive Lie algebra preserves its augmentation ideal. -/
@[simp] theorem augmentation_positiveUEAction (x : G) (u : PositiveEnveloping) :
    UE.augmentation ℂ positive (positiveUEAction x u) = 0 := by
  induction u using UE.induction ℂ positive with
  | scalar r =>
    rw [positiveUEAction_apply, Algebra.algebraMap_eq_smul_one, map_smul,
      TauCeti.derivationLieAlgebra.apply_one_eq_zero, smul_zero, map_zero]
  | generator y =>
    rw [positiveUEAction_apply]
    change UE.augmentation ℂ positive
      ((TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation ℂ positive
        (positiveConstantDerivation x) : Module.End ℂ PositiveEnveloping)
        (UniversalEnvelopingAlgebra.ι ℂ y)) = 0
    rw [TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_ι, UE.augmentation_ι]
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]
  | mul u v hu hv =>
    rw [positiveUEAction_mul, map_add, map_mul, map_mul, hu, hv, zero_mul, mul_zero, add_zero]

namespace FreeCE
open PositiveCE FiniteExterior

@[simp] theorem scalarCoefficient_colorAction (a : Fin 3) (ω : Cochain) :
    scalarCoefficient (PositiveCE.colorAction a ω) = 0 := by
  have h := colorAction_pairing a ω 1
  rw [PositiveCE.colorAction_one, map_zero, neg_zero] at h
  simpa only [show (1 : Cochain) = monomial ∅ from rfl,
    coefficientPairing_monomial_right, scalarCoefficient, Finsupp.lapply_apply] using h

@[simp] theorem scalarCoefficient_positiveAction (x : G) (ω : Cochain) :
    scalarCoefficient (ColorRoot.positiveAction x ω) = 0 := by
  rw [← MatrixSL2.color_decomposition x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    ColorRoot.positiveAction_color, scalarCoefficient_colorAction, smul_zero, Finset.sum_const_zero]

/-- The specified scalar augmentation is invariant under all constant matrices. -/
@[simp] theorem augmentation_constantAction (x : G) (u : Chain) :
    augmentation (constantAction x u) = 0 := by
  induction u using TensorProduct.inductionOn with
  | tmul v ω =>
    simp only [constantAction_tmul, map_add, augmentation_tmul, augmentation_positiveUEAction,
      scalarCoefficient_positiveAction, zero_mul, mul_zero, add_zero]
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]

end FreeCE
end KhanSL2.BGG
