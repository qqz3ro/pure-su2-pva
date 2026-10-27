module

public import KhanSL2.BGG.FreeCEEnergy
public import KhanSL2.BGG.FreeCEAugmentation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG.FreeCE

/-- Dilation fixes the scalar enveloping augmentation. -/
theorem augmentation_positiveUEScale (a : PositiveEnveloping) :
    UE.augmentation ℂ positive (positiveUEScale a) = UE.augmentation ℂ positive a := by
  induction a using UE.induction ℂ positive with
  | scalar r => simp
  | generator x =>
    simp only [positiveUEScale, UniversalEnvelopingAlgebra.lift_ι_apply,
      LieHom.comp_apply, UE.augmentation_ι]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, ha, hb]

/-- The exterior scalar coefficient has physical energy zero. -/
theorem scalarCoefficient_energyScale (u : Cochain) :
    scalarCoefficient (PositiveCE.energyScale u) = scalarCoefficient u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single s r =>
    have hr : Finsupp.single s r = r • FiniteExterior.monomial s := by
      simp [FiniteExterior.monomial]
    rw [hr, map_smul, map_smul, map_smul, PositiveCE.energyScale_monomial, map_smul]
    by_cases hs : s = ∅
    · subst s
      simp [scalarCoefficient, FiniteExterior.monomial, PositiveCE.monomialEnergy]
    · simp [scalarCoefficient, FiniteExterior.monomial, hs, Ne.symm hs]

/-- The full free CE augmentation is invariant under total-energy dilation. -/
theorem augmentation_totalEnergyScale (u : Chain) :
    augmentation (totalEnergyScale u) = augmentation u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a u => simp only [totalEnergyScale_tmul, augmentation_tmul,
      augmentation_positiveUEScale, scalarCoefficient_energyScale]

end KhanSL2.BGG.FreeCE
