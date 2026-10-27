module

public import KhanSL2.BGG.FreeCEEnergy
public import KhanSL2.BGG.PositiveTransfer
public import KhanSL2.BGG.PerturbationEquivariance

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG.PositiveTransfer

/-- Total physical-energy dilation on the actual harmonic free module. -/
def totalEnergyScale : Module.End ℂ HarmonicChain :=
  TensorProduct.map positiveUEScale.toLinearMap PositiveCE.harmonicEnergyScale

@[simp] theorem totalEnergyScale_tmul (a : PositiveEnveloping) (u : PositiveCE.Harmonic) :
    totalEnergyScale (a ⊗ₜ[ℂ] u) = positiveUEScale a ⊗ₜ[ℂ] PositiveCE.harmonicEnergyScale u := rfl

theorem totalEnergyScale_baseIncl (u : HarmonicChain) :
    FreeCE.totalEnergyScale (baseContraction.incl u) = baseContraction.incl (totalEnergyScale u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a u => simp only [baseContraction_incl_tmul, totalEnergyScale_tmul,
      FreeCE.totalEnergyScale_tmul, PositiveCE.harmonicEnergyScale_coe]

theorem totalEnergyScale_baseProj (u : Chain) :
    totalEnergyScale (baseContraction.proj u) = baseContraction.proj (FreeCE.totalEnergyScale u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a u => simp only [baseContraction_proj_tmul, totalEnergyScale_tmul,
      FreeCE.totalEnergyScale_tmul, PositiveCE.harmonicEnergyScale_projection]

theorem totalEnergyScale_baseHomotopy (u : Chain) :
    FreeCE.totalEnergyScale (baseContraction.homotopy u) =
      baseContraction.homotopy (FreeCE.totalEnergyScale u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a u => simp only [baseContraction_homotopy_tmul,
      FreeCE.totalEnergyScale_tmul, PositiveCE.energyScale_homotopy]

/-- Every term of the finite perturbation series preserves total physical energy. -/
theorem totalEnergyScale_series (u : Chain) :
    FreeCE.totalEnergyScale (series u) = series (FreeCE.totalEnergyScale u) :=
  Perturbation.series_commute baseContraction FreeCE.action FreeCE.totalEnergyScale.toAddMonoidHom
    totalEnergyScale_baseHomotopy FreeCE.totalEnergyScale_action isUnit_one_add_action_homotopy u

/-- The actual transferred differential preserves total physical energy. -/
theorem totalEnergyScale_differential (u : HarmonicChain) :
    totalEnergyScale (differential u) = differential (totalEnergyScale u) := by
  exact Perturbation.differential_commute baseContraction FreeCE.action
    FreeCE.totalEnergyScale.toAddMonoidHom totalEnergyScale.toAddMonoidHom
    totalEnergyScale_baseIncl totalEnergyScale_baseProj totalEnergyScale_baseHomotopy
    (by intro x; simp) FreeCE.totalEnergyScale_action isUnit_one_add_action_homotopy u

/-- The actual perturbed inclusion preserves total energy. -/
theorem totalEnergyScale_incl (u : HarmonicChain) :
    FreeCE.totalEnergyScale (contraction.incl u) = contraction.incl (totalEnergyScale u) :=
  Perturbation.inclusion_commute baseContraction FreeCE.action
    FreeCE.totalEnergyScale.toAddMonoidHom totalEnergyScale.toAddMonoidHom
    totalEnergyScale_baseIncl totalEnergyScale_baseHomotopy FreeCE.totalEnergyScale_action
    perturbation_square_compat isUnit_one_add_action_homotopy u

/-- The actual perturbed projection preserves total energy. -/
theorem totalEnergyScale_proj (u : Chain) :
    totalEnergyScale (contraction.proj u) = contraction.proj (FreeCE.totalEnergyScale u) :=
  Perturbation.projection_commute baseContraction FreeCE.action
    FreeCE.totalEnergyScale.toAddMonoidHom totalEnergyScale.toAddMonoidHom
    totalEnergyScale_baseProj totalEnergyScale_baseHomotopy FreeCE.totalEnergyScale_action
    perturbation_square_compat isUnit_one_add_action_homotopy u

end KhanSL2.BGG.PositiveTransfer
