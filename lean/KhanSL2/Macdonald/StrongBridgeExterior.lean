module

public import KhanSL2.Macdonald.StrongBridgeGenerators
public import KhanSL2.StrongMacdonald.DbarSquare

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Compatibility of the imported differential with the actual positive-current
CE differential on exterior coefficients. The epsilon sign is checked explicitly. -/
noncomputable section
open scoped BigOperators TensorProduct
namespace KhanSL2.Macdonald

@[simp] theorem strongModel_parity (u : StrongMacdonald.W) :
    strongModel (StrongMacdonald.parity u) =
      TensorProduct.map LinearMap.id FiniteExterior.parityLinear (strongModel u) := by
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single e ω =>
    simp only [StrongMacdonald.parity_single, strongModel_single, TensorProduct.map_tmul,
      LinearMap.id_apply]

@[simp] theorem strongDbar_ofExt_generator (m : Mode) :
    StrongMacdonald.dbar (StrongMacdonald.ofExt (FiniteExterior.generator m)) =
      StrongMacdonald.ofExt (BGG.PositiveCE.d (FiniteExterior.generator m)) := by
  change StrongMacdonald.dbar (StrongMacdonald.psiOf m.index m.color) = _
  rw [StrongMacdonald.dbar_psiOf, BGG.PositiveCE.d_generator]
  simp only [map_smul, map_sum, map_mul, ← StrongMacdonald.psi_eq,
    map_neg, neg_smul, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  rw [epsilon_swap_left a m.color c]
  simp only [neg_smul, smul_neg]
  rfl

/-- The imported coboundary restricts to the already constructed positive CE
coboundary, with the same exterior generators and the same sign. -/
theorem strongDbar_ofExt (ω : Exterior) :
    StrongMacdonald.dbar (StrongMacdonald.ofExt ω) =
      StrongMacdonald.ofExt (BGG.PositiveCE.d ω) := by
  induction ω using FiniteExterior.induction_on BGG.PositiveCE.Mode.code with
  | hzero => simp
  | hone =>
    change StrongMacdonald.dbar (StrongMacdonald.ofExt 1) = StrongMacdonald.ofExt (BGG.PositiveCE.d 1)
    rw [map_one, StrongMacdonald.homDer_dbar.map_one, BGG.PositiveCE.d_one, map_zero]
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsmul r u hu => simp only [map_smul, hu]
  | hgen m u hu =>
    change StrongMacdonald.dbar (StrongMacdonald.ofExt (FiniteExterior.generator m * u)) =
      StrongMacdonald.ofExt (BGG.PositiveCE.d (FiniteExterior.generator m * u))
    rw [map_mul, StrongMacdonald.dbar_mul, strongDbar_ofExt_generator, hu,
      BGG.PositiveCE.d_mul, map_add, map_mul, map_mul]
    simp only [← StrongMacdonald.psi_eq, StrongMacdonald.parity_psi,
      FiniteExterior.parity_generator, map_neg]


end KhanSL2.Macdonald
