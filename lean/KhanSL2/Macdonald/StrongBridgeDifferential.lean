module

public import KhanSL2.Macdonald.StrongBridgeDerivations
public import KhanSL2.StrongMacdonald.HermLap

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Decomposition of the proved Macdonald differential into the actual exterior
CE differential and the locally finite coadjoint coefficient term. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Macdonald

def tensorExteriorDifferential : Module.End ℂ W :=
  TensorProduct.map LinearMap.id BGG.PositiveCE.d

@[simp] theorem tensorExteriorDifferential_tmul (p : Poly) (ω : Exterior) :
    tensorExteriorDifferential (p ⊗ₜ[ℂ] ω) = p ⊗ₜ[ℂ] BGG.PositiveCE.d ω := rfl

theorem tensorExteriorDifferential_mul (u v : W) :
    tensorExteriorDifferential (u*v) = tensorExteriorDifferential u * v +
      TensorProduct.map LinearMap.id FiniteExterior.parityLinear u * tensorExteriorDifferential v := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul p ω =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q η =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorExteriorDifferential_tmul,
        BGG.PositiveCE.d_mul, TensorProduct.tmul_add, TensorProduct.map_tmul, LinearMap.id_apply]
    | add v w hv hw => simp only [mul_add, map_add, hv, hw, add_mul]; abel
  | add u w hu hw => simp only [add_mul, map_add, hu, hw, mul_add]; abel

def strongExteriorDifferential : Module.End ℂ StrongMacdonald.W :=
  strongModel.symm.toLinearMap.comp (tensorExteriorDifferential.comp strongModel.toLinearMap)

@[simp] theorem strongModel_exteriorDifferential (u : StrongMacdonald.W) :
    strongModel (strongExteriorDifferential u) = tensorExteriorDifferential (strongModel u) := by
  simp [strongExteriorDifferential]

theorem strongExteriorDifferential_isDer : StrongMacdonald.IsDer 1 strongExteriorDifferential := by
  intro u v
  apply strongModel.injective
  simpa only [strongModel_exteriorDifferential, strongModel_mul, map_add,
    Function.iterate_one, strongModel_parity] using
    tensorExteriorDifferential_mul (strongModel u) (strongModel v)

/-- The coefficient part of the coboundary, by positive physical mode. -/
def strongCoefficientDifferentialFamily (i : ℕ) : Module.End ℂ StrongMacdonald.W :=
  ∑ a : Fin 3, StrongMacdonald.lmul (StrongMacdonald.psiOf i a) * StrongMacdonald.Rlow a (i+1)

theorem strongCoefficientDifferentialFamily_kills : StrongMacdonald.Kills strongCoefficientDifferentialFamily :=
  StrongMacdonald.Kills.sum Finset.univ fun a _ =>
    (StrongMacdonald.kills_Rlow a).mul_left fun i => StrongMacdonald.lmul (StrongMacdonald.psiOf i a)

def strongCoefficientDifferential : Module.End ℂ StrongMacdonald.W :=
  StrongMacdonald.lsum strongCoefficientDifferentialFamily strongCoefficientDifferentialFamily_kills.evZero

theorem strongCoefficientDifferential_isDer : StrongMacdonald.IsDer 1 strongCoefficientDifferential :=
  StrongMacdonald.IsDer.lsum _ fun i =>
    StrongMacdonald.IsDer.sum _ _ fun a _ =>
      StrongMacdonald.isDer_lmul_psi_mul (StrongMacdonald.homDer_Rlow a (i+1)) _

/-- The imported differential decomposes into exactly the two CE terms. -/
theorem strongDbar_decomposition :
    StrongMacdonald.dbar = strongCoefficientDifferential + strongExteriorDifferential := by
  apply StrongMacdonald.homDer_dbar.isDer.ext
    (strongCoefficientDifferential_isDer.add strongExteriorDifferential_isDer)
  intro g
  cases g with
  | s g =>
    obtain ⟨k,b⟩ := g
    change StrongMacdonald.dbar (StrongMacdonald.sigOf k b) =
      (strongCoefficientDifferential + strongExteriorDifferential) (StrongMacdonald.sigOf k b)
    have he : strongExteriorDifferential (StrongMacdonald.sigOf k b) = 0 := by
      apply strongModel.injective
      simp only [strongModel_exteriorDifferential, strongModel_sigOf, sigma,
        tensorExteriorDifferential_tmul, BGG.PositiveCE.d_one, TensorProduct.tmul_zero, map_zero]
    rw [LinearMap.add_apply, he, add_zero, strongCoefficientDifferential,
      StrongMacdonald.lsum_apply_of_bound _ k (fun i hi => by
        simp [strongCoefficientDifferentialFamily, show ¬(i+1 ≤ k) by omega])]
    simp only [StrongMacdonald.dbar_sigOf, strongCoefficientDifferentialFamily,
      LinearMap.sum_apply, Module.End.mul_apply, StrongMacdonald.lmul_apply,
      StrongMacdonald.Rlow_sigOf]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a _ => ?_
    rw [if_pos (by have := Finset.mem_range.mp hi; omega), Finset.mul_sum,
      show k-(i+1) = k-1-i by omega]
    simp only [mul_smul_comm]
  | p m =>
    change StrongMacdonald.dbar (StrongMacdonald.psi m) =
      (strongCoefficientDifferential + strongExteriorDifferential) (StrongMacdonald.psi m)
    have hc : strongCoefficientDifferential (StrongMacdonald.psi m) = 0 := by
      rw [strongCoefficientDifferential, StrongMacdonald.lsum_apply_of_bound _ 0 (fun i hi => by
        change strongCoefficientDifferentialFamily i (StrongMacdonald.psiOf m.index m.color) = 0
        simp [strongCoefficientDifferentialFamily])]
      simp
    rw [LinearMap.add_apply, hc, zero_add]
    apply strongModel.injective
    rw [StrongMacdonald.psi_eq, strongDbar_ofExt, strongModel_ofExt,
      strongModel_exteriorDifferential, strongModel_ofExt, tensorExteriorDifferential_tmul]

end KhanSL2.Macdonald
