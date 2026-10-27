module

public import KhanSL2.Macdonald.StrongBridgePairing
public import KhanSL2.Macdonald.RestrictedCohomology
public import KhanSL2.StrongMacdonald.Invariants
public import KhanSL2.Factorization.RelativeChainsAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Imported constant invariants are exactly the restricted functionals that
annihilate the actual relative CE relations. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Macdonald

@[simp] theorem currentLower_zero (a : Fin 3) :
    currentLower 0 a = currentAction (BGG.mode 0 (MatrixSL2.color a)) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨n,b⟩
  rw [currentLower_X, currentAction_mode_X]
  simp

def tensorColorAction (a : Fin 3) : Module.End ℂ W :=
  tensorPolynomialDerivation (currentAction (BGG.mode 0 (MatrixSL2.color a))) +
    TensorProduct.map LinearMap.id (BGG.PositiveCE.colorAction a)

@[simp] theorem tensorColorAction_tmul (a : Fin 3) (p : Poly) (ω : Exterior) :
    tensorColorAction a (p ⊗ₜ[ℂ] ω) =
      currentAction (BGG.mode 0 (MatrixSL2.color a)) p ⊗ₜ[ℂ] ω +
        p ⊗ₜ[ℂ] BGG.PositiveCE.colorAction a ω := rfl

theorem tensorColorAction_mul (a : Fin 3) (u v : W) :
    tensorColorAction a (u*v) = tensorColorAction a u * v + u * tensorColorAction a v := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul p ω =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q η =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorColorAction_tmul,
        currentAction_mul, BGG.PositiveCE.colorAction_mul, TensorProduct.tmul_add,
        TensorProduct.add_tmul, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul]
      abel
    | add v w hv hw => simp only [mul_add, map_add, hv, hw, add_mul]; abel
  | add u w hu hw => simp only [add_mul, map_add, hu, hw, mul_add]; abel

def strongColorAction (a : Fin 3) : Module.End ℂ StrongMacdonald.W :=
  strongModel.symm.toLinearMap.comp ((tensorColorAction a).comp strongModel.toLinearMap)

@[simp] theorem strongModel_colorAction (a : Fin 3) (u : StrongMacdonald.W) :
    strongModel (strongColorAction a u) = tensorColorAction a (strongModel u) := by
  simp [strongColorAction]

theorem strongColorAction_isDer (a : Fin 3) : StrongMacdonald.IsDer 0 (strongColorAction a) := by
  intro u v
  apply strongModel.injective
  simpa only [strongModel_colorAction, strongModel_mul, map_add,
    Function.iterate_zero, id_eq] using tensorColorAction_mul a (strongModel u) (strongModel v)

theorem strongY_eq (a : Fin 3) : StrongMacdonald.Y a = strongColorAction a := by
  apply (StrongMacdonald.homDer_Y a).isDer.ext (strongColorAction_isDer a)
  intro g
  apply strongModel.injective
  cases g with
  | s g =>
    obtain ⟨n,b⟩ := g
    change strongModel (StrongMacdonald.Y a (StrongMacdonald.sigOf n b)) =
      strongModel (strongColorAction a (StrongMacdonald.sigOf n b))
    rw [StrongMacdonald.Y_sigOf, strongModel_colorAction]
    simp only [map_sum, map_smul, strongModel_sigOf, sigma, tensorColorAction_tmul,
      currentAction_mode_X, Nat.add_zero, Nat.zero_add, BGG.PositiveCE.colorAction_one,
      TensorProduct.tmul_zero, add_zero, TensorProduct.sum_tmul, TensorProduct.smul_tmul']
  | p g =>
    change strongModel (StrongMacdonald.Y a (StrongMacdonald.psiOf g.index g.color)) =
      strongModel (strongColorAction a (StrongMacdonald.psiOf g.index g.color))
    rw [StrongMacdonald.Y_psiOf, strongModel_colorAction]
    simp only [map_sum, map_smul, strongModel_psiOf, psi, tensorColorAction_tmul,
      Derivation.map_one_eq_zero, TensorProduct.zero_tmul, zero_add,
      BGG.PositiveCE.colorAction_generator, TensorProduct.tmul_sum, TensorProduct.tmul_smul]

theorem strongModel_Y (a : Fin 3) (u : StrongMacdonald.W) :
    strongModel (StrongMacdonald.Y a u) = tensorColorAction a (strongModel u) := by
  rw [strongY_eq, strongModel_colorAction]

/-- The raw relative-chain action transported to the mixed coordinates. -/
theorem chainModel_actC_color (a : Fin 3) (z : Factorization.RawChains SymmetricCoefficients) :
    chainModel (BGGBridge.actC SymmetricCoefficients (MatrixSL2.color a) z) =
      tensorColorAction a (chainModel z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul ω p =>
    rw [BGGBridge.actC, BGGBridge.diag_tmul]
    simp only [map_add, chainModel_tmul, BGG.ColorRoot.positiveAction_color,
      tensorColorAction_tmul, symmetricCoefficients_lie]
    rw [add_comm]
    rfl

theorem tensorColorAction_pairing (a : Fin 3) (u v : W) :
    pairing (tensorColorAction a u) v = -pairing u (tensorColorAction a v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw, neg_add]
  | tmul p ω =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v w hv hw => simp only [map_add, hv, hw, neg_add]
    | tmul q η =>
      simp only [tensorColorAction_tmul, map_add, LinearMap.add_apply, pairing_tmul,
        currentAction_pairing, currentLower_zero, BGG.PositiveCE.colorAction_pairing]
      ring

/-- Imported invariance and actual relative CE invariance coincide. -/
theorem strongModel_mem_relativeCochains (u : StrongMacdonald.W) :
    strongModel u ∈ relativeCochains ↔ u ∈ StrongMacdonald.inv := by
  rw [mem_relativeCochains, StrongMacdonald.mem_inv]
  constructor
  · intro hu a
    apply strongModel.injective
    rw [map_zero, strongModel_Y]
    apply pairing_nondegenerate
    intro v
    obtain ⟨z,rfl⟩ := chainModel.surjective v
    rw [tensorColorAction_pairing, ← chainModel_actC_color]
    have hmem : BGGBridge.actC SymmetricCoefficients (MatrixSL2.color a) z ∈
        BGGBridge.relC SymmetricCoefficients :=
      Submodule.mem_iSup_of_mem (MatrixSL2.color a) ⟨z,rfl⟩
    rw [hu _ hmem, neg_zero]
  · intro hu
    have hcol (a : Fin 3) (z : Factorization.RawChains SymmetricCoefficients) :
        chainPairing (strongModel u) (BGGBridge.actC SymmetricCoefficients (MatrixSL2.color a) z) = 0 := by
      change pairing (strongModel u) (chainModel (BGGBridge.actC SymmetricCoefficients (MatrixSL2.color a) z)) = 0
      rw [chainModel_actC_color]
      have h := tensorColorAction_pairing a (strongModel u) (chainModel z)
      rw [← strongModel_Y, hu a, map_zero, map_zero, LinearMap.zero_apply] at h
      exact neg_eq_zero.mp h.symm
    show BGGBridge.relC SymmetricCoefficients ≤ LinearMap.ker (chainPairing (strongModel u))
    apply iSup_le
    rintro x _ ⟨z,rfl⟩
    rw [LinearMap.mem_ker, Factorization.CEModel.actC_sum]
    simp only [map_sum, map_smul, hcol, smul_zero, Finset.sum_const_zero]

/-- The coordinate equivalence is a concrete equivalence of relative cochains. -/
def strongRelativeEquiv : StrongMacdonald.inv ≃ₗ[ℂ] relativeCochains :=
  strongModel.submoduleMap StrongMacdonald.inv |>.trans
    (LinearEquiv.ofEq _ _ (by
      ext v
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨u,hu,rfl⟩; exact (strongModel_mem_relativeCochains u).mpr hu
      · intro hv
        exact ⟨strongModel.symm v, (strongModel_mem_relativeCochains _).mp (by simpa using hv),
          strongModel.apply_symm_apply v⟩))

/-- The imported and actual differentials agree, not only their dimensions. -/
theorem strongModel_dbar (u : StrongMacdonald.W) :
    strongModel (StrongMacdonald.dbar u) = differential (strongModel u) := by
  apply sub_eq_zero.mp
  apply pairing_nondegenerate
  intro v
  rw [map_sub, LinearMap.sub_apply, strongDbar_chainBoundary_pairing, differential_pairing,
    sub_self]

end KhanSL2.Macdonald
