module

public import KhanSL2.SymmetricFamily.ExteriorChartCoproduct
public import KhanSL2.SymmetricFamily.FactorCurrent

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The canonical exterior coefficient coproduct commutes with the original
current action, via the literal slot derivations and alternating quotient. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

section Generic
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Actual slot derivations split into the two original block derivations. -/
theorem tensorSlotsBlockEquiv_deriv (r s : ℕ) (D : Module.End ℂ M) (x : ⨂[ℂ]^(r+s) M) :
    tensorSlotsBlockEquiv M r s (tensorDeriv (r+s) D x) =
      TensorProduct.map (tensorDeriv r D) LinearMap.id (tensorSlotsBlockEquiv M r s x) +
        TensorProduct.map LinearMap.id (tensorDeriv s D) (tensorSlotsBlockEquiv M r s x) := by
  have he : (tensorSlotsBlockEquiv M r s).toLinearMap.comp (tensorDeriv (r+s) D) =
      ((TensorProduct.map (tensorDeriv r D) LinearMap.id +
        TensorProduct.map LinearMap.id (tensorDeriv s D)).comp
          (tensorSlotsBlockEquiv M r s).toLinearMap) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,
      tensorDeriv_tprod,map_sum,tensorSlotsBlockEquiv_tprod,LinearMap.add_apply,
      TensorProduct.map_tmul,LinearMap.id_apply,TensorProduct.sum_tmul,TensorProduct.tmul_sum]
    rw [Fin.sum_univ_add]
    apply congrArg₂ (fun u w => u+w)
    · apply Finset.sum_congr rfl
      intro i _
      rw [Function.update_comp_eq_of_injective v (Fin.castAdd_injective r s)]
      rw [Function.update_comp_eq_of_forall_ne v _ (by
        intro j h
        have hh := congrArg Fin.val h
        change r+j.val=i.val at hh
        omega)]
      rfl
    · apply Finset.sum_congr rfl
      intro i _
      rw [Function.update_comp_eq_of_injective v (Fin.natAdd_injective s r)]
      rw [Function.update_comp_eq_of_forall_ne v _ (by
        intro j h
        have hh := congrArg Fin.val h
        change j.val=r+i.val at hh
        omega)]
      rfl
  exact LinearMap.congr_fun he x

/-- Taking the exterior quotients of the two blocks preserves their actual derivations. -/
theorem tensorToExterior_diagonal (r s : ℕ) (D : Module.End ℂ M)
    (z : (⨂[ℂ]^r M) ⊗[ℂ] (⨂[ℂ]^s M)) :
    TensorProduct.map (tensorToExterior M r) (tensorToExterior M s)
      (TensorProduct.map (tensorDeriv r D) LinearMap.id z +
        TensorProduct.map LinearMap.id (tensorDeriv s D) z) =
      TensorProduct.map (exteriorDeriv r D) LinearMap.id
        (TensorProduct.map (tensorToExterior M r) (tensorToExterior M s) z) +
      TensorProduct.map LinearMap.id (exteriorDeriv s D)
        (TensorProduct.map (tensorToExterior M r) (tensorToExterior M s) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add] at *; rw [add_add_add_comm]; rw [hz,hw]; abel
  | tmul u v =>
    simp only [TensorProduct.map_tmul,LinearMap.id_apply,map_add]
    rw [show tensorToExterior M r (tensorDeriv r D u) = exteriorDeriv r D (tensorToExterior M r u) from
      LinearMap.congr_fun (tensorToExterior_tensorDeriv r D) u,
      show tensorToExterior M s (tensorDeriv s D v) = exteriorDeriv s D (tensorToExterior M s v) from
        LinearMap.congr_fun (tensorToExterior_tensorDeriv s D) v]

/-- The actual normalized alternating block intertwines the original induced derivations. -/
theorem exteriorTensorBlock_deriv (r s : ℕ) (D : Module.End ℂ M) (p : ⋀[ℂ]^(r+s) M) :
    exteriorTensorBlock M r s (exteriorDeriv (r+s) D p) =
      TensorProduct.map (exteriorDeriv r D) LinearMap.id (exteriorTensorBlock M r s p) +
        TensorProduct.map LinearMap.id (exteriorDeriv s D) (exteriorTensorBlock M r s p) := by
  change TensorProduct.map (tensorToExterior M r) (tensorToExterior M s)
    (tensorSlotsBlockEquiv M r s (exteriorToTensor M (r+s) (exteriorDeriv (r+s) D p))) = _
  rw [show exteriorToTensor M (r+s) (exteriorDeriv (r+s) D p) =
    tensorDeriv (r+s) D (exteriorToTensor M (r+s) p) from
      LinearMap.congr_fun (exteriorToTensor_exteriorDeriv (r+s) D) p,
    tensorSlotsBlockEquiv_deriv,tensorToExterior_diagonal]
  rfl

end Generic

/-- The diagonal tensor current action uses the same original exterior derivations. -/
theorem exteriorTensor_lie (r s : ℕ) (x : BGG.Current)
    (z : (⋀[ℂ]^r BGG.Current) ⊗[ℂ] (⋀[ℂ]^s BGG.Current)) :
    ⁅x,z⁆ = TensorProduct.map (exteriorDeriv r (LieAlgebra.ad ℂ BGG.Current x)) LinearMap.id z +
      TensorProduct.map LinearMap.id (exteriorDeriv s (LieAlgebra.ad ℂ BGG.Current x)) z := rfl

/-- The original normalized alternating block is a genuine current-module homomorphism. -/
def exteriorTensorBlockLieHom (r s : ℕ) :
    (⋀[ℂ]^(r+s) BGG.Current) →ₗ⁅ℂ,BGG.Current⁆
      (⋀[ℂ]^r BGG.Current) ⊗[ℂ] (⋀[ℂ]^s BGG.Current) where
  toLinearMap := exteriorTensorBlock BGG.Current r s
  map_lie' {x p} := by
    change exteriorTensorBlock BGG.Current r s ⁅x,p⁆ = ⁅x,exteriorTensorBlock BGG.Current r s p⁆
    exact (exteriorTensorBlock_deriv (M:=BGG.Current) r s (LieAlgebra.ad ℂ BGG.Current x) p).trans
      (exteriorTensor_lie r s x _).symm

/-- The unnormalized canonical alternating coproduct is also an actual current map. -/
def exteriorPowerCoproductLieHom (r s : ℕ) :
    (⋀[ℂ]^(r+s) BGG.Current) →ₗ⁅ℂ,BGG.Current⁆
      (⋀[ℂ]^r BGG.Current) ⊗[ℂ] (⋀[ℂ]^s BGG.Current) where
  toLinearMap := exteriorPowerCoproductComponent BGG.Current r s
  map_lie' {x p} := by
    change exteriorPowerCoproductComponent BGG.Current r s ⁅x,p⁆ =
      ⁅x,exteriorPowerCoproductComponent BGG.Current r s p⁆
    rw [exteriorPowerCoproductComponent_tensorBlock,exteriorPowerCoproductComponent_tensorBlock]
    exact (congrArg (fun z : (⋀[ℂ]^r BGG.Current) ⊗[ℂ] (⋀[ℂ]^s BGG.Current) =>
      (Nat.choose (r+s) r : ℂ) • z) ((exteriorTensorBlockLieHom r s).map_lie x p)).trans
      (lie_smul (Nat.choose (r+s) r : ℂ) x (exteriorTensorBlock BGG.Current r s p)).symm

end KhanSL2.SymmetricFamily
