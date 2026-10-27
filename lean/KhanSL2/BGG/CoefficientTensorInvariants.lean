module

public import KhanSL2.BGG.CoefficientDual
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.LinearAlgebra.Contraction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG

variable (p : ℕ) (M : Type*) [AddCommGroup M] [Module ℂ M]

/-- The tensor-Hom equivalence obtained from the proved self-duality of V(2p).
Only the coefficient representation is finite dimensional; M is arbitrary. -/
def coefficientTensorHomLinearEquiv :
    M ⊗[ℂ] Coefficient p ≃ₗ[ℂ] (Coefficient p →ₗ[ℂ] M) :=
  (TensorProduct.comm ℂ M (Coefficient p)).trans
    ((TensorProduct.congr (coefficientDualEquiv p).toLinearEquiv
      (LinearEquiv.refl ℂ M)).trans
        (dualTensorHomEquivOfBasis (N := M) (TauCeti.Sl2Std.basis ℂ (2*p))))

@[simp] theorem coefficientTensorHomLinearEquiv_tmul_apply
    (m : M) (v w : Coefficient p) :
    coefficientTensorHomLinearEquiv p M (m ⊗ₜ[ℂ] v) w =
      coefficientDualEquiv p v w • m := by
  simp only [coefficientTensorHomLinearEquiv, LinearEquiv.trans_apply,
    TensorProduct.comm_tmul, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    dualTensorHomEquivOfBasis_apply, dualTensorHom_apply]
  rfl

variable [LieRingModule G M] [LieModule ℂ G M]

/-- The self-duality pairing is invariant under the constant Lie algebra. -/
theorem coefficientDualEquiv_lie_apply (x : G) (v w : Coefficient p) :
    coefficientDualEquiv p ⁅x,v⁆ w = -coefficientDualEquiv p v ⁅x,w⁆ := by
  have h := congrArg (fun f : Module.Dual ℂ (Coefficient p) => f w)
    ((coefficientDualEquiv p).map_lie x v)
  simpa only [LieModuleEquiv.coe_toLieModuleHom, Module.Dual.lie_apply] using h

/-- The tensor-Hom identification intertwines the actual diagonal Lie action. -/
theorem coefficientTensorHomLinearEquiv_lie (x : G) (t : M ⊗[ℂ] Coefficient p) :
    coefficientTensorHomLinearEquiv p M ⁅x,t⁆ =
      ⁅x, coefficientTensorHomLinearEquiv p M t⁆ := by
  induction t using TensorProduct.inductionOn with
  | tmul m v =>
    apply LinearMap.ext
    intro w
    simp only [TensorProduct.LieModule.lie_tmul_right, map_add, LinearMap.add_apply,
      coefficientTensorHomLinearEquiv_tmul_apply, LieHom.lie_apply, lie_smul,
      coefficientDualEquiv_lie_apply, neg_smul, sub_eq_add_neg]
  | add t u ht hu => simp only [lie_add, map_add, ht, hu]

/-- V(2p) self-duality and tensor-Hom adjunction as an actual Lie-module equivalence. -/
def coefficientTensorHomEquiv :
    M ⊗[ℂ] Coefficient p ≃ₗ⁅ℂ,G⁆ (Coefficient p →ₗ[ℂ] M) :=
  { coefficientTensorHomLinearEquiv p M with
    map_lie' := fun {x t} => coefficientTensorHomLinearEquiv_lie p M x t }

@[simp] theorem coefficientTensorHomEquiv_tmul_apply (m : M) (v w : Coefficient p) :
    coefficientTensorHomEquiv p M (m ⊗ₜ[ℂ] v) w = coefficientDualEquiv p v w • m :=
  coefficientTensorHomLinearEquiv_tmul_apply p M m v w

/-- Invariant tensors with coefficient V(2p) are exactly equivariant linear maps
from V(2p). The self-duality used here was proved from irreducible classification. -/
def coefficientTensorInvariantsEquiv :
    LieModule.maxTrivSubmodule ℂ G (M ⊗[ℂ] Coefficient p) ≃ₗ[ℂ]
      (Coefficient p →ₗ⁅ℂ,G⁆ M) :=
  (LieModule.maxTrivEquiv (coefficientTensorHomEquiv p M)).toLinearEquiv.trans
    LieModule.maxTrivLinearMapEquivLieModuleHom

/-- The invariant-tensor equivalence evaluates through the specified self-duality
pairing and the ordinary tensor-Hom map. -/
@[simp] theorem coefficientTensorInvariantsEquiv_apply
    (t : LieModule.maxTrivSubmodule ℂ G (M ⊗[ℂ] Coefficient p)) (v : Coefficient p) :
    coefficientTensorInvariantsEquiv p M t v =
      coefficientTensorHomLinearEquiv p M (t : M ⊗[ℂ] Coefficient p) v := rfl

end KhanSL2.BGG