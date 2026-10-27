module

public import KhanSL2.Factorization.RelativeChainsModel

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The universal CE comparison also intertwines the actual outer constant action. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Factorization.CEModel
open KhanSL2.BGG KhanSL2.BGGBridge KhanSL2.Current

variable {N : Type*} [AddCommGroup N] [Module ℂ N]
  [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]

/-- The constant color action on the universal positive CE model. -/
def constantAction (a : Fin 3) : Module.End ℂ (LieChains.Chains ℂ plus N) :=
  LieChains.lieDeriv (relD a) (LieModule.toEnd ℂ BGG.Current N (constant (MatrixSL2.color a)))

set_option maxHeartbeats 1000000 in
theorem J_constantAction (a : Fin 3) (z : LieChains.Chains ℂ plus N) :
    J (constantAction a z) = actC N (MatrixSL2.color a) (J z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u n =>
    rw [constantAction, LieChains.lieDeriv_tmul, map_add, J_tmul, J_tmul,
      J_tmul, actC, diag_tmul, ColorRoot.positiveAction_color,
      BGGBridge.colorAction_exteriorEquiv]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem actC_add (x y : G) (z : ChainN N) :
    actC N (x + y) z = actC N x z + actC N y z := by
  simp only [actC, diag, map_add, LinearMap.rTensor_add, LinearMap.lTensor_add,
    LinearMap.add_apply]
  abel

theorem actC_smul (c : ℂ) (x : G) (z : ChainN N) :
    actC N (c • x) z = c • actC N x z := by
  simp only [actC, diag, map_smul, LinearMap.rTensor_smul, LinearMap.lTensor_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_add]

/-- Every constant-action relation is a linear combination of the three color actions. -/
theorem actC_sum (x : G) (z : ChainN N) :
    actC N x z = ∑ a : Fin 3, FreeCE.colorBasis.repr x a • actC N (MatrixSL2.color a) z := by
  conv_lhs => rw [← FreeCE.colorBasis.sum_repr x]
  induction (Finset.univ : Finset (Fin 3)) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h := actC_smul (0 : ℂ) 0 z
    rwa [zero_smul, zero_smul] at h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, actC_add, actC_smul, ih,
      FreeCE.colorBasis_apply]

end KhanSL2.Factorization.CEModel

