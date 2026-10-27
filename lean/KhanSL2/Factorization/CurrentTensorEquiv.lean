module

public import KhanSL2.Factorization.ShuffleEquivalences

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Specified tensor equivalences retain the actual diagonal current action. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG
variable {M N P Q : Type}
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup P] [Module ℂ P] [LieRingModule Current P] [LieModule ℂ Current P]
  [AddCommGroup Q] [Module ℂ Q] [LieRingModule Current Q] [LieModule ℂ Current Q]

/-- Tensor two specified genuine current equivalences. -/
def tensorCurrentEquiv (e : M ≃ₗ⁅ℂ,Current⁆ N) (f : P ≃ₗ⁅ℂ,Current⁆ Q) :
    M ⊗[ℂ] P ≃ₗ⁅ℂ,Current⁆ N ⊗[ℂ] Q where
  __ := TensorProduct.congr e.toLinearEquiv f.toLinearEquiv
  map_lie' {x m} := by
    change TensorProduct.map e.toLinearMap f.toLinearMap ⁅x,m⁆ =
      ⁅x,TensorProduct.map e.toLinearMap f.toLinearMap m⁆
    exact (TensorProduct.LieModule.map e.toLieModuleHom f.toLieModuleHom).map_lie x m

end KhanSL2.Factorization
