module

public import KhanSL2.Factorization.ShuffleChains

@[expose] public section

/-! Naturality of the canonical CE shuffle in both coefficient variables. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization.CEShuffle
open KhanSL2.LieChains

variable (L : Type*) [LieRing L] [LieAlgebra ℂ L]
variable {M N M' N' : Type*}
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  [AddCommGroup M'] [Module ℂ M'] [AddCommGroup N'] [Module ℂ N']

private theorem reorder_coeffMap (f : M →ₗ[ℂ] M') (g : N →ₗ[ℂ] N')
    (z : ExteriorShuffle.Tensor L) (t : M ⊗[ℂ] N) :
    reorder L M' N' (z ⊗ₜ[ℂ] TensorProduct.map f g t) =
      TensorProduct.map (LinearMap.lTensor (ExteriorAlgebra ℂ L) f)
        (LinearMap.lTensor (ExteriorAlgebra ℂ L) g)
        (reorder L M N (z ⊗ₜ[ℂ] t)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add t s ht hs => simp only [map_add, TensorProduct.tmul_add, ht, hs]
  | add z w hz hw => simp only [TensorProduct.add_tmul, map_add, hz, hw]

/-- The specified shuffle is natural for all linear maps of its two coefficient spaces. -/
theorem shuffle_coeffMap (f : M →ₗ[ℂ] M') (g : N →ₗ[ℂ] N')
    (z : Chains ℂ L (M ⊗[ℂ] N)) :
    shuffle L M' N' (LinearMap.lTensor (ExteriorAlgebra ℂ L) (TensorProduct.map f g) z) =
      TensorProduct.map (LinearMap.lTensor (ExteriorAlgebra ℂ L) f)
        (LinearMap.lTensor (ExteriorAlgebra ℂ L) g) (shuffle L M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u t =>
    rw [LinearMap.lTensor_tmul, shuffle_tmul, shuffle_tmul]
    exact reorder_coeffMap L f g (ExteriorShuffle.shuffle L u) t
  | add z w hz hw => simp only [map_add, hz, hw]

end KhanSL2.Factorization.CEShuffle
