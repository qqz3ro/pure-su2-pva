module

public import KhanSL2.Factorization.ShuffleChains

@[expose] public section

/-! Equivariance of the canonical shuffle for arbitrary exterior/coefficient
endomorphisms, including the outer constant sl2 action on positive CE chains. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization.CEShuffle
open KhanSL2.LieChains

variable (L M N : Type*) [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- The even diagonal coefficient operator. -/
def coefficientAction (S : Module.End ℂ M) (T : Module.End ℂ N) :
    Module.End ℂ (M ⊗[ℂ] N) := LinearMap.rTensor N S + LinearMap.lTensor M T

@[simp] theorem coefficientAction_tmul (S : Module.End ℂ M) (T : Module.End ℂ N)
    (m : M) (n : N) : coefficientAction M N S T (m ⊗ₜ[ℂ] n) =
      S m ⊗ₜ[ℂ] n + m ⊗ₜ[ℂ] T n := rfl

/-- The corresponding diagonal operator on the two full chain factors. -/
def tensorAction (D : Module.End ℂ L) (S : Module.End ℂ M) (T : Module.End ℂ N) :
    Module.End ℂ (CETensor.TensorChains L M N) :=
  LinearMap.rTensor (Chains ℂ L N) (lieDeriv D S) +
    LinearMap.lTensor (Chains ℂ L M) (lieDeriv D T)

@[simp] theorem tensorAction_tmul (D : Module.End ℂ L) (S : Module.End ℂ M)
    (T : Module.End ℂ N) (u : Chains ℂ L M) (v : Chains ℂ L N) :
    tensorAction L M N D S T (u ⊗ₜ[ℂ] v) =
      lieDeriv D S u ⊗ₜ[ℂ] v + u ⊗ₜ[ℂ] lieDeriv D T v := rfl

private theorem reorder_deriv (D : Module.End ℂ L) (S : Module.End ℂ M)
    (T : Module.End ℂ N) (z : ExteriorShuffle.Tensor L) (t : M ⊗[ℂ] N) :
    reorder L M N (ExteriorShuffle.tensorDeriv D z ⊗ₜ[ℂ] t +
      z ⊗ₜ[ℂ] coefficientAction M N S T t) =
        tensorAction L M N D S T (reorder L M N (z ⊗ₜ[ℂ] t)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
      simp only [ExteriorShuffle.tensorDeriv_tmul, TensorProduct.add_tmul,
        coefficientAction_tmul, TensorProduct.tmul_add, map_add,
        reorder_tmul, tensorAction_tmul, lieDeriv_tmul]
      abel
    | add t s ht hs =>
      simp only [TensorProduct.tmul_add, map_add] at ht hs ⊢
      rw [← ht, ← hs]
      abel
  | add z w hz hw =>
    simp only [map_add, TensorProduct.add_tmul] at hz hw ⊢
    rw [← hz, ← hw]
    abel

/-- Simultaneous exterior/coefficient derivations commute with the actual shuffle. -/
theorem shuffle_lieDeriv (D : Module.End ℂ L) (S : Module.End ℂ M)
    (T : Module.End ℂ N) (z : Chains ℂ L (M ⊗[ℂ] N)) :
    shuffle L M N (lieDeriv D (coefficientAction M N S T) z) =
      tensorAction L M N D S T (shuffle L M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u t =>
    rw [lieDeriv_tmul, map_add, shuffle_tmul, shuffle_tmul, shuffle_tmul,
      ExteriorShuffle.shuffle_derivExt]
    simpa only [map_add] using reorder_deriv L M N D S T (ExteriorShuffle.shuffle L u) t
  | add z w hz hw => simp only [map_add, hz, hw]

end KhanSL2.Factorization.CEShuffle
